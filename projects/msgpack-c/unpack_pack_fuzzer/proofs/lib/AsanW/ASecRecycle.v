(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes AKitQ AModelFacts ARep ALayout AHeapP ARepKit ARepFrame ASec ASecFacts APoisonR_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_rsrvshadow AFrameD ARepFrameD F_asecdealloc F_arecsec ASecRecycle_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AExh AC6U AC6Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module ASecRecycle.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
Lemma u64arr_app_inv' : forall m A ws1 ws2, u64arr asegs m A (ws1 ++ ws2) ->
  u64arr asegs m A ws1 /\ u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [HB HW]. rewrite u64s_app in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite u64s_length in HB2. replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) in HB2 by lia.
  rewrite length_app in HW. destruct HW as (H0 & H1 & HW).
  split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + 8 * Z.of_nat (length ws1) + i) with (A + (8 * Z.of_nat (length ws1) + i)) by lia. apply HW. lia.
Qed.

Lemma junk_of_u64arr' : forall m A ws, u64arr asegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [| exact I]. rewrite u64s_length. lia.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)))) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma map_upd : forall {A B} (f : A -> B) (l : list A) i x, map f (upd l i x) = upd (map f l) i (f x).
Proof. intros A B f l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma upd_app_mid : forall {A} (l1 l2 : list A) (a x : A), upd (l1 ++ a :: l2) (length l1) x = l1 ++ x :: l2.
Proof. intros A l1. induction l1 as [|y l1 IH]; intros l2 a x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_snoc : forall {A} (l : list A) (a : A), firstn (length l) (l ++ [a]) = l.
Proof. intros A l a. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma nth_error_last_split : forall {A} (l : list A) n x,
  length l = S n -> nth_error l n = Some x -> l = removelast l ++ [x] /\ length (removelast l) = n.
Proof.
  intros A l n x HL HN.
  assert (NE : l <> []) by (intros ->; discriminate).
  pose proof (app_removelast_last x NE) as E.
  assert (LR : length (removelast l) = n) by (rewrite E, length_app in HL; cbn in HL; lia).
  split; [| exact LR].
  assert (HN' : nth_error (removelast l ++ [last l x]) n = Some x) by (rewrite <- E; exact HN).
  rewrite nth_error_app2 in HN' by lia. rewrite LR, Nat.sub_diag in HN'. cbn in HN'. injection HN' as HN'.
  transitivity (removelast l ++ [last l x]); [exact E| rewrite HN'; reflexivity].
Qed.

Lemma disjoint_from_Forall : forall W A k, disjoint_from W A k <-> Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W.
Proof.
  intros W A k. induction W as [|[lo hi] W IH]; cbn.
  - split; [intros _; constructor| intros _; exact I].
  - split.
    + intros [H1 H2]. constructor; [cbn; exact H1| apply IH; exact H2].
    + intros HF. inversion HF; subst. split; [assumption| apply IH; assumption].
Qed.

Lemma sec_wf1_facts : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n
  /\ 64512 < n <= AREQMAX /\ rz_size n = 2048 /\ 73728 <= ms <= 4293926912 /\ ms mod 4096 = 0
  /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n /\ sec_clear L mb ms.
Proof.
  intros L mb ms n W. cbn [sec_wf1] in W. destruct W as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  repeat (split; [first [assumption | lia]|]). exact G7.
Qed.

Lemma bases_dominated : forall L cs mb ms n,
  Forall (sec_wf1 L) cs -> sec_disjoint cs -> In (CSec mb ms n) cs ->
  Forall (fun b => 0 <= b < 2^64 /\ (b <= mb + 6128 -> b <= mb)) (map sec_mb cs).
Proof.
  intros L cs mb ms n WF [ND D] IN. rewrite Forall_map. rewrite Forall_forall in WF |- *. intros ch Hch.
  pose proof (WF ch Hch) as W1. pose proof (WF _ IN) as W0.
  destruct ch as [c k|mb' ms' n']; [destruct W1|]. cbn [sec_mb].
  destruct (sec_wf1_facts _ _ _ _ W1) as (_ & A2 & A3 & _ & _ & _ & A7 & _).
  destruct (sec_wf1_facts _ _ _ _ W0) as (_ & B2 & B3 & _ & _ & _ & B7 & _).
  pose proof (ablk_lin _ _ A2) as (A2a & A2b & A2c & A2d). pose proof (ablk_lin _ _ B2) as (B2a & B2b & B2c & B2d).
  unfold K_HIGH_MEM in *. split; [lia|]. intros LE.
  assert (DEC : {CSec mb' ms' n' = CSec mb ms n} + {CSec mb' ms' n' <> CSec mb ms n}) by (repeat (decide equality)).
  destruct DEC as [E|NE]; [injection E as -> -> ->; lia|].
  destruct (D _ _ Hch IN NE) as [X|X]; cbn [sec_mb sec_ms] in X; lia.
Qed.

Lemma rw_cells_hd' : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [H _]. exact H. Qed.
Lemma rw_cells_tl' : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.
Lemma rw_cells_cons' : forall m A c cs,
  rw_cells asegs m A [c] -> rw_cells asegs m (A + Z.of_nat (csize c)) cs -> rw_cells asegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app asegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma mtx4_join : forall m, rw_cells asegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xd6701 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xd6700 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H1 H2. apply rw_cells_cons'; [exact H1| exact H2]. Qed.
Lemma mtx4_split : forall m, rw_cells asegs m 0xd6700 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0xd6701 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. split; [eapply rw_cells_hd'; exact H| apply rw_cells_tl' in H; exact H]. Qed.

Lemma sec_shadow_cb : forall m mb ms n lv, asec_chunk m (CSec mb ms n) 0 lv \/ (exists idx, asec_chunk m (CSec mb ms n) idx lv) ->
  mb mod 4096 = 0 -> 64512 < n <= AREQMAX -> ms = sec_map_size n -> is_primary n = false ->
  exists shj, rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj].
Proof.
  intros m mb ms n lv CH MAL NB MSE NPR.
  assert (CH' : exists idx, asec_chunk m (CSec mb ms n) idx lv) by (destruct CH as [CH|CH]; [exists 0; exact CH| exact CH]).
  clear CH. destruct CH' as [idx CH].
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- MSE in MSR, MSM, MSB.
  cbn [asec_chunk] in CH. destruct CH as (_ & _ & _ & _ & _ & _ & S1 & S2 & S3). unfold SEC_UOFF in *.
  assert (GR : 0 <= granules n /\ shad (mb + 6144) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules. rewrite !shad_div, shlen_div. clear -MAL NB RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3). rewrite GR2 in S2, S3.
  apply cb_of_fill in S1. apply cb_of_fill in S3.
  pose proof (cb_app m (shad mb) _ _ _ _ S1 ltac:(rewrite Z2Nat.id by lia; exact S2)) as S12.
  replace (shad mb + 768 + granules n) with (shad mb + Z.of_nat (Z.to_nat 768 + Z.to_nat (granules n))) in S3 by (clear -GR1; lia).
  pose proof (cb_app m (shad mb) _ _ _ _ S12 S3) as S123.
  eexists. replace (Z.to_nat (shlen ms)) with (Z.to_nat 768 + Z.to_nat (granules n) + Z.to_nat (ms / 8 - 768 - granules n))%nat; [exact S123|].
  rewrite shlen_div. clear -GR1 GR3. lia.
Qed.

Lemma premap_of_rt : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  unfold premap_cells. split; [eapply rw_cells_hd'; exact R11|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.

Lemma poison_cells_of_rt : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma asec_chunk_frameD : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

Lemma cb_zeros_at : forall m A n j, rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  AIMG_HI <= A -> 0 <= j < n -> m (wa (A + j)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n j [[_ B] _] HA Hj. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  rewrite repeat_length in B1, B. specialize (B (Z.to_nat j) ltac:(lia)). rewrite (@nth_error_repeat _ (Z_to_bv 8 0) (Z.to_nat n) (Z.to_nat j) ltac:(clear -Hj; lia)) in B.
  replace (A + Z.of_nat (Z.to_nat j)) with (A + j) in B by lia.
  unfold mrd in B. destruct (m (wa (A + j))) as [b|] eqn:E; [congruence|].
  exfalso. rewrite ref_seg_rom_none in B; [discriminate|]. rewrite wa_unsigned by lia. unfold AIMG_HI in HA. lia.
Qed.

Lemma fstepS_munmap_after_le : forall a l rsp rsp' R R1 R',
  fp_le R R1 -> fstepS (NMunmap a l) rsp R1 R' -> fstepS (NMunmap a l) rsp' R R'.
Proof.
  intros a l rsp rsp' R R1 R' LE [HA HS]. cbn [fstepA fstepS] in HA, HS |- *. split.
  - intros b j Hb Hd. apply HA; [apply LE; exact Hb| exact Hd].
  - eapply fp_le_trans; [exact LE| exact HS].
Qed.

Theorem srec : srec_stmt ASECc RSEC.
Proof.
  unfold srec_stmt.
  intros AQ AD AF cs1 cs2 R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m st X mb ms n CBA lo SHO ALO ARNG RS AR MI ST CEIL LO SPHI TP -> -> RA RSTK KONT.
  set (ch := CSec mb ms n) in *. set (cs := cs1 ++ ch :: cs2) in *.
  assert (IN : In ch cs) by (subst cs; apply in_elt).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.

  pose proof AR as AR0.
  destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot ah_fake AHS] in HQ, HS, HD.
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT RT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & TK & _ & _ & _ & _ & _ & _ & _ & _ & _ & T88 & TSD & _ & _ & CT).
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  pose proof THR as THR0. destruct THR0 as (Tc0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof HS as HS0. destruct HS0 as (WFS & SARR & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct SARR as (order & PO & U64 & JK & PER).
  pose proof (Permutation_length PO) as LENO.
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch IN) as WFch.
  destruct (sec_wf1_facts L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL).
  pose proof NB as NB0. destruct WFch as (_ & _ & _ & _ & _ & NPR & _).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & _).

  destruct (PER i ch NTH) as (lv & _ & CH). pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & H2 & H3 & H4 & (b1 & cx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in H5. replace (mb + 6144 - 16) with (mb + 6128) in H5 by lia.
  destruct (sec_shadow_cb m mb ms n lv (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].

  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- WL, <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- WL, <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. all: split; [clear -LCE LMSB; lia|].     all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: clear -LC_p LMSB WR WB; lia. }

  eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (CBA := CBA) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 (if lv then 2 else 3)) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PRM
       | |- arelro0 _ => exact HRO
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; unfold PG; clear -RZ; lia]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680| exact PAD]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => first [eassumption | exact I32 | exact I64 | exact I72 | exact I112 | exact ISRT | exact TI | exact TK | exact T88 | exact TSD | exact H1]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- WL, <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map, LENO; exact WL
       | |- _ -> _ /\ _ => exact LHDR
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact (proj1 ARNG)
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ (shad _) _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [_ RH]; cbn [sec_mb sec_ms] in RH; rewrite shlen_div; exact RH
       | |- rng _ (al_ptr_array _) _ => destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RP & _); exact RP
       | |- rng _ (al_t _) _ => destruct ARNG as (_ & RT1 & _); exact RT1
       | |- rng _ (al_ctx _) _ => destruct ARNG as (_ & _ & RC & _); eapply rng_sub'; [exact RC|]; clear; lia
       | |- rng _ _ _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [RH _]; cbn [sec_mb sec_ms] in RH; exact RH
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in CEIL, LO, SPHI, OT, OC, OP, MLO, MCE, NB |- *.
  all: pose proof (alayout_ctx L ALO) as (_ & _ & CXI' & _); pose proof (alayout_t L ALO) as (_ & _ & _ & TIC').
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- iclr _ _ => exact TIC' | |- AIMG_HI <= al_ctx _ => exact CXI' | |- a_nres _ <= 1048576 => clear -WR; lia
       | |- sclr (al_ctx _) _ => exact (proj1 (alayout_ctx L ALO)) | |- sclr (al_t _) _ => exact (proj1 (alayout_t L ALO))
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- _ => try first [ assumption | exact SC_t
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -OC; lia | clear -OT; lia | clear -OP WR WB; lia | clear -IL LENO WL; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia ]
       end.

  intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  apply KONT. unfold srec_ret.
  destruct PP as (MU & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold sdealloc_W in MU.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- WL, <- LENO; clear -IL; lia).
  exists u0, u1, u2, b0, b1', b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (lmb + 24).
  split; [reflexivity|]. split; [reflexivity|].
  split.
  {   unfold srec_hl_ok, sec_clear, K_HIGH_MEM in *. destruct LSCL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. split; [clear -LCE LMSB; lia|].
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [clear -Q1 LMSB; lia | clear -Q2 LMSB; lia | clear -Q3 LMSB; lia | clear -Q4 LMSB; lia
            | clear -Q5 LMSB; lia | clear -Q6 LMSB; lia | clear -Q7 LMSB; lia | clear -Q8 LMSB; lia]. }
  split.
  {   replace (lmb + 24 - 24) with lmb by (clear; lia).
    destruct (Z.eq_dec lmb mb) as [E|NE].
    - left. rewrite E. clear -MSB. lia.
    - right. exists lms, ln. split; [| exact WFl].
      assert (INc : In (CSec lmb lms ln) cs) by (eapply Permutation_in; [exact PO| exact INl]).
      subst cs. apply in_app_iff in INc. apply in_app_iff. destruct INc as [H1'|[H1'|H1']]; [left; exact H1'| exfalso; apply NE; unfold ch in H1'; congruence| right; exact H1']. }
  split.
  {   eapply munch_weaken; [| exact MU]. unfold srec_W, AINSTANCE.
    let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *. clear -Hq I64b WB LO. lia. }
  split; [exact MI'|]. split; [exact ST'|].
  split.
  2: { split; [eapply fstepS_munmap_after_le; [exact LE1| exact HF]|].
       split.
       - eapply arng_mono; [exact LE|]. eapply arng_st; [| | | exact ARNG]; [intros c Hc; reflexivity| reflexivity|].
         rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st)) by reflexivity. apply Permutation_refl.
       - eapply RSEC_mono; [exact LE|]. unfold RSEC in RS |- *. subst cs. rewrite Forall_app in RS |- *.
         destruct RS as [RS1 RS2]. split; [exact RS1| exact (Forall_inv_tail RS2)]. }

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ MLO) as [kA MBND]. pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & _ & _). unfold AIMG_HI in ML1.
  destruct (ablk_int _ _ LLO) as [kL LBND]. pose proof (ablk_lin _ _ LLO) as (LL1 & _ & _ & _). unfold AIMG_HI in LL1.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s.
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  unfold adisj in D_t_r, D_p_r, D_t_n, D_t_s, D_n_p, D_s_p, D_t_f, D_f_p, D_t_d, D_d_p.
  pose proof LSCL as (_ & _ & LC_r & _ & LC_n & LC_st & LC_f & LC_d).
  pose proof SCL as (_ & _ & SC_r & _ & _ & _ & _ & _).
  assert (SHR : 0x800bde00 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MBND ML1 MCE MSB; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_r as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 0x10007fef8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  destruct RSH as (SR1 & SR2 & SR3).
  assert (FSH : 0x800bde00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 0x10007fef8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK OFKi OFKs. Z.div_mod_to_equations. lia. }
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, LCE, LLO.

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall A kk, 65536 <= A -> 0 <= kk -> (A + kk <= 0xd64d0 \/ (0xd6728 <= A /\ A + kk <= AIMG_HI)) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_t : forall A kk, al_t L <= A -> 0 <= kk -> (A + kk <= al_t L + 2800 \/ (al_t L + 3168 <= A /\ A + kk <= al_t L + 4096)) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OT D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB OTs OTi. lia. }
  assert (K_ctx : forall A kk, al_ctx L <= A -> 0 <= kk -> A + kk <= al_ctx L + 65536 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OC D_t_c D_c_p LC_c SC_c SHR I64b WR WB MSB LMSB OT OTs OTi OCs OCi. lia. }
  assert (K_res : forall A kk, al_res L <= A -> 0 <= kk -> A + kk <= al_res L + 137439023104 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO ORS D_t_r D_p_r LC_r SC_r SHR I64b WR WB MSB LMSB OT OTs OTi RHI. lia. }
  assert (K_shres : forall A kk, shad (al_res L) <= A -> 0 <= kk -> A + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO SR1 SR2 SR3 SHSEP SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'. pose proof (alayout_space L ALO) as RSPs.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  split; [exact WF|].
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact Tc0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           eapply cells_frameD; [exact UNW| exact MU| apply K_t; clear; cbn; lia]. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  assert (K_nodes : disjoint_from Wd (al_nodes L) 1048576).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO ON D_t_n D_n_p LC_n SC_n SHR I64b WR WB OT LMSB MSB OTs OTi ONs ONi. lia. }
  assert (K_store : disjoint_from Wd (al_store L) 8388608).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OS D_t_s D_s_p LC_st SC_st SHR I64b WR WB OT LMSB MSB OTs OTi OSs OSi. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OFK D_t_f D_f_p LC_f SC_f SHR I64b WR WB OT LMSB MSB OTs OTi OFKs OFKi. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OD D_t_d D_d_p LC_d SC_d SHR I64b WR WB OT LMSB MSB OTs OTi ODs ODi. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO FSH SHSEPF SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }

  split.
  { eapply (sho_quar _ _ SHO L st _ X X m m' Wd); [exact HQ | exact MU | |].
    - unfold quar_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L) 208 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img (AINSTANCE + 728) 256 ltac:(clear; unfold AINSTANCE; lia) ltac:(clear; lia) ltac:(clear; unfold AINSTANCE, AIMG_HI; lia))) as F2.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xdacc0 0x81030 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F3.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x169548 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
      rewrite Forall_forall in F1, F2, F3, F4. specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). cbn [fst snd] in F1, F2, F3, F4.
      split; [clear -F1; lia|]. split; [clear -F2; lia|]. split; [clear -F3; lia|]. split; [clear -F4; lia|].
      intros b Hb. destruct (BB b Hb) as [B1' B2']. pose proof (size_of_class_facts (xb_class b) (proj1 (BUSY b Hb))) as [QSb _].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_res (xb_alloc L b) (size_of_class (xb_class b)) B1' ltac:(clear -QSb; lia) B2')) as F5.
      rewrite Forall_forall in F5. specialize (F5 _ Hin). cbn [fst snd] in F5. destruct (xb_st b); [exact I| clear -F5; lia| clear -F5; lia].
    - unfold quar_same. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes a_space_beg set_nsec].
      repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }

  split.
  2: {   split.
       { eapply (sho_depot _ _ SHO L m m' Wd); [exact HD | exact MU |].
         pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1ab988 (0x5fb9d0 - 0x1ab988) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F1.
         pose proof (proj1 (disjoint_from_Forall _ _ _) K_nodes) as F2. pose proof (proj1 (disjoint_from_Forall _ _ _) K_store) as F3.
         apply Forall_forall. intros [qlo qhi] Hin a Ha. rewrite Forall_forall in F1, F2, F3.
         specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). cbn [fst snd] in F1, F2, F3, Ha. clear -F1 F2 F3 Ha. lia. }

       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact RT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  assert (K_hi : forall A kk, (A + kk <= 65536 \/ 6483968 <= A) -> (A + kk <= 2147446784 \/ 17594333495296 <= A) -> 0 <= kk -> A + kk <= ATOP ->
            (A + kk <= mb \/ mb + ms <= A) -> (A + kk <= lmb + 24 \/ lmb + 32 <= A) ->
            (A + kk <= al_t L \/ al_t L + 4096 <= A) -> (A + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
            disjoint_from Wd A kk).
  { intros A kk Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7. subst Wd. cbn [disjoint_from]. clear -Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 CEIL LO SHR I64b WR WB. lia. }
  assert (K_sh : forall A kk, 2147446784 <= A -> 0 <= kk -> A + kk <= 17594333495296 ->
            (A + kk <= shad mb \/ shad mb + shlen ms <= A) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 CEIL LO OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_pa : forall A kk, al_ptr_array L + 8 * a_nsec st <= A -> 0 <= kk -> A + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OP D_t_p LC_p SC_p SHR I64b WR WB MSB LMSB OT OTs OTi OPs OPi. lia. }

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall A kk, mb' + 32 <= A -> 0 < kk -> A + kk <= mb' + ms' -> disjoint_from Wd A kk)
          /\ (forall A kk, shad mb' <= A -> 0 < kk -> A + kk <= shad mb' + ms' / 8 -> disjoint_from Wd A kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL).
    destruct JSCL as (JC_t & _ & _ & JC_p & _). unfold K_HIGH_MEM in JLO, JCE.
    destruct (ablk_int _ _ JLO) as [kJ JB]. pose proof (ablk_lin _ _ JLO) as (JL1 & _ & _ & _). unfold AIMG_HI in JL1.
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 0x800bde00 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -JB JL1 JCE JMSB; Z.div_mod_to_equations; lia).

    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [clear -Dc; lia|].
    all: split; [intros A kk Z1 Z2 Z3; apply K_hi; [clear -Z1 JL1; lia| clear -Z1 Z3 JB; lia| clear -Z2; lia| clear -Z3 JCE; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros A kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -JL1; lia| clear -JB JMSB; lia| clear; lia| clear -JCE JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (rewrite LENO; symmetry; exact WL).
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall c, sec_live (set_nsec (a_nsec st - 1) st) c <-> sec_live st c) by (intros c; unfold sec_live; cbn [a_live set_nsec]; apply iff_refl).
  assert (WFA : asec_wf L (set_nsec (a_nsec st - 1) st) (cs1 ++ cs2)).
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    subst cs. rewrite length_app in WL |- *. cbn [length] in WL.
    split; [clear -WL; lia|]. split; [clear -WL WB; lia|].
    split; [apply Forall_app in WF1 as [F1 F2]; apply Forall_app; split; [exact F1| exact (Forall_inv_tail F2)]|].
    destruct WD as [ND DJ]. split; [exact (NoDup_remove_1 _ _ _ ND)|].
    intros ci cj Hi Hj NE.
    apply DJ; [| | exact NE];
      [apply in_app_iff in Hi; apply in_app_iff; destruct Hi as [Hi|Hi]; [left; exact Hi| right; right; exact Hi]
      |apply in_app_iff in Hj; apply in_app_iff; destruct Hj as [Hj|Hj]; [left; exact Hj| right; right; exact Hj]]. }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; lia]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L (cs1 ++ cs2) m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
    assert (SX : 0x800bde00 <= shad x < 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, KLS, AIMG_HI; exact Hx) HFh).
    2,4: subst cs; apply Forall_app in HC as [HC1 HC2]; apply Forall_app; split; [exact HC1| constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC2]].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia. }

  assert (AXH' : AEXHc (cs1 ++ cs2) L (set_nsec (a_nsec st - 1) st) m').
  { eapply (AEXHc_sub cs); [subst cs; intros c0 Hc0; apply in_app_iff in Hc0; apply in_app_iff; destruct Hc0 as [H0|H0]; [left; exact H0| right; right; exact H0]|].
    eapply (aexhc_frameK cs L st _ m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) cs) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.c6_std. left. clear -CEIL LO. lia.
    - left. unfold AC6U.c6_std. right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.c6_std. do 4 right; left. clear -SHR. lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_app_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO. exact PO. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_app_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; exact PO].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite LVE; exact LVl|].
      destruct (CHK _ lmb lms ln NTHL ltac:(clear -NE; lia)) as (Wj & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End CANSEC1.
End ASecRecycle.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AQConst AMalloc_iface ADepot_iface ARepQ ARepQP AKit AKit2 AFreeModel AFreeRep AFreeGeo.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc_s.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_iseg F_afree_front F_afree_icpt F_apoisonz F_aputrec AHolesD.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_kit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_arep.
Module ASF_big.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoisonz. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aputrec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHolesD. Import ASecRecycle.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x16954c); (t + 2800, t + 3169);
   (0x1ab988, 0x5fb9d0); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xd64d0, 0xd64d9); (0xd64e8, 0xd64f8); (0xd6700, 0xd6704); (0xd6718, 0xd6728);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; lia.

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd6730 \/ 0xd67f0 <= fst iv)
                                  /\ (snd iv <= 0xdacc0 \/ 0x15bcf0 <= fst iv)
                                  /\ (snd iv <= 0x169548 \/ 0x16954c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem afree_sec_big : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),

  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].

  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (Ni & Na & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (Si & Sa & [kS SBND]).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & OPa & [kP OPs]).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (Ci & Ca & [kC CBND]). pose proof (aobj4_int _ (ao_t L ALO)) as (Ti4 & Ta4 & [kT TBND] & [jT TIMG]).
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).

  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.

  pose proof HS as HS0. destruct HS0 as (WFS & _ & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).

  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts' L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL & _).
  pose proof (ablk_int _ _ LLO) as (kLl & KALl & KBLl & KELl & KCLl & KDLl).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & LC_n & LC_st & LC_f & LC_d).
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].     all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia| clear -LC_st LMSB; lia]. }

  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.

  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).

  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_spec DI L (q_ia Q) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo (al_top L) (al_bot L) uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).
  apply evtF_done.

  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148261376 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).

  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { intros NE. destruct (LHDR NE) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). atop_facts.
    pose proof (ablk_int _ _ L2) as (kL & KAL & KBL & KEL & KCL & KDL).
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). exact L7. }
  clear LHDR.

  name_sp sp (-2128).
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp0 gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (_ - _) => rewrite Hsp; eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: try rewrite Hsp.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.

  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  destruct PP as (MU2 & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold putrec_W in MU2.
  unname_sp.

  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply (cells_frameD _ m1 m') in SS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in TB1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FRS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  replace (ret_pc (Z_to_bv 64 386508)) with (Z_to_bv 64 386508) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  eapply evtF_mono.
  { eapply (ficptD_spec RNG' sp gp tp); [exact ST' | atop_facts; clear -BOT STK3; lia | clear -LO; lia | exact MI'
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia); exact TB1 | reflexivity]
      | exact FRS1 | eapply rng_fp_le; [exact LE| exact RIMG] | eapply rng_fp_le; [exact LE| exact RSTK] ]. }
  cbv beta. intros ms3 [-> ST3].

  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST3|].

  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  pose proof LSCL as (_ & _ & LC_r & _).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  destruct RSH3 as (SR1 & SR2 & SR3).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFi & OFa & [kF FBND]).
  assert (FSH : 2148261376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->
            (Ad + kk <= 0xd64d0 \/ (0xd6728 <= Ad /\ Ad + kk <= 0xdacc0) \/ (0x15bcf0 <= Ad /\ Ad + kk <= 0x169548)
             \/ (0x16954c <= Ad /\ Ad + kk <= 0x1ab988) \/ (0x5fb9d0 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6483968 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. pose proof (aobj4_int _ (ao_dtls L ALO)) as (ODi & ODa & [kD DBND] & [jD DIMG]). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).

  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - destruct BLK as (b & Hb & R). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: destruct (sec_wf1_facts' L mb' ms' n' G') as (_ & JLO & JCE & _ & JNB & _ & JMSB & _ & JNMS & _ & (JC_t & _ & _ & JC_p & JC_n & JC_st & _) & _ & JN6).
            all: pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + destruct (proj1 (proj2 BL) cls A' n' Hb) as (F1 & F2 & F3). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - destruct SHD as (a' & Ha' & ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].
        + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + destruct FK as (cls & FA & sz & Hin & R). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          destruct (proj1 (proj2 BL) cls FA sz Hin) as (F1 & F2 & F3).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }

  split; [exact ALO|].
  split.
  {   eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: {
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| apply K_t; clear; lia | |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xd3358 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cc78 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F5.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cc88 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F6.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cca8 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16b671 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x169558 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F5; lia| clear -F6; lia| clear -F7; lia| clear -F8; lia| clear -F9; lia].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }

  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }

  split.
  2: {
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts' L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL & _).
    destruct JSCL as (JC_t & _ & _ & JC_p & JC_n & JC_st & _). unfold K_HIGH_MEM in JLO, JCE.
    pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148261376 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.
    assert (SX : 2148261376 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].

  assert (AXH' : AEXHc cs' L st' m').
  { eapply (AEXHc_sub (sec_chunks_of st)); [intros c0 Hc0; eapply Permutation_in; [exact PD| right; exact Hc0]|].
    eapply (aexhc_frameK (sec_chunks_of st) L st st' m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.c6_std. left. clear -LO BOT. unfold AFREE_STACK in *. lia.
    - left. unfold AC6U.c6_std. do 6 right; left. clear. lia.
    - do 4 right. unfold AC6U.c6_imgp, AIMG_HI. clear. lia.
    - left. unfold AC6U.c6_std. right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 7 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 8 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 9 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.c6_std. do 4 right; left. clear -SHR. lia. }
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      destruct (CHK _ lmb lms ln NTHL NEli) as (Wj & _ & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End S.
End CANSEC2.

End ASF_big.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_adealloc_front ADeallocLib.
Module ADeallocSF_big.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoisonz. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aputrec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHolesD. Import ASecRecycle.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_arep.
Import ASF_big. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocLib.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1b. Context {rc : runConstT} {ov : annOV}.

Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

End CANSEC1b.
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; lia.

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC3. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd6730 \/ 0xd67f0 <= fst iv)
                                  /\ (snd iv <= 0xdacc0 \/ 0x15bcf0 <= fst iv)
                                  /\ (snd iv <= 0x169548 \/ 0x16954c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem adealloc_sec_big : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),

  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 ZSS ZTB2 ZLTB2 ZLTRT ZTRF TRU ZSPS ZSTOP ZRS ZFLAG RA4 RSTK.
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].

  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (Ni & Na & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (Si & Sa & [kS SBND]).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & OPa & [kP OPs]).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (Ci & Ca & [kC CBND]). pose proof (aobj4_int _ (ao_t L ALO)) as (Ti4 & Ta4 & [kT TBND] & [jT TIMG]).
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -ZSPS ZSTOP; lia).

  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  assert (QIA : q_ia Q = true) by (eapply flag_ia_true; [exact FL| exact ZFLAG]). rewrite QIA in FL. specialize (IAM QIA).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.

  pose proof HS as HS0. destruct HS0 as (WFS & _ & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).

  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts' L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL & _).
  pose proof (ablk_int _ _ LLO) as (kLl & KALl & KBLl & KELl & KCLl & KDLl).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & LC_n & LC_st & LC_f & LC_d).
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].     all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia| clear -LC_st LMSB; lia]. }

  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.

  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).

  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo SO pc uw (Z_to_bv 64 (al_top L)) (Z_to_bv 64 (al_bot L)) sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact ZTB2
         | |- map _ _ = _ => exact ZTRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (al_t L + 3168, al_t L + 3169); (mb + 6128, mb + 6128 + 4); (mb + 6128 + 16, mb + 6128 + 24); (al_t L + 2800, al_t L + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }
  apply evtF_done.

  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148261376 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).

  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { intros NE. destruct (LHDR NE) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). atop_facts.
    pose proof (ablk_int _ _ L2) as (kL & KAL & KBL & KEL & KCL & KDL).
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). exact L7. }
  clear LHDR.

  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (_ - _) => eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.

  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  destruct PP as (MU2 & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold putrec_W in MU2.

  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.

  apply evtF_done. unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].

  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  pose proof LSCL as (_ & _ & LC_r & _).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  destruct RSH3 as (SR1 & SR2 & SR3).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFi & OFa & [kF FBND]).
  assert (FSH : 2148261376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->
            (Ad + kk <= 0xd64d0 \/ (0xd6728 <= Ad /\ Ad + kk <= 0xdacc0) \/ (0x15bcf0 <= Ad /\ Ad + kk <= 0x169548)
             \/ (0x16954c <= Ad /\ Ad + kk <= 0x1ab988) \/ (0x5fb9d0 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6483968 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. pose proof (aobj4_int _ (ao_dtls L ALO)) as (ODi & ODa & [kD DBND] & [jD DIMG]). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).

  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - destruct BLK as (b & Hb & R). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: destruct (sec_wf1_facts' L mb' ms' n' G') as (_ & JLO & JCE & _ & JNB & _ & JMSB & _ & JNMS & _ & (JC_t & _ & _ & JC_p & JC_n & JC_st & _) & _ & JN6).
            all: pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + destruct (proj1 (proj2 BL) cls A' n' Hb) as (F1 & F2 & F3). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - destruct SHD as (a' & Ha' & ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].
        + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + destruct FK as (cls & FA & sz & Hin & R). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          destruct (proj1 (proj2 BL) cls FA sz Hin) as (F1 & F2 & F3).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }

  split; [exact ALO|].
  split.
  {   eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: {
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| apply K_t; clear; lia | |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xd3358 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cc78 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F5.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cc88 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F6.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60cca8 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16b671 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x169558 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F5; lia| clear -F6; lia| clear -F7; lia| clear -F8; lia| clear -F9; lia].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }

  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }

  split.
  2: {
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts' L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL & _).
    destruct JSCL as (JC_t & _ & _ & JC_p & JC_n & JC_st & _). unfold K_HIGH_MEM in JLO, JCE.
    pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148261376 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.
    assert (SX : 2148261376 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].

  assert (AXH' : AEXHc cs' L st' m').
  { eapply (AEXHc_sub (sec_chunks_of st)); [intros c0 Hc0; eapply Permutation_in; [exact PD| right; exact Hc0]|].
    eapply (aexhc_frameK (sec_chunks_of st) L st st' m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.c6_std. left. clear -LO BOT. unfold AFREE_STACK in *. lia.
    - left. unfold AC6U.c6_std. do 6 right; left. clear. lia.
    - do 4 right. unfold AC6U.c6_imgp, AIMG_HI. clear. lia.
    - left. unfold AC6U.c6_std. right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 7 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 8 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 9 right; left. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.c6_std. do 4 right; left. clear -SHR. lia. }
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      destruct (CHK _ lmb lms ln NTHL NEli) as (Wj & _ & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End S.
End CANSEC3.
End ADeallocSF_big.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module ASecRecycle.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
Lemma u64arr_app_inv' : forall m A ws1 ws2, u64arr bsegs m A (ws1 ++ ws2) ->
  u64arr bsegs m A ws1 /\ u64arr bsegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [HB HW]. rewrite u64s_app in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite u64s_length in HB2. replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) in HB2 by lia.
  rewrite length_app in HW. destruct HW as (H0 & H1 & HW).
  split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + 8 * Z.of_nat (length ws1) + i) with (A + (8 * Z.of_nat (length ws1) + i)) by lia. apply HW. lia.
Qed.

Lemma junk_of_u64arr' : forall m A ws, u64arr bsegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [| exact I]. rewrite u64s_length. lia.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)))) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma map_upd : forall {A B} (f : A -> B) (l : list A) i x, map f (upd l i x) = upd (map f l) i (f x).
Proof. intros A B f l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma upd_app_mid : forall {A} (l1 l2 : list A) (a x : A), upd (l1 ++ a :: l2) (length l1) x = l1 ++ x :: l2.
Proof. intros A l1. induction l1 as [|y l1 IH]; intros l2 a x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_snoc : forall {A} (l : list A) (a : A), firstn (length l) (l ++ [a]) = l.
Proof. intros A l a. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma nth_error_last_split : forall {A} (l : list A) n x,
  length l = S n -> nth_error l n = Some x -> l = removelast l ++ [x] /\ length (removelast l) = n.
Proof.
  intros A l n x HL HN.
  assert (NE : l <> []) by (intros ->; discriminate).
  pose proof (app_removelast_last x NE) as E.
  assert (LR : length (removelast l) = n) by (rewrite E, length_app in HL; cbn in HL; lia).
  split; [| exact LR].
  assert (HN' : nth_error (removelast l ++ [last l x]) n = Some x) by (rewrite <- E; exact HN).
  rewrite nth_error_app2 in HN' by lia. rewrite LR, Nat.sub_diag in HN'. cbn in HN'. injection HN' as HN'.
  transitivity (removelast l ++ [last l x]); [exact E| rewrite HN'; reflexivity].
Qed.

Lemma disjoint_from_Forall : forall W A k, disjoint_from W A k <-> Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W.
Proof.
  intros W A k. induction W as [|[lo hi] W IH]; cbn.
  - split; [intros _; constructor| intros _; exact I].
  - split.
    + intros [H1 H2]. constructor; [cbn; exact H1| apply IH; exact H2].
    + intros HF. inversion HF; subst. split; [assumption| apply IH; assumption].
Qed.

Lemma sec_wf1_facts : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n
  /\ 64512 < n <= AREQMAX /\ rz_size n = 2048 /\ 73728 <= ms <= 4293926912 /\ ms mod 4096 = 0
  /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n /\ sec_clear L mb ms.
Proof.
  intros L mb ms n W. cbn [sec_wf1] in W. destruct W as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  repeat (split; [first [assumption | lia]|]). exact G7.
Qed.

Lemma bases_dominated : forall L cs mb ms n,
  Forall (sec_wf1 L) cs -> sec_disjoint cs -> In (CSec mb ms n) cs ->
  Forall (fun b => 0 <= b < 2^64 /\ (b <= mb + 6128 -> b <= mb)) (map sec_mb cs).
Proof.
  intros L cs mb ms n WF [ND D] IN. rewrite Forall_map. rewrite Forall_forall in WF |- *. intros ch Hch.
  pose proof (WF ch Hch) as W1. pose proof (WF _ IN) as W0.
  destruct ch as [c k|mb' ms' n']; [destruct W1|]. cbn [sec_mb].
  destruct (sec_wf1_facts _ _ _ _ W1) as (_ & A2 & A3 & _ & _ & _ & A7 & _).
  destruct (sec_wf1_facts _ _ _ _ W0) as (_ & B2 & B3 & _ & _ & _ & B7 & _).
  pose proof (ablk_lin _ _ A2) as (A2a & A2b & A2c & A2d). pose proof (ablk_lin _ _ B2) as (B2a & B2b & B2c & B2d).
  unfold K_HIGH_MEM in *. split; [lia|]. intros LE.
  assert (DEC : {CSec mb' ms' n' = CSec mb ms n} + {CSec mb' ms' n' <> CSec mb ms n}) by (repeat (decide equality)).
  destruct DEC as [E|NE]; [injection E as -> -> ->; lia|].
  destruct (D _ _ Hch IN NE) as [X|X]; cbn [sec_mb sec_ms] in X; lia.
Qed.

Lemma rw_cells_hd' : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [H _]. exact H. Qed.
Lemma rw_cells_tl' : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.
Lemma rw_cells_cons' : forall m A c cs,
  rw_cells bsegs m A [c] -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs -> rw_cells bsegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app bsegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma mtx4_join : forall m, rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xd88c1 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xd88c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H1 H2. apply rw_cells_cons'; [exact H1| exact H2]. Qed.
Lemma mtx4_split : forall m, rw_cells bsegs m 0xd88c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0xd88c1 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. split; [eapply rw_cells_hd'; exact H| apply rw_cells_tl' in H; exact H]. Qed.

Lemma sec_shadow_cb : forall m mb ms n lv, asec_chunk m (CSec mb ms n) 0 lv \/ (exists idx, asec_chunk m (CSec mb ms n) idx lv) ->
  mb mod 4096 = 0 -> 64512 < n <= AREQMAX -> ms = sec_map_size n -> is_primary n = false ->
  exists shj, rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj].
Proof.
  intros m mb ms n lv CH MAL NB MSE NPR.
  assert (CH' : exists idx, asec_chunk m (CSec mb ms n) idx lv) by (destruct CH as [CH|CH]; [exists 0; exact CH| exact CH]).
  clear CH. destruct CH' as [idx CH].
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- MSE in MSR, MSM, MSB.
  cbn [asec_chunk] in CH. destruct CH as (_ & _ & _ & _ & _ & _ & S1 & S2 & S3). unfold SEC_UOFF in *.
  assert (GR : 0 <= granules n /\ shad (mb + 6144) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules. rewrite !shad_div, shlen_div. clear -MAL NB RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3). rewrite GR2 in S2, S3.
  apply cb_of_fill in S1. apply cb_of_fill in S3.
  pose proof (cb_app m (shad mb) _ _ _ _ S1 ltac:(rewrite Z2Nat.id by lia; exact S2)) as S12.
  replace (shad mb + 768 + granules n) with (shad mb + Z.of_nat (Z.to_nat 768 + Z.to_nat (granules n))) in S3 by (clear -GR1; lia).
  pose proof (cb_app m (shad mb) _ _ _ _ S12 S3) as S123.
  eexists. replace (Z.to_nat (shlen ms)) with (Z.to_nat 768 + Z.to_nat (granules n) + Z.to_nat (ms / 8 - 768 - granules n))%nat; [exact S123|].
  rewrite shlen_div. clear -GR1 GR3. lia.
Qed.

Lemma premap_of_rt : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  unfold premap_cells. split; [eapply rw_cells_hd'; exact R11|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.

Lemma poison_cells_of_rt : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma asec_chunk_frameD : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells bsegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

Lemma cb_zeros_at : forall m A n j, rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  AIMG_HI <= A -> 0 <= j < n -> m (wa (A + j)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n j [[_ B] _] HA Hj. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  rewrite repeat_length in B1, B. specialize (B (Z.to_nat j) ltac:(lia)). rewrite (@nth_error_repeat _ (Z_to_bv 8 0) (Z.to_nat n) (Z.to_nat j) ltac:(clear -Hj; lia)) in B.
  replace (A + Z.of_nat (Z.to_nat j)) with (A + j) in B by lia.
  unfold mrd in B. destruct (m (wa (A + j))) as [b|] eqn:E; [congruence|].
  exfalso. rewrite ref_seg_rom_none in B; [discriminate|]. rewrite wa_unsigned by lia. unfold AIMG_HI in HA. lia.
Qed.

Lemma fstepS_munmap_after_le : forall a l rsp rsp' R R1 R',
  fp_le R R1 -> fstepS (NMunmap a l) rsp R1 R' -> fstepS (NMunmap a l) rsp' R R'.
Proof.
  intros a l rsp rsp' R R1 R' LE [HA HS]. cbn [fstepA fstepS] in HA, HS |- *. split.
  - intros b j Hb Hd. apply HA; [apply LE; exact Hb| exact Hd].
  - eapply fp_le_trans; [exact LE| exact HS].
Qed.

Theorem srec : srec_stmt ASECc RSEC.
Proof.
  unfold srec_stmt.
  intros AQ AD AF cs1 cs2 R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m st X mb ms n CBA lo SHO ALO ARNG RS AR MI ST CEIL LO SPHI TP -> -> RA RSTK KONT.
  set (ch := CSec mb ms n) in *. set (cs := cs1 ++ ch :: cs2) in *.
  assert (IN : In ch cs) by (subst cs; apply in_elt).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.

  pose proof AR as AR0.
  destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot ah_fake AHS] in HQ, HS, HD.
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT RT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & TK & _ & _ & _ & _ & _ & _ & _ & _ & _ & T88 & TSD & _ & _ & CT).
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  pose proof THR as THR0. destruct THR0 as (Tc0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof HS as HS0. destruct HS0 as (WFS & SARR & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct SARR as (order & PO & U64 & JK & PER).
  pose proof (Permutation_length PO) as LENO.
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch IN) as WFch.
  destruct (sec_wf1_facts L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL).
  pose proof NB as NB0. destruct WFch as (_ & _ & _ & _ & _ & NPR & _).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & _).

  destruct (PER i ch NTH) as (lv & _ & CH). pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & H2 & H3 & H4 & (b1 & cx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in H5. replace (mb + 6144 - 16) with (mb + 6128) in H5 by lia.
  destruct (sec_shadow_cb m mb ms n lv (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].

  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- WL, <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- WL, <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. all: split; [clear -LCE LMSB; lia|].     all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: clear -LC_p LMSB WR WB; lia. }

  eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (CBA := CBA) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 (if lv then 2 else 3)) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PRM
       | |- arelro0 _ => exact HRO
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; unfold PG; clear -RZ; lia]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680| exact PAD]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => first [eassumption | exact I32 | exact I64 | exact I72 | exact I112 | exact ISRT | exact TI | exact TK | exact T88 | exact TSD | exact H1]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- WL, <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map, LENO; exact WL
       | |- _ -> _ /\ _ => exact LHDR
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact (proj1 ARNG)
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ (shad _) _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [_ RH]; cbn [sec_mb sec_ms] in RH; rewrite shlen_div; exact RH
       | |- rng _ (al_ptr_array _) _ => destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RP & _); exact RP
       | |- rng _ (al_t _) _ => destruct ARNG as (_ & RT1 & _); exact RT1
       | |- rng _ (al_ctx _) _ => destruct ARNG as (_ & _ & RC & _); eapply rng_sub'; [exact RC|]; clear; lia
       | |- rng _ _ _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [RH _]; cbn [sec_mb sec_ms] in RH; exact RH
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in CEIL, LO, SPHI, OT, OC, OP, MLO, MCE, NB |- *.
  all: pose proof (alayout_ctx L ALO) as (_ & _ & CXI' & _); pose proof (alayout_t L ALO) as (_ & _ & _ & TIC').
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- iclr _ _ => exact TIC' | |- AIMG_HI <= al_ctx _ => exact CXI' | |- a_nres _ <= 1048576 => clear -WR; lia
       | |- sclr (al_ctx _) _ => exact (proj1 (alayout_ctx L ALO)) | |- sclr (al_t _) _ => exact (proj1 (alayout_t L ALO))
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- _ => try first [ assumption | exact SC_t
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -OC; lia | clear -OT; lia | clear -OP WR WB; lia | clear -IL LENO WL; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia ]
       end.

  intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  apply KONT. unfold srec_ret.
  destruct PP as (MU & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold sdealloc_W in MU.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- WL, <- LENO; clear -IL; lia).
  exists u0, u1, u2, b0, b1', b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (lmb + 24).
  split; [reflexivity|]. split; [reflexivity|].
  split.
  {   unfold srec_hl_ok, sec_clear, K_HIGH_MEM in *. destruct LSCL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. split; [clear -LCE LMSB; lia|].
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [clear -Q1 LMSB; lia | clear -Q2 LMSB; lia | clear -Q3 LMSB; lia | clear -Q4 LMSB; lia
            | clear -Q5 LMSB; lia | clear -Q6 LMSB; lia | clear -Q7 LMSB; lia | clear -Q8 LMSB; lia]. }
  split.
  {   replace (lmb + 24 - 24) with lmb by (clear; lia).
    destruct (Z.eq_dec lmb mb) as [E|NE].
    - left. rewrite E. clear -MSB. lia.
    - right. exists lms, ln. split; [| exact WFl].
      assert (INc : In (CSec lmb lms ln) cs) by (eapply Permutation_in; [exact PO| exact INl]).
      subst cs. apply in_app_iff in INc. apply in_app_iff. destruct INc as [H1'|[H1'|H1']]; [left; exact H1'| exfalso; apply NE; unfold ch in H1'; congruence| right; exact H1']. }
  split.
  {   eapply munch_weaken; [| exact MU]. unfold srec_W, AINSTANCE.
    let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *. clear -Hq I64b WB LO. lia. }
  split; [exact MI'|]. split; [exact ST'|].
  split.
  2: { split; [eapply fstepS_munmap_after_le; [exact LE1| exact HF]|].
       split.
       - eapply arng_mono; [exact LE|]. eapply arng_st; [| | | exact ARNG]; [intros c Hc; reflexivity| reflexivity|].
         rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st)) by reflexivity. apply Permutation_refl.
       - eapply RSEC_mono; [exact LE|]. unfold RSEC in RS |- *. subst cs. rewrite Forall_app in RS |- *.
         destruct RS as [RS1 RS2]. split; [exact RS1| exact (Forall_inv_tail RS2)]. }

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ MLO) as [kA MBND]. pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & _ & _). unfold AIMG_HI in ML1.
  destruct (ablk_int _ _ LLO) as [kL LBND]. pose proof (ablk_lin _ _ LLO) as (LL1 & _ & _ & _). unfold AIMG_HI in LL1.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s.
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  unfold adisj in D_t_r, D_p_r, D_t_n, D_t_s, D_n_p, D_s_p, D_t_f, D_f_p, D_t_d, D_d_p.
  pose proof LSCL as (_ & _ & LC_r & _ & LC_n & LC_st & LC_f & LC_d).
  pose proof SCL as (_ & _ & SC_r & _ & _ & _ & _ & _).
  assert (SHR : 0x800be200 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MBND ML1 MCE MSB; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_r as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 0x10007fef8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  destruct RSH as (SR1 & SR2 & SR3).
  assert (FSH : 0x800be200 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 0x10007fef8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK OFKi OFKs. Z.div_mod_to_equations. lia. }
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, LCE, LLO.

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall A kk, 65536 <= A -> 0 <= kk -> (A + kk <= 0xd8690 \/ (0xd88e8 <= A /\ A + kk <= AIMG_HI)) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_t : forall A kk, al_t L <= A -> 0 <= kk -> (A + kk <= al_t L + 2800 \/ (al_t L + 3168 <= A /\ A + kk <= al_t L + 4096)) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OT D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB OTs OTi. lia. }
  assert (K_ctx : forall A kk, al_ctx L <= A -> 0 <= kk -> A + kk <= al_ctx L + 65536 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OC D_t_c D_c_p LC_c SC_c SHR I64b WR WB MSB LMSB OT OTs OTi OCs OCi. lia. }
  assert (K_res : forall A kk, al_res L <= A -> 0 <= kk -> A + kk <= al_res L + 137439023104 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO ORS D_t_r D_p_r LC_r SC_r SHR I64b WR WB MSB LMSB OT OTs OTi RHI. lia. }
  assert (K_shres : forall A kk, shad (al_res L) <= A -> 0 <= kk -> A + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO SR1 SR2 SR3 SHSEP SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'. pose proof (alayout_space L ALO) as RSPs.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  split; [exact WF|].
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact Tc0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           eapply cells_frameD; [exact UNW| exact MU| apply K_t; clear; cbn; lia]. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  assert (K_nodes : disjoint_from Wd (al_nodes L) 1048576).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO ON D_t_n D_n_p LC_n SC_n SHR I64b WR WB OT LMSB MSB OTs OTi ONs ONi. lia. }
  assert (K_store : disjoint_from Wd (al_store L) 8388608).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OS D_t_s D_s_p LC_st SC_st SHR I64b WR WB OT LMSB MSB OTs OTi OSs OSi. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OFK D_t_f D_f_p LC_f SC_f SHR I64b WR WB OT LMSB MSB OTs OTi OFKs OFKi. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OD D_t_d D_d_p LC_d SC_d SHR I64b WR WB OT LMSB MSB OTs OTi ODs ODi. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO FSH SHSEPF SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }

  split.
  { eapply (sho_quar _ _ SHO L st _ X X m m' Wd); [exact HQ | exact MU | |].
    - unfold quar_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L) 208 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img (AINSTANCE + 728) 256 ltac:(clear; unfold AINSTANCE; lia) ltac:(clear; lia) ltac:(clear; unfold AINSTANCE, AIMG_HI; lia))) as F2.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xdce80 0x81030 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F3.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16b708 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
      rewrite Forall_forall in F1, F2, F3, F4. specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). cbn [fst snd] in F1, F2, F3, F4.
      split; [clear -F1; lia|]. split; [clear -F2; lia|]. split; [clear -F3; lia|]. split; [clear -F4; lia|].
      intros b Hb. destruct (BB b Hb) as [B1' B2']. pose proof (size_of_class_facts (xb_class b) (proj1 (BUSY b Hb))) as [QSb _].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_res (xb_alloc L b) (size_of_class (xb_class b)) B1' ltac:(clear -QSb; lia) B2')) as F5.
      rewrite Forall_forall in F5. specialize (F5 _ Hin). cbn [fst snd] in F5. destruct (xb_st b); [exact I| clear -F5; lia| clear -F5; lia].
    - unfold quar_same. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes a_space_beg set_nsec].
      repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }

  split.
  2: {   split.
       { eapply (sho_depot _ _ SHO L m m' Wd); [exact HD | exact MU |].
         pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1adb48 (0x5fdb90 - 0x1adb48) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F1.
         pose proof (proj1 (disjoint_from_Forall _ _ _) K_nodes) as F2. pose proof (proj1 (disjoint_from_Forall _ _ _) K_store) as F3.
         apply Forall_forall. intros [qlo qhi] Hin a Ha. rewrite Forall_forall in F1, F2, F3.
         specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). cbn [fst snd] in F1, F2, F3, Ha. clear -F1 F2 F3 Ha. lia. }

       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact RT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  assert (K_hi : forall A kk, (A + kk <= 65536 \/ 6492160 <= A) -> (A + kk <= 2147446784 \/ 17594333495296 <= A) -> 0 <= kk -> A + kk <= ATOP ->
            (A + kk <= mb \/ mb + ms <= A) -> (A + kk <= lmb + 24 \/ lmb + 32 <= A) ->
            (A + kk <= al_t L \/ al_t L + 4096 <= A) -> (A + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
            disjoint_from Wd A kk).
  { intros A kk Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7. subst Wd. cbn [disjoint_from]. clear -Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 CEIL LO SHR I64b WR WB. lia. }
  assert (K_sh : forall A kk, 2147446784 <= A -> 0 <= kk -> A + kk <= 17594333495296 ->
            (A + kk <= shad mb \/ shad mb + shlen ms <= A) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 CEIL LO OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_pa : forall A kk, al_ptr_array L + 8 * a_nsec st <= A -> 0 <= kk -> A + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OP D_t_p LC_p SC_p SHR I64b WR WB MSB LMSB OT OTs OTi OPs OPi. lia. }

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall A kk, mb' + 32 <= A -> 0 < kk -> A + kk <= mb' + ms' -> disjoint_from Wd A kk)
          /\ (forall A kk, shad mb' <= A -> 0 < kk -> A + kk <= shad mb' + ms' / 8 -> disjoint_from Wd A kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL).
    destruct JSCL as (JC_t & _ & _ & JC_p & _). unfold K_HIGH_MEM in JLO, JCE.
    destruct (ablk_int _ _ JLO) as [kJ JB]. pose proof (ablk_lin _ _ JLO) as (JL1 & _ & _ & _). unfold AIMG_HI in JL1.
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 0x800be200 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -JB JL1 JCE JMSB; Z.div_mod_to_equations; lia).

    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [clear -Dc; lia|].
    all: split; [intros A kk Z1 Z2 Z3; apply K_hi; [clear -Z1 JL1; lia| clear -Z1 Z3 JB; lia| clear -Z2; lia| clear -Z3 JCE; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros A kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -JL1; lia| clear -JB JMSB; lia| clear; lia| clear -JCE JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (rewrite LENO; symmetry; exact WL).
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall c, sec_live (set_nsec (a_nsec st - 1) st) c <-> sec_live st c) by (intros c; unfold sec_live; cbn [a_live set_nsec]; apply iff_refl).
  assert (WFA : asec_wf L (set_nsec (a_nsec st - 1) st) (cs1 ++ cs2)).
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    subst cs. rewrite length_app in WL |- *. cbn [length] in WL.
    split; [clear -WL; lia|]. split; [clear -WL WB; lia|].
    split; [apply Forall_app in WF1 as [F1 F2]; apply Forall_app; split; [exact F1| exact (Forall_inv_tail F2)]|].
    destruct WD as [ND DJ]. split; [exact (NoDup_remove_1 _ _ _ ND)|].
    intros ci cj Hi Hj NE.
    apply DJ; [| | exact NE];
      [apply in_app_iff in Hi; apply in_app_iff; destruct Hi as [Hi|Hi]; [left; exact Hi| right; right; exact Hi]
      |apply in_app_iff in Hj; apply in_app_iff; destruct Hj as [Hj|Hj]; [left; exact Hj| right; right; exact Hj]]. }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; lia]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L (cs1 ++ cs2) m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
    assert (SX : 0x800be200 <= shad x < 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, KLS, AIMG_HI; exact Hx) HFh).
    2,4: subst cs; apply Forall_app in HC as [HC1 HC2]; apply Forall_app; split; [exact HC1| constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC2]].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia. }

  assert (AXH' : AEXHc (cs1 ++ cs2) L (set_nsec (a_nsec st - 1) st) m').
  { eapply (AEXHc_sub cs); [subst cs; intros c0 Hc0; apply in_app_iff in Hc0; apply in_app_iff; destruct Hc0 as [H0|H0]; [left; exact H0| right; right; exact H0]|].
    eapply (aexhc_frameK cs L st _ m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) cs) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.TwinB.c6_std. left. clear -CEIL LO. lia.
    - left. unfold AC6U.TwinB.c6_std. right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 4 right; left. clear -SHR. lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_app_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO. exact PO. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_app_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; exact PO].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite LVE; exact LVl|].
      destruct (CHK _ lmb lms ln NTHL ltac:(clear -NE; lia)) as (Wj & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End CANSEC1.
End ASecRecycle.

Module ASF_big.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoisonz.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aputrec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHolesD.TwinB. Import ASecRecycle.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.TwinB.ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_arep.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b70c); (t + 2800, t + 3169);
   (0x1adb48, 0x5fdb90); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xd8690, 0xd8699); (0xd86a8, 0xd86b8); (0xd88c0, 0xd88c4); (0xd88d8, 0xd88e8);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; lia.

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd88f0 \/ 0xd89b0 <= fst iv)
                                  /\ (snd iv <= 0xdce80 \/ 0x15deb0 <= fst iv)
                                  /\ (snd iv <= 0x16b708 \/ 0x16b70c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem afree_sec_big : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),

  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].

  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (Ni & Na & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (Si & Sa & [kS SBND]).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & OPa & [kP OPs]).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (Ci & Ca & [kC CBND]). pose proof (aobj4_int _ (ao_t L ALO)) as (Ti4 & Ta4 & [kT TBND] & [jT TIMG]).
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).

  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.

  pose proof HS as HS0. destruct HS0 as (WFS & _ & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).

  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts' L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL & _).
  pose proof (ablk_int _ _ LLO) as (kLl & KALl & KBLl & KELl & KCLl & KDLl).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & LC_n & LC_st & LC_f & LC_d).
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].     all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia| clear -LC_st LMSB; lia]. }

  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.

  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).

  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_spec DI L (q_ia Q) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo (al_top L) (al_bot L) uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).
  apply evtF_done.

  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148262400 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).

  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { intros NE. destruct (LHDR NE) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). atop_facts.
    pose proof (ablk_int _ _ L2) as (kL & KAL & KBL & KEL & KCL & KDL).
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). exact L7. }
  clear LHDR.

  name_sp sp (-2128).
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp0 gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (_ - _) => rewrite Hsp; eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: try rewrite Hsp.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.

  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  destruct PP as (MU2 & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold putrec_W in MU2.
  unname_sp.

  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply (cells_frameD _ m1 m') in SS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in TB1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FRS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  replace (ret_pc (Z_to_bv 64 388956)) with (Z_to_bv 64 388956) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  eapply evtF_mono.
  { eapply (ficptD_spec RNG' sp gp tp); [exact ST' | atop_facts; clear -BOT STK3; lia | clear -LO; lia | exact MI'
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia); exact TB1 | reflexivity]
      | exact FRS1 | eapply rng_fp_le; [exact LE| exact RIMG] | eapply rng_fp_le; [exact LE| exact RSTK] ]. }
  cbv beta. intros ms3 [-> ST3].

  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST3|].

  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  pose proof LSCL as (_ & _ & LC_r & _).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  destruct RSH3 as (SR1 & SR2 & SR3).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFi & OFa & [kF FBND]).
  assert (FSH : 2148262400 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->
            (Ad + kk <= 0xd8690 \/ (0xd88e8 <= Ad /\ Ad + kk <= 0xdce80) \/ (0x15deb0 <= Ad /\ Ad + kk <= 0x16b708)
             \/ (0x16b70c <= Ad /\ Ad + kk <= 0x1adb48) \/ (0x5fdb90 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6492160 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. pose proof (aobj4_int _ (ao_dtls L ALO)) as (ODi & ODa & [kD DBND] & [jD DIMG]). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).

  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - destruct BLK as (b & Hb & R). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: destruct (sec_wf1_facts' L mb' ms' n' G') as (_ & JLO & JCE & _ & JNB & _ & JMSB & _ & JNMS & _ & (JC_t & _ & _ & JC_p & JC_n & JC_st & _) & _ & JN6).
            all: pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + destruct (proj1 (proj2 BL) cls A' n' Hb) as (F1 & F2 & F3). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - destruct SHD as (a' & Ha' & ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].
        + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + destruct FK as (cls & FA & sz & Hin & R). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          destruct (proj1 (proj2 BL) cls FA sz Hin) as (F1 & F2 & F3).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree bsegs m m' (wa a) E). exact Hw. }

  split; [exact ALO|].
  split.
  {   eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: {
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| apply K_t; clear; lia | |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xd5470 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee38 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F5.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee48 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F6.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee68 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16d831 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16b718 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F5; lia| clear -F6; lia| clear -F7; lia| clear -F8; lia| clear -F9; lia].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }

  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }

  split.
  2: {
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts' L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL & _).
    destruct JSCL as (JC_t & _ & _ & JC_p & JC_n & JC_st & _). unfold K_HIGH_MEM in JLO, JCE.
    pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148262400 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.
    assert (SX : 2148262400 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].

  assert (AXH' : AEXHc cs' L st' m').
  { eapply (AEXHc_sub (sec_chunks_of st)); [intros c0 Hc0; eapply Permutation_in; [exact PD| right; exact Hc0]|].
    eapply (aexhc_frameK (sec_chunks_of st) L st st' m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.TwinB.c6_std. left. clear -LO BOT. unfold AFREE_STACK in *. lia.
    - left. unfold AC6U.TwinB.c6_std. do 6 right; left. clear. lia.
    - do 4 right. unfold AC6U.TwinB.c6_imgp, AIMG_HI. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 7 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 8 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 9 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 4 right; left. clear -SHR. lia. }
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      destruct (CHK _ lmb lms ln NTHL NEli) as (Wj & _ & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End S.
End CANSEC2.

End ASF_big.

Module ADeallocSF_big.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APoisonR_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rsrvshadow.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoisonz.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_asecdealloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecsec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aputrec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHolesD.TwinB. Import ASecRecycle.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.TwinB.ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_arep.TwinB.
Import ASF_big. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocLib.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1b. Context {rc : runConstT} {ov : annOV}.

Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

End CANSEC1b.
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; lia.

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC3. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd88f0 \/ 0xd89b0 <= fst iv)
                                  /\ (snd iv <= 0xdce80 \/ 0x15deb0 <= fst iv)
                                  /\ (snd iv <= 0x16b708 \/ 0x16b70c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem adealloc_sec_big : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),

  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 ZSS ZTB2 ZLTB2 ZLTRT ZTRF TRU ZSPS ZSTOP ZRS ZFLAG RA4 RSTK.
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].

  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).

  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (Ni & Na & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (Si & Sa & [kS SBND]).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & OPa & [kP OPs]).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (Ci & Ca & [kC CBND]). pose proof (aobj4_int _ (ao_t L ALO)) as (Ti4 & Ta4 & [kT TBND] & [jT TIMG]).
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -ZSPS ZSTOP; lia).

  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).

  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  assert (QIA : q_ia Q = true) by (eapply flag_ia_true; [exact FL| exact ZFLAG]). rewrite QIA in FL. specialize (IAM QIA).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.

  pose proof HS as HS0. destruct HS0 as (WFS & _ & SINST & PZ & SHZ & AXH).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).

  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts' L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL & _).
  pose proof (ablk_int _ _ LLO) as (kLl & KALl & KBLl & KELl & KCLl & KDLl).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & LC_n & LC_st & LC_f & LC_d).
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].     all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia| clear -LC_st LMSB; lia]. }

  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.

  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).

  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo SO pc uw (Z_to_bv 64 (al_top L)) (Z_to_bv 64 (al_bot L)) sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact ZTB2
         | |- map _ _ = _ => exact ZTRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (al_t L + 3168, al_t L + 3169); (mb + 6128, mb + 6128 + 4); (mb + 6128 + 16, mb + 6128 + 24); (al_t L + 2800, al_t L + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }
  apply evtF_done.

  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148262400 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).

  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { intros NE. destruct (LHDR NE) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). atop_facts.
    pose proof (ablk_int _ _ L2) as (kL & KAL & KBL & KEL & KCL & KDL).
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). exact L7. }
  clear LHDR.

  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (_ - _) => eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.

  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  destruct PP as (MU2 & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold putrec_W in MU2.

  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.

  apply evtF_done. unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].

  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.

  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  pose proof LSCL as (_ & _ & LC_r & _).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  destruct RSH3 as (SR1 & SR2 & SR3).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFi & OFa & [kF FBND]).
  assert (FSH : 2148262400 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).

  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->
            (Ad + kk <= 0xd8690 \/ (0xd88e8 <= Ad /\ Ad + kk <= 0xdce80) \/ (0x15deb0 <= Ad /\ Ad + kk <= 0x16b708)
             \/ (0x16b70c <= Ad /\ Ad + kk <= 0x1adb48) \/ (0x5fdb90 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6492160 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. pose proof (aobj4_int _ (ao_dtls L ALO)) as (ODi & ODa & [kD DBND] & [jD DIMG]). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }

  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }

  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).

  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - destruct BLK as (b & Hb & R). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: destruct (sec_wf1_facts' L mb' ms' n' G') as (_ & JLO & JCE & _ & JNB & _ & JMSB & _ & JNMS & _ & (JC_t & _ & _ & JC_p & JC_n & JC_st & _) & _ & JN6).
            all: pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + destruct (proj1 (proj2 BL) cls A' n' Hb) as (F1 & F2 & F3). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - destruct SHD as (a' & Ha' & ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].
        + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + destruct FK as (cls & FA & sz & Hin & R). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          destruct (proj1 (proj2 BL) cls FA sz Hin) as (F1 & F2 & F3).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree bsegs m m' (wa a) E). exact Hw. }

  split; [exact ALO|].
  split.
  {   eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: {
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| apply K_t; clear; lia | |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xd5470 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee38 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F5.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee48 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F6.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x60ee68 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16d831 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x16b718 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F5; lia| clear -F6; lia| clear -F7; lia| clear -F8; lia| clear -F9; lia].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }

  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. {   unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. {   unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  {
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }

  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }

  split.
  2: {
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.

  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts' L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL & _).
    destruct JSCL as (JC_t & _ & _ & JC_p & JC_n & JC_st & _). unfold K_HIGH_MEM in JLO, JCE.
    pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148262400 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }

  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.
    assert (SX : 2148262400 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: {
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }

  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].

  assert (AXH' : AEXHc cs' L st' m').
  { eapply (AEXHc_sub (sec_chunks_of st)); [intros c0 Hc0; eapply Permutation_in; [exact PD| right; exact Hc0]|].
    eapply (aexhc_frameK (sec_chunks_of st) L st st' m m' Wd ALO AXH MU); [| reflexivity| reflexivity].
    assert (INc : In (CSec lmb lms ln) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INl]).
    subst Wd. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil]; unfold c6_kind; cbn [fst snd]; intros NEV.
    - left. unfold AC6U.TwinB.c6_std. left. clear -LO BOT. unfold AFREE_STACK in *. lia.
    - left. unfold AC6U.TwinB.c6_std. do 6 right; left. clear. lia.
    - do 4 right. unfold AC6U.TwinB.c6_imgp, AIMG_HI. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 7 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 8 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 9 right; left. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 12 right. clear -I64b WB WR. lia.
    - right; right; left. exists (CSec lmb lms ln). split; [exact INc|]. split; [exact WFl|]. cbn [sec_mb sec_ms]. clear -LMSB. lia.
    - right; right; left. exists ch. split; [exact IN|]. split; [exact (proj1 (Forall_forall _ _) WF1 ch IN)|]. unfold ch. cbn [sec_mb sec_ms]. clear. lia.
    - left. unfold AC6U.TwinB.c6_std. do 4 right; left. clear -SHR. lia. }
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| split; [exact SHZn| exact AXH']]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  -
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  -
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    +
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      destruct (CHK _ lmb lms ln NTHL NEli) as (Wj & _ & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & _ & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End S.
End CANSEC3.
End ADeallocSF_big.
End TwinB.
