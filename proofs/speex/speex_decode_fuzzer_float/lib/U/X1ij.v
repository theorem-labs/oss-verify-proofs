(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4.
Import ListNotations.
Open Scope Z_scope.

Definition cmod (W : list (Z * Z)) (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma cmod_refl : forall W LB SP m, cmod W LB SP m m.
Proof. intros W LB SP m a _ _ _. auto. Qed.

Lemma cmod_trans : forall W LB SP m1 m2 m3, cmod W LB SP m1 m2 -> cmod W LB SP m2 m3 -> cmod W LB SP m1 m3.
Proof.
intros W LB SP m1 m2 m3 H1 H2 a Ha Hc Ho. destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2].
split; [congruence| auto].
Qed.

Lemma cmod_weaken : forall W W' LB LB' SP SP' m m',
cmod W LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> sub_fp W W' -> cmod W' LB' SP' m m'.
Proof.
intros W W' LB LB' SP SP' m m' H HS HL HW a Ha Hc Ho. apply H; [exact Ha| | apply HW; exact Ho].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma cmod_of_rheap_pres : forall W LB SP m m', rheap_pres LB SP m m' -> cmod W LB SP m m'.
Proof. intros W LB SP m m' H a Ha Hc _. apply H; assumption. Qed.

Lemma cmod_of_munch : forall W LB SP m m', munch W m m' -> wmono rsegs m m' -> cmod W LB SP m m'.
Proof.
intros W LB SP m m' MU WM a Ha _ Ho. split.
- apply MU. rewrite wa_unsigned by lia. exact Ho.
- apply WM.
Qed.

Lemma cmod_bytes_at : forall W LB SP m m' A bs,
cmod W LB SP m m' -> bytes_at rsegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
disjoint_from W A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
intros W LB SP m m' A bs HP (H0 & H1 & HB) HR HD. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])
ltac:(eapply disjoint_outside; [exact HD| lia])) as [E _].
rewrite E. reflexivity.
Qed.

Lemma cmod_wr_at : forall W LB SP m m' A n,
cmod W LB SP m m' -> wr_at rsegs m A n -> rclient_range LB SP A n -> disjoint_from W A n -> wr_at rsegs m' A n.
Proof.
intros W LB SP m m' A n HP (H0 & H1 & HW) HR HD. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])
ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ W'].
apply W'. apply HW. exact Hi.
Qed.

Lemma cmod_rw_cells : forall W LB SP m m' A cs,
cmod W LB SP m m' -> rw_cells rsegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
intros W LB SP m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
- eapply cmod_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
- eapply cmod_wr_at; eauto.
Qed.

Lemma cmod_u8arr : forall W LB SP m m' A xs,
cmod W LB SP m m' -> u8arr rsegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
disjoint_from W A (Z.of_nat (length xs)) -> u8arr rsegs m' A xs.
Proof.
intros W LB SP m m' A xs HP [HB HW] HR HD. split; [eapply cmod_bytes_at; eauto| eapply cmod_wr_at; eauto].
Qed.

Lemma cmod_u32arr : forall W LB SP m m' A ws,
cmod W LB SP m m' -> u32arr rsegs m A ws -> rclient_range LB SP A (4 * Z.of_nat (length ws)) ->
disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr rsegs m' A ws.
Proof.
intros W LB SP m m' A ws HP [HB HW] HR HD. split.
- eapply cmod_bytes_at; eauto; rewrite u32s_length, Nat2Z.inj_mul; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; assumption.
- eapply cmod_wr_at; eauto.
Qed.

Lemma cmod_u64arr : forall W LB SP m m' A ws,
cmod W LB SP m m' -> u64arr rsegs m A ws -> rclient_range LB SP A (8 * Z.of_nat (length ws)) ->
disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
intros W LB SP m m' A ws HP [HB HW] HR HD. split.
- eapply cmod_bytes_at; eauto; rewrite u64s_length, Nat2Z.inj_mul; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; assumption.
- eapply cmod_wr_at; eauto.
Qed.

Lemma rclient_range_stack : forall LB SP A n, SP <= A -> rclient_range LB SP A n.
Proof. intros; left; assumption. Qed.
Lemma rclient_range_block : forall LB SP p A n A' n',
In (p, A, n) LB -> A <= A' -> A' + n' <= A + n -> rclient_range LB SP A' n'.
Proof. intros LB SP p A n A' n' HIN H1 H2. right; right. exists (p, A, n). cbn. auto. Qed.

Lemma cmod_drop_low : forall lo' hi W LB SP m m',
cmod ((lo', hi) :: W) LB SP m m' -> hi <= SP -> 0x6e000 <= lo' ->
(forall b, In b LB -> blk_addr b + blk_size b <= lo' \/ hi <= blk_addr b) -> cmod W LB SP m m'.
Proof.
intros lo' hi W LB SP m m' H Hhi Hlo HB a Ha Hc Ho. apply H; [exact Ha| exact Hc|]. cbn. split; [| exact Ho].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
destruct (HB b Hb); lia.
Qed.
