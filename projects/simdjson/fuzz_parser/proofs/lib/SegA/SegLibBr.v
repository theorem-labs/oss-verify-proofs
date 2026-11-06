(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.
Open Scope Z_scope.

Module SLB.
Section S.
Variable segs : list Segment.

Lemma u64 : forall i, 0 <= i < 2^64 -> bv_unsigned (Z_to_bv 64 i) = i.
Proof. intros i Hi. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; cbn; lia]. Qed.

Lemma urange : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma msteps_mstepsF_none : forall E ms ms', msteps segs ms ms' -> ExecF.mstepsF segs (SX.fp_of None E) ms ms'.
Proof.
  intros E ms ms' H. induction H as [ms|ms ms1 ms2 [Hsvc Hs] _ IH]; [constructor|].
  econstructor; [exact (SX.stepF_true segs ms ms1 Hsvc Hs) | exact IH].
Qed.

Lemma evt_evtF_none : forall E Q ms, evt segs Q ms -> ExecF.evtF segs (SX.fp_of None E) Q ms.
Proof. intros E Q ms (ms' & Hr & HQ). exists ms'. split; [exact (msteps_mstepsF_none E ms ms' Hr) | exact HQ]. Qed.

Section E.
Variable E : env.
Variable M : word -> option byte.

(* [comment removed for export] *)
Lemma kn_blob_bytes : forall b k n kk, kentry_ok segs E M (KBlob (SA b k) n kk) ->
  bytes_at segs M (bv_unsigned (edenot E b) + k) (eb E kk) /\ length (eb E kk) = Z.to_nat (bv_unsigned (edenot E n))
  /\ 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n) <= 2^64.
Proof.
  intros b k n kk (Hfl & Hl & Hz). destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off] in *.
  split; [|split; [lia | split; lia]].
  split; [lia|]. split; [lia|]. intros i Hi. unfold mrd, wa.
  specialize (Hz (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in Hz. rewrite Hz.
  symmetry. apply nth_error_nth'. exact Hi.
Qed.

Lemma kn_wr_at : forall b k n, kentry_ok segs E M (KWr (SA b k) n) ->
  wr_at segs M (bv_unsigned (edenot E b) + k) (bv_unsigned (edenot E n)).
Proof.
  intros b k n (Hfl & Hs). destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off] in *.
  split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (Hs i 1%nat ltac:(lia) ltac:(lia)) as S1.
  pose proof (store_ok_wview segs M _ 1 0 S1 ltac:(lia)) as W. rewrite u64 in W by lia. rewrite Z.add_0_r in W. exact W.
Qed.

Lemma kn_defined : forall b k n, kentry_ok segs E M (KUnk (SA b k) n) ->
  forall i, 0 <= i < bv_unsigned (edenot E n) -> M (wa (bv_unsigned (edenot E b) + k + i)) <> None.
Proof.
  intros b k n (Hfl & Hd) i Hi. unfold elenZ in Hd. exact (Hd i Hi).
Qed.

(* [comment removed for export] *)
Lemma kn_rw_CB : forall b k n, kentry_ok segs E M (KWr (SA b k) n) -> kentry_ok segs E M (KUnk (SA b k) n) ->
  exists junk, rw_cells segs M (bv_unsigned (edenot E b) + k) [CB (Z.to_nat (bv_unsigned (edenot E n))) junk].
Proof.
  intros b k n HW HU. set (A := bv_unsigned (edenot E b) + k). set (nn := Z.to_nat (bv_unsigned (edenot E n))).
  pose proof (kn_wr_at b k n HW) as (W1 & W2 & W3).
  pose proof (kn_defined b k n HU) as HD.
  exists (map (fun i => match M (wa (A + Z.of_nat i)) with Some x => x | None => Z_to_bv 8 0 end) (seq 0 nn)).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_map, length_seq. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_map, length_seq; unfold nn; rewrite Z2Nat.id by (pose proof (urange (edenot E n)); lia); lia|].
    intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb i nn) eqn:Hlt; [|apply Nat.ltb_ge in Hlt; lia]. cbn [option_map Nat.add].
    unfold mrd. specialize (HD (Z.of_nat i) ltac:(unfold nn in Hi; lia)). fold A in HD.
    destruct (M (wa (A + Z.of_nat i))) as [x|]; [reflexivity | contradiction].
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. unfold nn. rewrite Z2Nat.id by (pose proof (urange (edenot E n)); lia).
    split; [exact W1|]. split; [exact W2|]. exact W3.
Qed.

(* [comment removed for export] *)
Lemma kn_bytes_of_unk : forall b k n, kentry_ok segs E M (KUnk (SA b k) n) ->
  exists bs, bytes_at segs M (bv_unsigned (edenot E b) + k) bs /\ length bs = Z.to_nat (bv_unsigned (edenot E n)).
Proof.
  intros b k n HU. set (A := bv_unsigned (edenot E b) + k). set (nn := Z.to_nat (bv_unsigned (edenot E n))).
  destruct HU as (Hfl & Hd). destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off] in *.
  exists (map (fun i => match M (wa (A + Z.of_nat i)) with Some x => x | None => Z_to_bv 8 0 end) (seq 0 nn)).
  split; [|rewrite length_map, length_seq; reflexivity].
  split; [lia|]. split; [rewrite length_map, length_seq; unfold nn; rewrite Z2Nat.id by (pose proof (urange (edenot E n)); lia); lia|].
  intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb i nn) eqn:Hlt; [|apply Nat.ltb_ge in Hlt; lia]. cbn [option_map Nat.add].
  unfold mrd. specialize (Hd (Z.of_nat i) ltac:(unfold nn in Hi; lia)). fold A in Hd. unfold wa in *.
  destruct (M (Z_to_bv 64 (A + Z.of_nat i))) as [x|]; [reflexivity | contradiction].
Qed.

(* [comment removed for export] *)
Lemma kn_stk : forall b k n, kentry_ok segs E M (KWr (SA b k) n) -> kentry_ok segs E M (KUnk (SA b k) n) ->
  stk segs M (bv_unsigned (edenot E b) + k) (bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n)).
Proof.
  intros b k n HW HU. pose proof (kn_wr_at b k n HW) as (W1 & W2 & W3). pose proof (kn_defined b k n HU) as HD.
  split; [exact W1|]. split; [exact W2|]. intros a Ha.
  replace a with (bv_unsigned (edenot E b) + k + (a - (bv_unsigned (edenot E b) + k))) by lia.
  split; [apply W3; lia|]. unfold mrd. specialize (HD (a - (bv_unsigned (edenot E b) + k)) ltac:(lia)).
  destruct (M _) as [x|]; [eexists; reflexivity | contradiction].
Qed.

Lemma kn_zero_bytes : forall b k n, kentry_ok segs E M (KZero (SA b k) n) ->
  forall i, 0 <= i < bv_unsigned (edenot E n) -> M (wa (bv_unsigned (edenot E b) + k + i)) = Some (Z_to_bv 8 0).
Proof. intros b k n (Hfl & Hz) i Hi. exact (Hz i Hi). Qed.

End E.

(* [comment removed for export] *)
Lemma kx_blob : forall E M' b k n kk,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n) <= 2^64 ->
  bv_unsigned (edenot E b) + k < 2^64 ->
  length (eb E kk) = Z.to_nat (bv_unsigned (edenot E n)) ->
  (forall i, 0 <= i < bv_unsigned (edenot E n) -> M' (wa (bv_unsigned (edenot E b) + k + i)) <> None) ->
  bytes_at segs M' (bv_unsigned (edenot E b) + k) (eb E kk) ->
  kentry_ok segs E M' (KBlob (SA b k) n kk).
Proof.
  intros E M' b k n kk H0 H1 H2 Hl Hd (B1 & B2 & HB). cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
  pose proof (urange (edenot E n)) as Rn.
  split; [unfold flat, estart, elenZ; cbn [a_base a_off]; lia|]. split; [rewrite Hl, Z2Nat.id by lia; reflexivity|].
  intros i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia. unfold mrd in HB.
  specialize (Hd i Hi). unfold wa in *. destruct (M' (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i))) as [x|]; [|contradiction].
  rewrite HB. apply nth_error_nth'. rewrite Hl. lia.
Qed.

(* [comment removed for export] *)
Definition env_ext (E : env) (n : nat) (l : list word) : env :=
  Env (fun v => if Nat.ltb v n then ev E v else nth (v - n) l (Z_to_bv 64 0)) (eb E).

Lemma env_ext_lt : forall E n l v, (v < n)%nat -> ev (env_ext E n l) v = ev E v.
Proof. intros E n l v H. cbn [env_ext ev]. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma gagree_ext : forall G E n l, (G <= n)%nat -> SP.gagree G E (env_ext E n l).
Proof. intros G E n l H j Hj. symmetry. apply env_ext_lt. lia. Qed.

(* [comment removed for export] *)
Lemma mbytes_of_bytes_at : forall m A bs, bytes_at segs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (wa (A + i)) <> None) ->
  forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros m A bs (B1 & B2 & HB) Hd i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia. unfold mrd in HB.
  specialize (Hd i Hi). unfold wa in *. destruct (m (Z_to_bv 64 (A + i))) as [x|]; [|contradiction].
  rewrite HB. apply nth_error_nth'. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_of_munch : forall E W M M',
  munch (map (SP.win_den E) W) M M' -> forall x : word, SP.outside_wins E W (bv_unsigned x) -> M' x = M x.
Proof.
  intros E W M M' HM x Hx. apply HM. clear HM. unfold SP.outside_wins in Hx. induction W as [|w W IH]; [exact I|].
  inversion Hx as [|w0 W0 Hw HW]; subst. cbn [map outside]. destruct (SP.win_den E w) as [lo hi] eqn:Ew. split; [lia|].
  exact (IH HW).
Qed.

End S.
End SLB.
