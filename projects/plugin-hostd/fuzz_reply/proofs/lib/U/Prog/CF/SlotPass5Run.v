(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module names and numbers changed; 514 of its 611 lines of code are new or changed and 567 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5S.v, with its module paths and module names changed; 165 of its 257 lines of code are new or changed and 519 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5Run.v, with its module paths, module names and addresses changed; 119 of its 183 lines of code are new or changed and 193 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_source_c relay_reads_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Ltac u5_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac u5_nt := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; u5_cond] end.

Lemma op5_seg_a : forall (P N K SP : Z)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b]) ->
  store_ok rsegs m (Z_to_bv 64 (SP + 32)) 8 = true ->
  evt rsegs (fun ms => exists (s0 s1 s10 : word) (K' : Z),
      ms = MS (mkR (Z_to_bv 64 0x14498) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 s0 s1 (Z_to_bv 64 (SP + 40)) (Z_to_bv 64 48)
        (Z_to_bv 64 0x102a2) (Z_to_bv 64 0x103e6) s1 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 s10 x27
        x28 x29 x30 x31) F (Z_to_bv 64 0x187f8) fc None (write_to_mem m (Z_to_bv 64 (SP + 32)) (le8 (Z_to_bv 64 0)))
        ro /\
      s0 = Z_to_bv 64 (P + K') /\ s10 = Z_to_bv 64 (N - K') /\
      ((K < N /\ K' = K + 1 /\ s1 = zxb b) \/ (K = N /\ K' = K /\ s1 = Z_to_bv 64 0)))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143d8) fc None m ro).
Proof.
  intros P N K SP x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29
    x30 x31 F fc m ro b HK HN HP HPN RB HS.
  step. if_cases HC.
  - assert (HKN : K = N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia. }
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 3 eexists. exists K. split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. right. split; [exact HKN|]. split; reflexivity.
  - assert (HKN : K < N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_neq in HC. lia. }
    specialize (RB HKN).
    step. step. u5_nt.
    step. step. step. step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 3 eexists. exists (K + 1). split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. left. split; [exact HKN|]. split; reflexivity.
Qed.

Fixpoint op5_hit (fd : Z) (es : list rentry) : Z :=
  match es with
  | [] => 0
  | e :: es' => if re_fd e =? fd then (if re_eof e =? 0 then 1 else 0) else op5_hit fd es'
  end.

Definition op5_rec (es : list rentry) (fd op : Z) : Z := if op =? 0 then 0 else op5_hit fd es.

Lemma op5_hit_reads : forall fd es, relay_reads_r fd es = op5_hit fd es.
Proof.
  intros fd es. unfold relay_reads_r. induction es as [|e es IH]; cbn [src_find op5_hit]; [reflexivity|].
  destruct (re_fd e =? fd); [reflexivity|].
  destruct (src_find fd es) as [[k e']|]; exact IH.
Qed.

Lemma op5_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma op5_len : forall es, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H. destruct H as [(P1 & P2 & _) H].
  cbn [map concat length]. rewrite length_app, op5_entry_len by assumption. rewrite IH by assumption. lia.
Qed.

Lemma op5_bv : forall a b, a = b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b ->. reflexivity. Qed.

Ltac op5_eq := cbv beta; unfold mkR;
  repeat match goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  | |- write_to_mem _ _ _ = write_to_mem _ _ _ => f_equal
  end;
  try (apply op5_bv; unfold G_S in *; lia).

Lemma op5_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma op5_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma op5_rd4 : forall m a (v : word), bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma op5_slot2 : forall m (i : nat) fd op,
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 fd)) /\
  ov_read_bytes rsegs m (Z_to_bv 64 (G_S + 96 * Z.of_nat i + 4)) 4 = Some (le4 (Z_to_bv 64 op)).
Proof.
  intros m i fd op [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  apply bytes_at_app in H. destruct H as [H1 H2]. rewrite length_le4 in H2. split.
  - apply op5_rd4. exact H1.
  - replace (G_S + 96 * Z.of_nat i + 4) with (G_S + 96 * Z.of_nat i + Z.of_nat 4) by lia. apply op5_rd4. exact H2.
Qed.

Lemma op5_seg_b : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat 0)) (Z_to_bv 64 0x318a0) x21 x22 x23
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x318a0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14498) fc None m ro).
Proof.
  intros. step. step. apply evt_done. op5_eq.
Qed.

Definition op5_r_next (SP : Z) (i : nat) (v : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  ((S i < 4)%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (G_S + 96 * Z.of_nat (S i))) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat (S i))) x20 x21 x22
              (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None
           (write_to_mem m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) (le4 (Z_to_bv 64 v))) ro) \/
  (S i = 4%nat /\
   ms = MS (mkR (Z_to_bv 64 0x144c8) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (G_S + 384)) (Z_to_bv 64 (SP + 32)) x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27
              x28 x29 x30 x31) F (Z_to_bv 64 0x13664) fc None
           (write_to_mem m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) (le4 (Z_to_bv 64 v))) ro).

Lemma op5_r_ret : forall (SP v : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> wr_at rsegs m (SP + 16) 16 ->
  evt rsegs (op5_r_next SP i v x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28
      x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32))
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144b0) fc None m ro).
Proof.
  intros SP v i x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HS0 HS1 WR.
  pose proof (wr_at_store_ok rsegs m (SP + 16) 16 (4 * Z.of_nat i) 4 WR ltac:(lia)
    ltac:(change (Z.of_nat 4) with 4; lia)) as HS.
  step. step. step. step.
  if_cases HE; rewrite op5_eqb in HE by lia.
  - apply Bool.negb_true_iff, Z.eqb_neq in HE.
    apply evt_done. unfold op5_r_next. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.eqb_eq in HE.
    step. step. apply evt_done. unfold op5_r_next. right. split; [lia|]. op5_eq.
Qed.

Lemma op5_r_head : forall (SP fd op : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> 0 <= op < 2 ^ 31 ->
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] ->
  wr_at rsegs m (SP + 16) 16 ->
  evt rsegs (fun ms =>
      (op <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x144b0) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29
                  x30 x31) F (Z_to_bv 64 RELAY_READS) fc None m ro) \/
      (op = 0 /\
       op5_r_next SP i 0 x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30
         x31 F fc m ro ms))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x20 x21 x22 (Z_to_bv 64 (SP + 32))
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144a0) fc None m ro).
Proof.
  intros SP fd op i x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro Hi HS0 HS1 Hop HC WR.
  destruct (op5_slot2 m i fd op HC) as [_ RO].
  step. rewrite (op5_sx32 op) by lia.
  step. if_cases H0; rewrite op5_eqb in H0 by lia.
  - apply Z.eqb_eq in H0. subst op.
    eapply evt_mono; [apply op5_r_ret; [lia|lia|lia|exact WR]|].
    intros ms Hms. right. split; [reflexivity|exact Hms].
  - apply Z.eqb_neq in H0.
    step. step. apply evt_done. left. split; [exact H0|]. op5_eq.
Qed.
