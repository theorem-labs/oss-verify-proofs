(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk HeapIface Statics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export HeapIface Statics.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition statics_ok (segs : list Segment) (L : heap_layout) (m : mem) : Prop :=
  pristine (hl_data_lo L) (hl_data_hi L) (hl_written L) m.

Definition const_at (L : heap_layout) (A n : Z) : Prop :=
  hl_data_lo L <= A /\ A + n <= hl_data_hi L /\ forall a, A <= a < A + n -> ~ hl_written L a.

Lemma statics_ok_cells : forall segs L m A bs,
  statics_ok segs L m -> const_at L A (Z.of_nat (length bs)) -> img_bytes_b segs A bs = true ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
  intros segs L m A bs SOK (H1 & H2 & H3) Hb. eapply pristine_cells; eauto.
Qed.

Lemma statics_ok_write : forall segs L m (a : Z) (bs : list byte),
  statics_ok segs L m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (a + Z.of_nat (length bs) <= hl_data_lo L \/ hl_data_hi L <= a) ->
  statics_ok segs L (write_to_mem m (wa a) bs).
Proof.
  intros segs L m a bs SOK Ha Hl Hout. unfold statics_ok in *. eapply pristine_write; eauto. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Ltac solve_client_range :=
  first [ apply client_range_stack; lia
        | eapply client_range_block; [ eassumption | lia | lia ]
        | eapply client_range_block; [ eauto using in_eq, in_cons | lia | lia ] ].

(* [comment removed for export] *)
Ltac solve_client_wrange :=
  first [ apply client_wrange_stack; [lia | lia]
        | eapply client_wrange_block; [ eassumption | lia | lia ]
        | eapply client_wrange_block; [ eauto using in_eq, in_cons | lia | lia ] ].

(* [comment removed for export] *)
Ltac transport_heap segs m a bs :=
  repeat match goal with
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption (* [comment removed for export] *) | simpl_sizes; solve_client_wrange | lia | simpl_sizes; lia ]
            | idtac "note: could not carry HEAP hypothesis across the store at" a "(dropping it)"; clear H ]
  end.

Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  try (assert (Ha : (0 <= a)%Z) by first [tb_light_a a | lia]);
  try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by first [tb_light_l a | (simpl_sizes; slia)]);
  (lazymatch goal with
   | Ha' : (0 <= a)%Z, Hl' : (a + Z.of_nat (length bs) <= 2^64)%Z |- _ => transport_batch segs m a bs Ha' Hl'
   | _ => idtac
   end);
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | lia | simpl_sizes; lia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | lia | simpl_sizes; lia | simpl_sizes; lia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  end;
  try clear Ha; try clear Hl.

(* [comment removed for export] *)
Ltac heap_transport HP :=
  lazymatch type of HP with
  | heap_pres ?segs ?L ?LB ?SP ?m ?m' =>
    repeat match goal with
    | H : rw_cells segs m ?A ?cs |- _ =>
        first [ apply (heap_pres_rw_cells segs L LB SP m m' A cs HP) in H; [ | simpl_sizes; solve_client_range ]
              | idtac "note: dropping (not client memory across allocator call):" H; clear H ]
    | H : ro_cells segs m ?A ?cs |- _ =>
        first [ apply (heap_pres_ro_cells segs L LB SP m m' A cs HP) in H; [ | simpl_sizes; solve_client_range ]
              | idtac "note: dropping (not client memory across allocator call):" H; clear H ]
    | H : bytes_at segs m ?A ?bs |- _ =>
        first [ apply (heap_pres_bytes_at segs L LB SP m m' A bs HP) in H; [ | simpl_sizes; solve_client_range ]
              | idtac "note: dropping (not client memory across allocator call):" H; clear H ]
    | H : u8arr segs m ?A ?xs |- _ =>
        first [ apply (heap_pres_u8arr segs L LB SP m m' A xs HP) in H; [ | simpl_sizes; solve_client_range ]
              | idtac "note: dropping (not client memory across allocator call):" H; clear H ]
    | H : wr_at segs m ?A ?n |- _ =>
        first [ apply (heap_pres_wr_at segs L LB SP m m' A n HP) in H; [ | solve_client_range ]
              | clear H ]
    | H : stk segs m ?lo ?hi |- _ =>
        first [ apply (heap_pres_stk segs L LB SP m m' lo hi HP) in H; [ | lia ]
              | idtac "note: dropping stk hypothesis across allocator call:" H; clear H ]
    end
  end.
