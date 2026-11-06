(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_decode's ASan build (image A), after the checks of
   a Theorem Labs lane's audit row PS-10 (premise-check-libreac-fuzz_decode.md) and the proof-by-computation form of
   lib/A/AD2l.v GrantB_syms and lib/A/ACej.v memZL_In: five facts about decode A's start-up record GrantB
   (lib/A/AD2l.v:16), each proved by vm_compute at the record. *)
(* DecodeACrtFacts: the instance facts that lib/A/DecodeClose.v takes as the hypotheses HB_CRT_CELLS,
   HB_RO_RD_UNOWNED, HB_CRT_UCTX, HB_CRT_UFIX and HB_LLVMF_UTRACES, stated at decode A's record:
   - B := GrantB (lib/A/AD2l.v:16): as_const := Tfib_const, as_owned_static := Tfib_owned_static and
     as_zero_shadow := Tfib_zero_shadow (lib/A/AF0m.v), as_universe := Tfib_universe (lib/A/ACej.v:103),
     as_code := Tfib_code (lib/A/AF0l.v:10, pc_malloc_ra0 0x52204, pc_free_ra0 0x520a4);
   - RA_LLVMF := 0x7ff60, the return address of target_run's `jal LLVMFuzzerTestOneInput` (0x7ff5c), the value of
     lib/A/ACfn.v:25 RA_LLVMF (lib/A/ACej.v:68-73 shows the listing line).
   Each Lemma has the form of its hypothesis at B := GrantB and RA_LLVMF := 0x7ff60. *)
From Stdlib Require Import ZArith Arith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AF0l AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require check_round_trip_cg LLVMFuzzerTestOneInput_cg.
Import ListNotations.
Open Scope Z_scope.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_round_trip_cg.
Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LLVMFuzzerTestOneInput_cg.

(* Boolean equality on the record's cells (lib/Reusable/YG0f.v:89-110 aexp / aval / acell), for membership by
   computation. *)
Fixpoint dacrt_aexp_eqb (x y : aexp) : bool :=
  match x, y with
  | ANum a, ANum b | ASp a, ASp b | AQ a, AQ b | AT a, AT b | AC a, AC b | AF a, AF b | ANB a, ANB b
  | ASB a, ASB b | ATop a, ATop b | ATsd a, ATsd b | AStk a, AStk b | AInst a, AInst b | ADepot a, ADepot b
  | AStore a, AStore b | ATp a, ATp b | AIal a, AIal b | AD a, AD b => Z.eqb a b
  | ASec r a, ASec s b => Nat.eqb r s && Z.eqb a b
  | ASh e, ASh f => dacrt_aexp_eqb e f
  | _, _ => false
  end.

Lemma dacrt_aexp_eqb_eq : forall x y, dacrt_aexp_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn [dacrt_aexp_eqb]; intros H; try discriminate H.
  all: repeat match goal with
       | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
       | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
       | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
       end.
  all: try (subst; reflexivity).
  f_equal. apply IHx. assumption.
Qed.

Definition dacrt_aval_eqb (x y : aval) : bool :=
  match x, y with
  | AV e, AV f => dacrt_aexp_eqb e f
  | AVmask m v, AVmask m' v' => Z.eqb m m' && Z.eqb v v'
  | _, _ => false
  end.

Lemma dacrt_aval_eqb_eq : forall x y, dacrt_aval_eqb x y = true -> x = y.
Proof.
  intros [e|m v] [f|m' v']; cbn [dacrt_aval_eqb]; intros H; try discriminate H.
  - f_equal. apply dacrt_aexp_eqb_eq, H.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition dacrt_cell_eqb (x y : acell) : bool :=
  dacrt_aexp_eqb (c_at x) (c_at y) && Nat.eqb (c_w x) (c_w y) && dacrt_aval_eqb (c_val x) (c_val y).

Lemma dacrt_cell_eqb_eq : forall x y, dacrt_cell_eqb x y = true -> x = y.
Proof.
  intros [a w v] [a' w' v']. unfold dacrt_cell_eqb. cbn [c_at c_w c_val]. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply dacrt_aexp_eqb_eq in H1. apply Nat.eqb_eq in H2. apply dacrt_aval_eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint dacrt_cell_mem (x : acell) (l : list acell) : bool :=
  match l with [] => false | y :: l' => dacrt_cell_eqb y x || dacrt_cell_mem x l' end.

Lemma dacrt_cell_mem_In : forall x l, dacrt_cell_mem x l = true -> In x l.
Proof.
  intros x l. induction l as [|y l IH]; cbn [dacrt_cell_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply dacrt_cell_eqb_eq, H | right; apply IH, H].
Qed.

(* Boolean equality and membership on traces (lists of return addresses). *)
Fixpoint dacrt_trace_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && dacrt_trace_eqb a' b'
  | _, _ => false
  end.

Lemma dacrt_trace_eqb_eq : forall a b, dacrt_trace_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn [dacrt_trace_eqb]; intros H; try discriminate H;
    [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH, H2.
Qed.

Fixpoint dacrt_trace_mem (t : list Z) (U : list (list Z)) : bool :=
  match U with [] => false | u :: U' => dacrt_trace_eqb u t || dacrt_trace_mem t U' end.

Lemma dacrt_trace_mem_In : forall t U, dacrt_trace_mem t U = true -> In t U.
Proof.
  intros t U. induction U as [|u U IH]; cbn [dacrt_trace_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply dacrt_trace_eqb_eq, H | right; apply IH, H].
Qed.

(* dec_tab_zshadow_at (check_round_trip_cg.v:168) from a search of as_zero_shadow. *)
Lemma dacrt_zshadow_of_b : forall (B : asyms) (T : Z),
  existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? T) && (T + 8 <=? fst r + snd r)) (as_zero_shadow B) = true ->
  PC.dec_tab_zshadow_at B T.
Proof.
  intros B T H. apply existsb_exists in H as (r & Hr & Hb).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold PC.dec_tab_zshadow_at. exists r.
  split; [exact Hr|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* HB_CRT_CELLS (DecodeClose.v:325): the 24 constant-cell rows are cells of Tfib_const, and the three value-0 table
   granules 0x20d40 / 0x20d80 / 0x20d60 lie in the Tfib_zero_shadow ranges (0x10000, 0x10d48) / (0x20d80, 8) /
   (0x20d60, 8). *)
Lemma dec_crt_cells_GrantB : @PC.dec_crt_cells GrantB.
Proof.
  intros ly.
  repeat match goal with
  | |- PC.dec_tab_zshadow_at _ _ => apply dacrt_zshadow_of_b; vm_compute; reflexivity
  | |- In _ _ => apply dacrt_cell_mem_In; vm_compute; reflexivity
  | |- _ /\ _ => split
  end.
Qed.

(* HB_RO_RD_UNOWNED (DecodeClose.v:329): every DEC_RO_RD range is disjoint from every Tfib_owned_static range. *)
Lemma dec_ro_rd_unowned_GrantB : PC.dec_ro_rd_unowned GrantB.
Proof.
  intros a Hin Hown. unfold PC.dec_in_ro_rd in Hin.
  apply Exists_exists in Hin as (r & Hr & Ha).
  apply Exists_exists in Hown as (r' & Hr' & Ha').
  assert (D : forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))
                (as_owned_static GrantB)) PC.DEC_RO_RD = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) D r Hr) as D1. cbv beta in D1.
  pose proof (proj1 (forallb_forall _ _) D1 r' Hr') as D2. cbv beta in D2.
  unfold in_zr in Ha, Ha'.
  apply orb_prop in D2 as [D2|D2]; apply Z.leb_le in D2; lia.
Qed.

(* HB_CRT_UCTX (DecodeClose.v:366): for the four contexts of check_round_trip's two calls, the first malloc's trace
   and the tail free's trace are in Tfib_universe. *)
Lemma dec_crt_uctx_GrantB : @PC.dec_crt_uctx GrantB (@PL.CTX_check_round_trip 0x7ff60).
Proof.
  intros c Hc.
  assert (D : forallb (fun c =>
      dacrt_trace_mem (PC.dec_utrace (pc_malloc_ra0 (as_code GrantB)) (PC.DEC_CRT_RA_MALLOC1 :: tl c))
        (as_universe GrantB) &&
      dacrt_trace_mem (PC.dec_utrace (pc_free_ra0 (as_code GrantB)) c) (as_universe GrantB))
    (@PL.CTX_check_round_trip 0x7ff60) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) D c Hc) as E. cbv beta in E.
  apply andb_prop in E as [E1 E2].
  split; apply dacrt_trace_mem_In; assumption.
Qed.

(* HB_CRT_UFIX (DecodeClose.v:367): the four fixed traces of check_round_trip (second malloc, calloc, two frees) are
   in Tfib_universe. *)
Lemma dec_crt_ufix_GrantB : @PC.dec_crt_ufix GrantB.
Proof.
  unfold PC.dec_crt_ufix.
  refine (conj _ (conj _ (conj _ _))); apply dacrt_trace_mem_In; vm_compute; reflexivity.
Qed.

(* HB_LLVMF_UTRACES (DecodeClose.v:365): LLVMFuzzerTestOneInput's three malloc and three free traces, under the
   chains [] and [RA_LLVMF], are in Tfib_universe. *)
Lemma dec_llvmf_utraces_GrantB : @PL.dec_llvmf_utraces 0x7ff60 GrantB.
Proof.
  intros sp Hsp. split; intros r Hr; apply dacrt_trace_mem_In.
  - assert (D : forallb (fun sp => forallb (fun r =>
        dacrt_trace_mem (PC.dec_utrace (pc_malloc_ra0 (as_code GrantB)) (r :: sp)) (as_universe GrantB))
        PL.DEC_LLVMF_RA_MALLOC) [[]; [0x7ff60]] = true) by (vm_compute; reflexivity).
    exact (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) D sp Hsp) r Hr).
  - assert (D : forallb (fun sp => forallb (fun r =>
        dacrt_trace_mem (PC.dec_utrace (pc_free_ra0 (as_code GrantB)) (r :: sp)) (as_universe GrantB))
        PL.DEC_LLVMF_RA_FREE) [[]; [0x7ff60]] = true) by (vm_compute; reflexivity).
    exact (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) D sp Hsp) r Hr).
Qed.
