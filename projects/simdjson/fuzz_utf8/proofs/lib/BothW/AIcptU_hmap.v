(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation mem := (word -> option byte).

Ltac hstep := zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
Ltac amo_decide_sym :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?x)] =>
      replace (amo_aligned wd (Z_to_bv 64 x)) with true
        by (symmetry; unfold amo_aligned, amo_bytes; apply Z.eqb_eq; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite (Z.eqb_refl (bv_unsigned x)); cbv iota
  end.
Ltac amo_step_sym :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_decide_sym; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma rw_cells_recast_mid : forall (m : mem) A pre mid mid' post,
  rw_cells bsegs m A (pre ++ mid ++ post) -> cells_wf mid' -> cells_bytes mid' = cells_bytes mid -> cells_size mid' = cells_size mid ->
  rw_cells bsegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post H WF EB ES. pose proof H as [[HWF _] _].
  apply cells_wf_app in HWF as [W1 W23]. apply cells_wf_app in W23 as [W2 W3].
  eapply rw_cells_recast; [exact H | | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [exact WF| exact W3].
  - rewrite !cells_bytes_app, EB. reflexivity.
  - rewrite !cells_size_app, ES. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma munch_drop_eq : forall (W : list (Z * Z)) B n (m m' : mem),
  munch (W ++ [(B, B + n)]) m m' -> (forall x, B <= x < B + n -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) -> munch W m m'.
Proof.
  intros W B n m m' MU EQ x Hx.
  pose proof (bv_unsigned_in_range 64 x) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2^64) in RX.
  destruct (Z_le_gt_dec B (bv_unsigned x)) as [H1|H1]; [destruct (Z_lt_le_dec (bv_unsigned x) (B + n)) as [H2|H2]|].
  - specialize (EQ (bv_unsigned x) ltac:(lia) RX). unfold wa in EQ. rewrite Z_to_bv_bv_unsigned in EQ. exact EQ.
  - apply MU. clear MU EQ. induction W as [|[l h] W IH]; cbn in *; [split; [lia| exact I]|]. destruct Hx as [Hx1 Hx2]. split; [exact Hx1| exact (IH Hx2)].
  - apply MU. clear MU EQ. induction W as [|[l h] W IH]; cbn in *; [split; [lia| exact I]|]. destruct Hx as [Hx1 Hx2]. split; [exact Hx1| exact (IH Hx2)].
Qed.
(* [comment removed for export] *)
Lemma rw_cells_same_bytes : forall (m m' : mem) A cs, rw_cells bsegs m A cs -> rw_cells bsegs m' A cs -> 0x6d2000 <= A ->
  forall x, A <= x < A + Z.of_nat (cells_size cs) -> m' (wa x) = m (wa x).
Proof.
  intros m m' A cs [[WF (B0 & B1 & B)] _] [[_ (_ & _ & B')] _] HA x Hx.
  rewrite (cells_bytes_length cs WF) in *.
  specialize (B (Z.to_nat (x - A)) ltac:(lia)). specialize (B' (Z.to_nat (x - A)) ltac:(lia)).
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in B, B' by lia.
  rewrite (mrd_no_image bsegs m A (A + Z.of_nat (cells_size cs)) x) in B by (try apply RtCells.no_image_asan; lia).
  rewrite (mrd_no_image bsegs m' A (A + Z.of_nat (cells_size cs)) x) in B' by (try apply RtCells.no_image_asan; lia).
  rewrite B, B'. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hi_disjoint : forall (W : list (Z * Z)) HI A n, Forall (fun iv => HI <= fst iv) W -> A + n <= HI -> disjoint_from W A n.
Proof. intros W HI A n H HA. induction H as [|[l h] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

Lemma bytes_eq_of_unsigned_i : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Definition HMAP : Z := 0x17a8c8.

(* [comment removed for export] *)
Definition hm_bucket0 : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24)].
(* [comment removed for export] *)
Definition hm_handle_miss (B addr : Z) : list cell :=
  [C8 (Z_to_bv 64 HMAP); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 addr); C8 (Z_to_bv 64 0xffffffff);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition acquire_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo T h addr boff : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (h, h + 43); (T + boff, T + boff + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' h (hm_handle_miss (T + boff) addr)
    /\ rw_cells bsegs m' (T + boff) hm_bucket0.

Lemma acquire_miss_spec : forall RNG (lo T h addr boff : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (j1 j2 j3 : word) (jc : byte),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> KHIGH <= lo -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 HMAP -> a1 = Z_to_bv 64 h -> bv_unsigned sp <= h -> h + 43 <= bv_unsigned sp + 4096 -> h + 43 <= 2^64 ->
  ((addr = 0x176df0 /\ boff = 596640) \/ (addr = 0x176c10 /\ boff = 2256600)) ->
  rw_cells bsegs m HMAP [C8 (Z_to_bv 64 T)] ->
  rw_cells bsegs m h [C8 (Z_to_bv 64 HMAP); C8 j1; C8 j2; C8 (Z_to_bv 64 addr); C8 j3; C1 jc; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (T + boff) hm_bucket0 ->
  0x6d2000 <= T -> T + 0x38e000 <= lo -> T mod 8 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG h 43 -> rng RNG (T + boff) 120 -> rng_aimg RNG ->
  evtF bsegs RNG (acquire_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo T h addr boff m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x75b48) fc None m (seg_rom bsegs)).
Proof.
  intros until jc. intros ST LO KH MI -> -> HLO HHI SP47 HA MAPC HC BC TLO THI TAL RSTK RH RB RIMG.
  unfold HMAP, hm_bucket0 in *. unfold KHIGH in KH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (h, h + 43); (T + boff, T + boff + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct HA as [[-> ->]|[-> ->]].
  all: apply (proj1 (rw_cells_app bsegs m _ [C8 (Z_to_bv 64 0)] _)) in BC; destruct BC as [MTX BC]; cbn [cells_size csize Nat.add] in BC; change (Z.of_nat 8) with 8 in BC.
  1: replace (T + 596640 + 8) with (T + 596648) in BC by lia.
  2: replace (T + 2256600 + 8) with (T + 2256608) in BC by lia.
  all: carve_frame 176%nat ST.
  all: steps_to 0x75e98%Z.
  all: amo_step_sym; astep; amo_step_sym; astep.            (* [comment removed for export] *)
  all: steps_to 0x761bc%Z.
  all: amo_step_sym; astep; amo_step_sym; astep.            (* [comment removed for export] *)
  all: steps_to 0x75fe4%Z.
  all: match goal with H : rw_cells _ _ (bv_unsigned ?spv + -176) _, S : stk _ _ _ _ |- _ => release_frame H S (bv_unsigned spv) end.
  all: hstep; hstep.
  all: apply evtF_done; unfold acquire_post, hm_handle_miss, hm_bucket0, HMAP; do 16 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|]; split; [exact HC|].
  all: apply (proj2 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0)] _)); split; [exact MTX|]; cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8.
  1: replace (T + 596640 + 8) with (T + 596648) by lia.
  2: replace (T + 2256600 + 8) with (T + 2256608) by lia.
  all: exact BC.
Qed.
End CANSEC1.
