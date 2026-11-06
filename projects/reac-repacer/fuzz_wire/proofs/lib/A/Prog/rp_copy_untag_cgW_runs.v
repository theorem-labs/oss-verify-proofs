(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: adapted from reac-repacer/fuzz_uci's lib/A/Prog/rp_uci_int_cgW_runs.v for reac-repacer/fuzz_wire's rp_copy_untag in image A: its tactics (rui_ -> rcu_) and its form of the instrumented-check lemmas copied; the runs written for this function. *)
(* rp_copy_untag_cgW_runs: the footprint runs (lib/Lib/ExecF.v evtF) of rp_copy_untag in image A (fuzz_wire.asan
   0x813e0, 93 instruction words, every one reached is stepped), in the form of reac-repacer/fuzz_uci's
   lib/A/Prog/rp_uci_int_cgW_runs.v. lib/A/Prog/rp_copy_untag_cgW.v carries the runs into the cgif walk and cuts the
   two calls between them (the checked memmove 0x51310 and reac_frame_is_reac 0x817bc) by the statement's premises.
   - rcu_seg_small: the prologue (frame 0x20; ra s0 s1 s2 stored at sp + 24 .. sp + 0), `bltu` at +0x1c taken
     (n < 50), +0x100 `li s0, 0` and the epilogue: return 0.
   - rcu_seg_pro: the prologue, `bltu` not taken, s1 = f (+0x20), the shadow base read through its GOT word into s2
     (+0x24 .. +0x2c), up to +0x30.
   - rcu_seg_tag: from +0x30 the tag test, four 1-byte loads of f[12], f[13], f[16], f[17] (+0x44, +0x64, +0x80,
     +0xa0), each after the instrumented check of its shadow byte; a mismatch goes to +0xb8 and the call of
     reac_frame_is_reac with a0 = f, a1 = n (+0xc0); the tag goes to the call of the checked memmove with a0 = f + 12,
     a1 = f + 16, a2 = n - 16 (+0xb0).
   - rcu_seg_mm_ret: from the memmove's return address 0x81494: s0 = n - 4, the call of reac_frame_is_reac with
     a0 = f, a1 = n - 4.
   - rcu_seg_leaf_ret: from the leaf's return address 0x814a4: `beqz a0` returns 0; else f[16] (+0xdc) and f[17]
     (+0xf8), each after its instrumented check, decide the result s0 or 0; the epilogue.
   Each instrumented check loads the shadow byte k at (a >> 3) + s2 and continues when k = 0 or (a mod 8) < k; the
   branch to the error path (`jal` 0x580bc at +0x128, +0x134, +0x144, +0x150, +0x160, +0x170) needs k <> 0 and
   (a mod 8) >= k, which the shadow premise refutes, so no error path is reached. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.

(* ---- tactics: the template's, read at evtF ---- *)

Ltac rcu_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac rcu_w := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac shn := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; zb_fold_lits.
Ltac norm := wsub; do 3 (shn; usub).
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu, zxb; rewrite ?zb_signed; norm;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
(* a register's value from its defining step: an assumption, arithmetic, or a literal in range *)
Ltac rcu_u := first [ assumption | lia | (rewrite unsigned_lit by lia; lia) ].

(* ---- the epilogue ---- *)

(* +0x104 (0x814e4): a0 = s0, ra s0 s1 s2 loaded back from the frame, sp += 0x20, ret *)
Lemma rcu_epi : forall (RNG : ExecF.footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  32 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -32) 32 ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x8 x11 x12 x13 x14 x15 x16 x17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x814e4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 FR HSP RFR.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 7 step.
  apply evtF_done. f_equal; rcu_regs; rcu_w.
Qed.

(* entry 0x813e0, n < 50: the prologue, `bltu` at +0x1c taken, +0x100 `li s0, 0`, the epilogue *)
Lemma rcu_seg_small : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -32) 32 ->
  bv_unsigned a1 < 50 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 50) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x813e0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo ST LO RFR HN.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  carve_frame 32%nat ST.
  do 8 step.
  takeF true.
  step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [eapply (rcu_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm) |] end.
  all: cycle -1.
  { intros ms' ->. apply evtF_done.
    match goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity | exact MU]. }
  all: first [ eassumption | lia ].
Qed.

(* bytes_at read as one load of all its bytes *)
Lemma rcu_rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* entry 0x813e0, n >= 50: the prologue, `bltu` at +0x1c not taken, +0x20 s1 = f, +0x24 .. +0x2c the GOT word
   0x987e8 and through it the shadow base at 0xa0778 into s2, up to +0x30 (0x81410) *)
Lemma rcu_seg_pro : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
  CELL_K + 8 <= bv_unsigned sp + -32 ->
  ExecF.rng RNG (bv_unsigned sp + -32) 32 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  50 <= bv_unsigned a1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1 (w10 : word),
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a0 w10 (Z_to_bv 64 50) a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 ASAN_K) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x81410) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\
       rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x813e0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo ST LO GCK CK DC RFR RGC RCK HN.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  unfold CELL_K, GOT_CELL_K, ASAN_K in GCK, CK, DC, RGC, RCK.
  carve_frame 32%nat ST.
  do 8 step.
  takeF false.
  do 2 step.
  pose proof (rcu_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rcu_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 2 step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  eexists. split; [|split; [exact MU | eassumption]].
  unfold ASAN_K. f_equal; rcu_regs; rcu_w.
Qed.

(* ---- the instrumented checks and the tests that read the frame f ---- *)

Section Chk.
Variables (x1 x2 gp tp x5 x6 x7 x8 x9 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (LO HI : Z) (RNG : ExecF.footprint).
Hypothesis HLO0 : 0 <= LO.
Hypothesis HHI : HI <= 2 ^ 63.
(* the frame [LO, HI): each byte's shadow byte, read at (x >> 3) + the shadow base, lets the byte be loaded *)
Hypothesis SHD : forall x, LO <= x < HI ->
  exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k).
Hypothesis RDB : forall x, LO <= x < HI -> ExecF.rng RNG x 1.
Hypothesis RSH : forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1.
Variable Q : machine_state -> Prop.

Local Abbreviation ST pc x10 x11 x12 x13 x14 :=
  (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880)
           s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* The six checks. Each loads the shadow byte k of the address A (`srli; add s2; lb`), skips the slow path when
   k = 0 (`bnez`), else compares A & 7 with k (`andi; blt`); the branch to the error path is the `blt` not taken,
   which needs k <> 0 and A mod 8 >= k, which SHD refutes. *)

(* +0x34 (address in a0, shadow byte in a1, offset in a2) -> +0x44; error path at +0x128 *)
Lemma rcu_c12 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (ST 0x81424 x10 y11 y12 x13 x14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x81414 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x10) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0x54 (address in a1, shadow byte in a2, offset in a3) -> +0x64; error path at +0x144 *)
Lemma rcu_c13 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x11 = A -> LO <= A < HI ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (ST 0x81444 x10 x11 y12 y13 x14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x81434 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x11) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0x70 (address in a1, shadow byte in a2, offset in a3) -> +0x80; error path at +0x160 *)
Lemma rcu_c16 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x11 = A -> LO <= A < HI ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (ST 0x81460 x10 x11 y12 y13 x14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x81450 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x11) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0x90 (address in a2, shadow byte in a3, offset in a4) -> +0xa0; error path at +0x170 *)
Lemma rcu_c17 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x12 = A -> LO <= A < HI ->
  (forall y13 y14 : word, ExecF.evtF rsegs RNG Q (ST 0x81480 x10 x11 x12 y13 y14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x81470 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x12) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x12 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0xcc (address in a0, shadow byte in a1, offset in a2) -> +0xdc; error path at +0x134 *)
Lemma rcu_a16 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (ST 0x814bc x10 y11 y12 x13 x14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x814ac x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x10) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0xe8 (address in a0, shadow byte in a1, offset in a2) -> +0xf8; error path at +0x150 *)
Lemma rcu_a17 : forall (x10 x11 x12 x13 x14 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (ST 0x814d8 x10 y11 y12 x13 x14)) ->
  ExecF.evtF rsegs RNG Q (ST 0x814c8 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x10) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* +0x30 .. +0xb0: the tag test (f in s1, n in s0) over the bytes b12 b13 b16 b17 of f; a mismatch goes to +0xb8
   and calls reac_frame_is_reac (f, n), the tag calls the checked memmove (f + 12, f + 16, n - 16) *)
Lemma rcu_tag : forall (x10 x11 x12 x13 x14 : word) (f n : Z) (bs : list byte),
  bv_unsigned x9 = f -> bv_unsigned x8 = n -> 50 <= n <= 1600 ->
  LO <= f + 12 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 12)) = Some (nth 12 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 13)) = Some (nth 13 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 16)) = Some (nth 16 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 17)) = Some (nth 17 bs (Z_to_bv 8 0)) ->
  (PRc.cu_tagged bs = true -> forall y10 y11 y12 y13 y14 : word,
     bv_unsigned y10 = f + 12 -> bv_unsigned y11 = f + 16 -> bv_unsigned y12 = n - 16 ->
     Q (MS (mkR (Z_to_bv 64 0x81494) x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17
                (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (Z_to_bv 64 0x51310) fc None m (seg_rom rsegs))) ->
  (PRc.cu_tagged bs = false -> forall y10 y11 y12 y13 y14 : word,
     bv_unsigned y10 = f -> bv_unsigned y11 = n ->
     Q (MS (mkR (Z_to_bv 64 0x814a4) x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17
                (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (Z_to_bv 64 0x817bc) fc None m (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (ST 0x81410 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 f n bs H9 H8 Hn HL HH M12 M13 M16 M17 KT KN.
  pose proof (u64_range x9) as R9. pose proof (u64_range x8) as R8.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  pose proof (byte_range b12) as B12. pose proof (byte_range b13) as B13.
  pose proof (byte_range b16) as B16. pose proof (byte_range b17) as B17.
  assert (TG : PRc.cu_tagged bs =
    ((bv_unsigned b12 =? 0x81) && (bv_unsigned b13 =? 0) && (bv_unsigned b16 =? 0x88) && (bv_unsigned b17 =? 0x19))%bool)
    by (unfold PRc.cu_tagged, PRc.cu_byte; rewrite <- E12, <- E13, <- E16, <- E17; reflexivity).
  (* the mismatch exit: +0xb8 a0 = f, a1 = n, the call of reac_frame_is_reac *)
  assert (KM : forall y10 y11 y12 y13 y14 : word, PRc.cu_tagged bs = false ->
                 ExecF.evtF rsegs RNG Q (ST 0x81498 y10 y11 y12 y13 y14)).
  { intros y10 y11 y12 y13 y14 NT. do 3 step.
    apply evtF_done. apply (KN NT); rcu_u. }
  step. gen_addi x9 w12 U12.
  apply (rcu_c12 _ _ _ _ _ (f + 12)); [lia | lia |]. intros y11 y12.
  pose proof (rdw0 m w12 _ _ M12 ltac:(lia)) as R. pose proof (RDB (f + 12) ltac:(lia)) as RB.
  step. clear R. step. step.
  destruct (Z.eq_dec (bv_unsigned b12) 0x81) as [E81|N81].
  2: { takeF true. apply KM. rewrite TG, (proj2 (Z.eqb_neq _ _) N81). reflexivity. }
  takeF false.
  step. gen_addi x9 w13 U13.
  apply (rcu_c13 _ _ _ _ _ (f + 13)); [lia | lia |]. intros y12' y13.
  pose proof (rdw0 m w13 _ _ M13 ltac:(lia)) as R. pose proof (RDB (f + 13) ltac:(lia)) as RB'.
  step. clear R. step.
  destruct (Z.eq_dec (bv_unsigned b13) 0) as [E00|N00].
  2: { takeF true. apply KM. rewrite TG, (proj2 (Z.eqb_eq _ _) E81), (proj2 (Z.eqb_neq _ _) N00). reflexivity. }
  takeF false.
  step. gen_addi x9 w16 U16.
  apply (rcu_c16 _ _ _ _ _ (f + 16)); [lia | lia |]. intros y12'' y13'.
  pose proof (rdw0 m w16 _ _ M16 ltac:(lia)) as R. pose proof (RDB (f + 16) ltac:(lia)) as RB''.
  step. clear R. step. step.
  destruct (Z.eq_dec (bv_unsigned b16) 0x88) as [E88|N88].
  2: { takeF true. apply KM.
       rewrite TG, (proj2 (Z.eqb_eq _ _) E81), (proj2 (Z.eqb_eq _ _) E00), (proj2 (Z.eqb_neq _ _) N88). reflexivity. }
  takeF false.
  step. gen_addi x9 w17 U17.
  apply (rcu_c17 _ _ _ _ _ (f + 17)); [lia | lia |]. intros y13'' y14.
  pose proof (rdw0 m w17 _ _ M17 ltac:(lia)) as R. pose proof (RDB (f + 17) ltac:(lia)) as RB'''.
  step. clear R. step. step.
  destruct (Z.eq_dec (bv_unsigned b17) 0x19) as [E19|N19].
  2: { takeF true. apply KM.
       rewrite TG, (proj2 (Z.eqb_eq _ _) E81), (proj2 (Z.eqb_eq _ _) E00), (proj2 (Z.eqb_eq _ _) E88),
         (proj2 (Z.eqb_neq _ _) N19). reflexivity. }
  takeF false.
  assert (T : PRc.cu_tagged bs = true)
    by (rewrite TG, (proj2 (Z.eqb_eq _ _) E81), (proj2 (Z.eqb_eq _ _) E00), (proj2 (Z.eqb_eq _ _) E88),
          (proj2 (Z.eqb_eq _ _) E19); reflexivity).
  step. step.
  apply evtF_done. apply (KT T); rcu_u.
Qed.

(* +0xc4 .. +0x100 (0x814a4 .. 0x814e0), after reac_frame_is_reac returned r in a0: r = 0 returns 0; else the
   bytes b16, b17 at f + 16, f + 17 (+0xdc, +0xf8), each after its check: both 0 return s0 (L), else 0 *)
Definition KR (x13 x14 : word) (R : Z) : Prop := forall y8 y10 y11 y12 : word, bv_unsigned y8 = R ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 y8 x9 y10 y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880)
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x814e4) fc None m (seg_rom rsegs)).

Lemma rcu_leaf_ret : forall (x10 x11 x12 x13 x14 : word) (f r L : Z) (b16 b17 : byte),
  bv_unsigned x9 = f -> bv_unsigned x8 = L -> bv_unsigned x10 = r -> (r = 0 \/ r = 1) ->
  LO <= f + 16 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 16)) = Some b16 -> mrd rsegs m (wa (f + 17)) = Some b17 ->
  KR x13 x14 (if r =? 0 then 0 else if (bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0) then L else 0) ->
  ExecF.evtF rsegs RNG Q (ST 0x814a4 x10 x11 x12 x13 x14).
Proof.
  intros x10 x11 x12 x13 x14 f r L b16 b17 H9 H8 H10 HR HL HH M16 M17 K.
  pose proof (u64_range x9) as R9. pose proof (u64_range x8) as R8.
  pose proof (byte_range b16) as B16. pose proof (byte_range b17) as B17.
  step.
  destruct HR as [Er | Er]; rewrite Er in H10, K.
  - takeF true. step. apply K. rewrite unsigned_lit by lia. reflexivity.
  - takeF false.
    step. gen_addi x9 w16 U16.
    apply (rcu_a16 _ _ _ _ _ (f + 16)); [lia | lia |]. intros y11 y12.
    pose proof (rdw0 m w16 _ _ M16 ltac:(lia)) as R. pose proof (RDB (f + 16) ltac:(lia)) as RB.
    step. clear R. step.
    destruct (Z.eq_dec (bv_unsigned b16) 0) as [Z16|N16].
    2: { takeF true. step. apply K. rewrite unsigned_lit by lia.
         rewrite (proj2 (Z.eqb_neq (bv_unsigned b16) 0) N16). reflexivity. }
    takeF false.
    step. gen_addi x9 w17 U17.
    apply (rcu_a17 _ _ _ _ _ (f + 17)); [lia | lia |]. intros y11' y12'.
    pose proof (rdw0 m w17 _ _ M17 ltac:(lia)) as R. pose proof (RDB (f + 17) ltac:(lia)) as RB'.
    step. clear R. step.
    destruct (Z.eq_dec (bv_unsigned b17) 0) as [Z17|N17].
    + takeF true. apply K.
      rewrite (proj2 (Z.eqb_eq (bv_unsigned b16) 0) Z16), (proj2 (Z.eqb_eq (bv_unsigned b17) 0) Z17). exact H8.
    + takeF false. step. apply K. rewrite unsigned_lit by lia.
      rewrite (proj2 (Z.eqb_eq (bv_unsigned b16) 0) Z16), (proj2 (Z.eqb_neq (bv_unsigned b17) 0) N17). reflexivity.
Qed.
End Chk.

(* ---- the runs between the calls, as the walk uses them ---- *)

(* 0x81410 (+0x30) to the next call: the memmove (tag) or reac_frame_is_reac (no tag) *)
Theorem rcu_seg_tag : forall (RNG : ExecF.footprint)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (LO HI f n : Z) (bs : list byte),
  0 <= LO -> HI <= 2 ^ 63 ->
  (forall x, LO <= x < HI ->
     exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG x 1) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1) ->
  bv_unsigned x9 = f -> bv_unsigned x8 = n -> 50 <= n <= 1600 ->
  LO <= f + 12 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 12)) = Some (nth 12 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 13)) = Some (nth 13 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 16)) = Some (nth 16 bs (Z_to_bv 8 0)) ->
  mrd rsegs m (wa (f + 17)) = Some (nth 17 bs (Z_to_bv 8 0)) ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       (PRc.cu_tagged bs = true /\ exists y10 y11 y12 y13 y14 : word,
          bv_unsigned y10 = f + 12 /\ bv_unsigned y11 = f + 16 /\ bv_unsigned y12 = n - 16 /\
          ms' = MS (mkR (Z_to_bv 64 0x81494) x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17
                        (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x51310) fc None m (seg_rom rsegs)) \/
       (PRc.cu_tagged bs = false /\ exists y10 y11 y12 y13 y14 : word,
          bv_unsigned y10 = f /\ bv_unsigned y11 = n /\
          ms' = MS (mkR (Z_to_bv 64 0x814a4) x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17
                        (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x817bc) fc None m (seg_rom rsegs)))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880)
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x81410) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    F fc m LO HI f n bs H0 HH SHD RDB RSH H9 H8 Hn HL HU M12 M13 M16 M17.
  eapply rcu_tag with (LO := LO) (HI := HI) (f := f) (n := n) (bs := bs); try eassumption.
  - intros T y10 y11 y12 y13 y14 E10 E11 E12. left. split; [exact T|].
    exists y10, y11, y12, y13, y14. repeat split; assumption.
  - intros T y10 y11 y12 y13 y14 E10 E11. right. split; [exact T|].
    exists y10, y11, y12, y13, y14. repeat split; assumption.
Qed.

(* 0x81494 (+0xb4), the memmove's return address: s0 = n - 4, a0 = f, a1 = n - 4, the call of reac_frame_is_reac *)
Theorem rcu_seg_mm_ret : forall (RNG : ExecF.footprint)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  bv_unsigned x8 = n -> 50 <= n <= 1600 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y8 y10 y11 : word,
       bv_unsigned y8 = n - 4 /\ y10 = x9 /\ bv_unsigned y11 = n - 4 /\
       ms' = MS (mkR (Z_to_bv 64 0x814a4) x2 gp tp x5 x6 x7 y8 x9 y10 y11 x12 x13 x14 x15 x16 x17
                     x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x817bc) fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x81494) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x28 x29 x30 x31 F fc m n H8 Hn.
  pose proof (u64_range x8) as R8.
  do 4 step.
  apply evtF_done. do 3 eexists. split; [|split; [|split; [|reflexivity]]].
  all: first [ reflexivity | (rewrite ?unsigned_lit by lia; lia) ].
Qed.

(* 0x814a4 (+0xc4), reac_frame_is_reac's return address, to the return *)
Theorem rcu_seg_leaf_ret : forall (RNG : ExecF.footprint)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (ra sp c0 c1 c2 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (LO HI f r L : Z) (b16 b17 : byte),
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 c2; C8 c1; C8 c0; C8 ra] ->
  32 <= bv_unsigned sp -> ExecF.rng RNG (bv_unsigned sp + -32) 32 ->
  0 <= LO -> HI <= 2 ^ 63 ->
  (forall x, LO <= x < HI ->
     exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG x 1) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1) ->
  bv_unsigned x9 = f -> bv_unsigned x8 = L -> bv_unsigned x10 = r -> (r = 0 \/ r = 1) ->
  LO <= f + 16 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 16)) = Some b16 -> mrd rsegs m (wa (f + 17)) = Some b17 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y10 y11 y12 : word,
       bv_unsigned y10 = (if r =? 0 then 0 else if (bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0) then L else 0) /\
       ms' = MS (mkR ra sp gp tp x5 x6 x7 c0 c1 y10 y11 y12 x13 x14 x15 x16 x17
                     c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    ra sp c0 c1 c2 F fc m LO HI f r L b16 b17 FR HSP RFR H0 HH SHD RDB RSH H9 H8 H10 HR HL HU M16 M17.
  eapply rcu_leaf_ret with (LO := LO) (HI := HI) (f := f) (r := r) (L := L) (b16 := b16) (b17 := b17);
    try eassumption.
  unfold KR. intros y8 y10 y11 y12 Hy8.
  eapply evtF_mono; [eapply (rcu_epi RNG ra sp gp tp c0 c1 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m); eassumption |].
  intros ms' ->. exists y8, y11, y12. split; [exact Hy8 | reflexivity].
Qed.
