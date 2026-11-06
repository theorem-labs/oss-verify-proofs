(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: adapted from reac-repacer/fuzz_uci's lib/A/Prog/rp_uci_int_cgW_runs.v for reac-repacer/fuzz_wire's rp_copy_untag in image A: its tactics (rui_ -> rcu_) and its form of the instrumented-check lemmas copied; the runs written for this function. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/rp_copy_untag_cgW_runs.v, with its module paths, addresses and numbers changed; 107 of its 309 lines of code are new or changed and 249 lines of the source are left out. *)
(* rp_copy_untag_cgW_runs: the footprint runs (lib/Lib/ExecF.v evtF) of rp_copy_untag in image B
   (fuzz_wire.asan-ubsan 0x81414, 66 instruction words, every one reached is stepped), in the form of
   reac-repacer/fuzz_uci's lib/B/Prog/rp_uci_int_cgW_runs.v and of this unit's image-A twin
   lib/A/Prog/rp_copy_untag_cgW_runs.v. lib/B/Prog/rp_copy_untag_cgW.v carries the runs into the cgif walk and cuts
   the three calls between them (is_tagged_reac 0x8103c, the checked memmove 0x510b0 and reac_frame_is_reac 0x8183c)
   by the statement's premises.
   - rcu_seg_small: the prologue (frame 0x30; ra s0 s1 s2 s3 stored at sp + 40 .. sp + 8), `bltu` at +0x20 taken
     (n < 50), +0xc4 `li s0, 0` and the epilogue: return 0.
   - rcu_seg_call_tag: the prologue, `bltu` not taken, s1 = f (+0x24), the shadow base read through its GOT word
     0x98878 into s3 (+0x28 .. +0x30), a0 = f, the call of is_tagged_reac at +0x38 (return address 0x81450).
   - rcu_seg_tag_ret: from 0x81450: s2 = f + 16; `beqz a0` on the leaf's result: 0 goes to +0x6c and the call of
     reac_frame_is_reac with a0 = f, a1 = n; else the UBSan checks of f (+0x48, +0x4c, +0x54; `unimp` at +0xe8,
     refuted by 0 < f and f + 18 <= 2 ^ 63) and the call of the checked memmove with a0 = f + 12, a1 = f + 16,
     a2 = n - 16 (+0x64, return address 0x8147c).
   - rcu_seg_mm_ret: from the memmove's return address 0x8147c: s0 = n - 4, the call of reac_frame_is_reac with
     a0 = f, a1 = n - 4 (return address 0x8148c).
   - rcu_seg_leaf_ret: from the leaf's return address 0x8148c: `beqz a0` returns 0; else the UBSan checks of f
     (+0x7c, +0x84, +0xa4) and f[16] (+0x98) and f[17] (+0xbc), each after the instrumented check of its shadow
     byte, decide the result s0 or 0; the epilogue.
   Each instrumented check loads the shadow byte k at (a >> 3) + s3 and continues when k = 0 or (a mod 8) < k; the
   branch to the error path (`jal` 0x57e5c at +0xf8 and +0x104) needs k <> 0 and (a mod 8) >= k, which the shadow
   premise refutes, so no error path is reached. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

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

(* bytes_at read as one load of all its bytes *)
Lemma rcu_rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* ---- the epilogue ---- *)

(* +0xc8 (0x814dc): a0 = s0, ra s0 s1 s2 s3 loaded back from the frame, sp += 0x30, ret *)
Lemma rcu_epi : forall (RNG : ExecF.footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (junk : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  48 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x8 x11 x12 x13 x14 x15 x16 x17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x814dc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m junk
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 FR HSP RFR.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 8 step.
  apply evtF_done. f_equal; rcu_regs; rcu_w.
Qed.

(* ---- the two runs from the entry ---- *)

(* entry 0x81414, n < 50: the prologue, `bltu` at +0x20 taken, +0xc4 `li s0, 0`, the epilogue *)
Lemma rcu_seg_small : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  bv_unsigned a1 < 50 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 50) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo ST LO RFR HN.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  carve_frame 48%nat ST.
  do 9 step.
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

(* entry 0x81414, n >= 50: the prologue, `bltu` at +0x20 not taken, +0x24 s1 = f, +0x28 .. +0x30 the GOT word
   0x98878 and through it the shadow base at 0xa07f8 into s3, +0x34 a0 = f, +0x38 the call of is_tagged_reac
   (0x8103c), return address 0x81450 *)
Lemma rcu_seg_call_tag : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f n : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
  CELL_K + 8 <= bv_unsigned sp + -48 ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  bv_unsigned a0 = f -> bv_unsigned a1 = n -> 50 <= n <= 1600 -> 0 < f ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1 (junk : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x81450) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                     a1 a0 a0 (Z_to_bv 64 50) a2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x8103c) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\
       rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo f n ST LO GCK CK DC RFR RGC RCK Ha0 Ha1 Hn Hf.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  unfold CELL_K, GOT_CELL_K, ASAN_K in GCK, CK, DC, RGC, RCK.
  carve_frame 48%nat ST.
  do 9 step.
  takeF false.
  do 2 step.
  pose proof (rcu_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rcu_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 4 step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  eexists. split; [|split; [exact MU | eassumption]].
  unfold ASAN_K. f_equal; rcu_regs; rcu_w.
Qed.

(* ---- the instrumented checks and the tests of f[16], f[17] after the leaf returns ---- *)

Section Chk.
Variables (x1 x2 gp tp x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (LO HI : Z) (RNG : ExecF.footprint).
Hypothesis HLO0 : 0 <= LO.
Hypothesis HHI : HI <= 2 ^ 63.
(* the frame [LO, HI): each byte's shadow byte, read at (x >> 3) + the shadow base, lets the byte be loaded *)
Hypothesis SHD : forall x, LO <= x < HI ->
  exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k).
Hypothesis RDB : forall x, LO <= x < HI -> ExecF.rng RNG x 1.
Hypothesis RSH : forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1.
Variable Q : machine_state -> Prop.

(* the state of this stretch: s2 (x18) is f + 16, s3 (x19) the shadow base, s0 (x8) the result length, s1 (x9) f *)
Local Abbreviation ST pc x10 x11 x12 :=
  (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
           s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* +0x88 (address in s2, shadow byte in a0, offset in a1) -> +0x98; error path at +0xf8 *)
Lemma rcu_c16 : forall (x10 x11 x12 : word) (A : Z),
  bv_unsigned x18 = A -> LO <= A < HI ->
  (forall y10 y11 : word, ExecF.evtF rsegs RNG Q (ST 0x814ac y10 y11 x12)) ->
  ExecF.evtF rsegs RNG Q (ST 0x8149c x10 x11 x12).
Proof.
  intros x10 x11 x12 A EA RA CONT.
  destruct (SHD A RA) as (k & M & SK). pose proof (RSH A RA) as RK.
  pose proof (u64_range x18) as RS. unfold ASAN_K in M, RK.
  step. gen_shr x18 g G. rewrite EA in G.
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

(* +0xac (address in a0, shadow byte in a1, offset in a2) -> +0xbc; error path at +0x104 *)
Lemma rcu_c17 : forall (x10 x11 x12 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (ST 0x814d0 x10 y11 y12)) ->
  ExecF.evtF rsegs RNG Q (ST 0x814c0 x10 x11 x12).
Proof.
  intros x10 x11 x12 A EA RA CONT.
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

(* the epilogue's entry +0xc8 with s0 = R *)
Definition KR (R : Z) : Prop := forall y8 y10 y11 y12 : word, bv_unsigned y8 = R ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 y8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880)
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x814dc) fc None m (seg_rom rsegs)).

(* +0x78 .. +0xc8 (0x8148c .. 0x814dc), after reac_frame_is_reac returned r in a0: r = 0 returns 0; else the
   bytes b16, b17 at f + 16, f + 17 (+0x98, +0xbc), each after its check: both 0 return s0 (L), else 0.
   The UBSan checks of f at +0x7c, +0x84 and +0xa4 (`unimp` at +0xe8) are refuted by 0 < f and f + 18 <= 2 ^ 63. *)
Lemma rcu_leaf_ret : forall (x10 x11 x12 : word) (f r L : Z) (b16 b17 : byte),
  bv_unsigned x9 = f -> bv_unsigned x8 = L -> bv_unsigned x10 = r -> (r = 0 \/ r = 1) ->
  bv_unsigned x18 = f + 16 -> 0 < f -> LO <= f + 16 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 16)) = Some b16 -> mrd rsegs m (wa (f + 17)) = Some b17 ->
  KR (if r =? 0 then 0 else if (bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0) then L else 0) ->
  ExecF.evtF rsegs RNG Q (ST 0x8148c x10 x11 x12).
Proof.
  intros x10 x11 x12 f r L b16 b17 H9 H8 H10 HR H18 Hf HL HH M16 M17 K.
  pose proof (u64_range x9) as R9. pose proof (u64_range x8) as R8. pose proof (u64_range x18) as R18.
  pose proof (byte_range b16) as B16. pose proof (byte_range b17) as B17.
  step.
  destruct HR as [Er | Er]; rewrite Er in H10, K.
  - takeF true. step. apply K. rewrite unsigned_lit by lia. reflexivity.
  - takeF false.
    (* the UBSan checks of f at +0x7c and +0x84 (`unimp` at +0xe8) *)
    step. if_false. step. step. if_false.
    (* the instrumented check of f + 16, then `lbu a0, 0(s2)` *)
    apply (rcu_c16 _ _ _ (f + 16)); [lia | lia |]. intros y10 y11.
    pose proof (rdw0 m x18 _ _ M16 ltac:(lia)) as R. pose proof (RDB (f + 16) ltac:(lia)) as RB.
    step. clear R. step.
    destruct (Z.eq_dec (bv_unsigned b16) 0) as [Z16|N16].
    2: { takeF true. step. apply K. rewrite unsigned_lit by lia.
         rewrite (proj2 (Z.eqb_neq (bv_unsigned b16) 0) N16). reflexivity. }
    takeF false.
    (* the UBSan check of f at +0xa4, then a0 = f + 17 and its instrumented check *)
    step. step. if_false.
    step. gen_addi x9 w17 U17.
    apply (rcu_c17 _ _ _ (f + 17)); [lia | lia |]. intros y11' y12'.
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

(* 0x81450 (+0x3c), is_tagged_reac's return address: s2 = f + 16; the leaf's result r decides the next call *)
Theorem rcu_seg_tag_ret : forall (RNG : ExecF.footprint)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11
     x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n r : Z),
  bv_unsigned x9 = f -> bv_unsigned x8 = n -> bv_unsigned x10 = r -> (r = 0 \/ r = 1) ->
  50 <= n <= 1600 -> 0 < f -> f + 18 <= 2 ^ 63 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (y18 : word), bv_unsigned y18 = f + 16 /\
       ((r <> 0 /\ exists y10 y11 y12 : word,
           bv_unsigned y10 = f + 12 /\ bv_unsigned y11 = f + 16 /\ bv_unsigned y12 = n - 16 /\
           ms' = MS (mkR (Z_to_bv 64 0x8147c) x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17
                         y18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x510b0) fc None m (seg_rom rsegs)) \/
        (r = 0 /\ exists y10 y11 : word,
           bv_unsigned y10 = f /\ bv_unsigned y11 = n /\
           ms' = MS (mkR (Z_to_bv 64 0x8148c) x2 gp tp x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17
                         y18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8183c) fc None m (seg_rom rsegs))))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x81450) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11
    x28 x29 x30 x31 F fc m f n r H9 H8 H10 HR Hn Hf Hfn.
  pose proof (u64_range x9) as R9. pose proof (u64_range x8) as R8.
  step. gen_addi x9 w18 U18. step.
  destruct HR as [Er | Er]; rewrite Er in H10.
  - (* not tagged: +0x6c a0 = f, a1 = n, the call of reac_frame_is_reac *)
    takeF true. do 3 step.
    apply evtF_done. exists w18. split; [lia|]. right. split; [exact Er|].
    do 2 eexists. split; [|split; [|reflexivity]]. all: rcu_u.
  - (* tagged: the UBSan checks of f, then a0 = f + 12, a2 = n - 16, a1 = s2, the call of the memmove *)
    takeF false.
    step. step. if_false. step. if_false. step. step. if_false.
    do 4 step.
    apply evtF_done. exists w18. split; [lia|]. left. split; [lia|].
    do 3 eexists. split; [|split; [|split; [|reflexivity]]]. all: rcu_u.
Qed.

(* 0x8147c (+0x68), the memmove's return address: s0 = n - 4, a0 = f, a1 = n - 4, the call of reac_frame_is_reac *)
Theorem rcu_seg_mm_ret : forall (RNG : ExecF.footprint)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11
     x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n : Z),
  bv_unsigned x8 = n -> bv_unsigned x9 = f -> 50 <= n <= 1600 -> 0 < f ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y8 y10 y11 : word,
       bv_unsigned y8 = n - 4 /\ bv_unsigned y10 = f /\ bv_unsigned y11 = n - 4 /\
       ms' = MS (mkR (Z_to_bv 64 0x8148c) x2 gp tp x5 x6 x7 y8 x9 y10 y11 x12 x13 x14 x15 x16 x17
                     x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x8183c) fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8147c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11
    x28 x29 x30 x31 F fc m f n H8 H9 Hn Hf.
  pose proof (u64_range x8) as R8. pose proof (u64_range x9) as R9.
  do 4 step.
  apply evtF_done. do 3 eexists. split; [|split; [|split; [|reflexivity]]].
  all: first [ reflexivity | (rewrite ?unsigned_lit by lia; lia) ].
Qed.

(* 0x8148c (+0x78), reac_frame_is_reac's return address, to the return *)
Theorem rcu_seg_leaf_ret : forall (RNG : ExecF.footprint)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s4 s5 s6 s7 s8 s9 s10 s11
     x28 x29 x30 x31 : word)
    (ra sp c0 c1 c2 c3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte)
    (LO HI f r L : Z) (b16 b17 : byte),
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 c3; C8 c2; C8 c1; C8 c0; C8 ra] ->
  48 <= bv_unsigned sp -> ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  0 <= LO -> HI <= 2 ^ 63 ->
  (forall x, LO <= x < HI ->
     exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG x 1) ->
  (forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1) ->
  bv_unsigned x9 = f -> bv_unsigned x8 = L -> bv_unsigned x10 = r -> (r = 0 \/ r = 1) ->
  bv_unsigned x18 = f + 16 -> 0 < f -> LO <= f + 16 -> f + 18 <= HI ->
  mrd rsegs m (wa (f + 16)) = Some b16 -> mrd rsegs m (wa (f + 17)) = Some b17 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y10 y11 y12 : word,
       bv_unsigned y10 = (if r =? 0 then 0 else if (bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0) then L else 0) /\
       ms' = MS (mkR ra sp gp tp x5 x6 x7 c0 c1 y10 y11 y12 x13 x14 x15 x16 x17
                     c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8148c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s4 s5 s6 s7 s8 s9 s10 s11
    x28 x29 x30 x31 ra sp c0 c1 c2 c3 F fc m junk LO HI f r L b16 b17
    FR HSP RFR H0 HH SHD RDB RSH H9 H8 H10 HR H18 Hf HL HU M16 M17.
  eapply rcu_leaf_ret with (LO := LO) (HI := HI) (f := f) (r := r) (L := L) (b16 := b16) (b17 := b17);
    try eassumption.
  unfold KR. intros y8 y10 y11 y12 Hy8.
  eapply evtF_mono;
    [eapply (rcu_epi RNG ra sp gp tp c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m junk); eassumption |].
  intros ms' ->. exists y8, y11, y12. split; [exact Hy8 | reflexivity].
Qed.
