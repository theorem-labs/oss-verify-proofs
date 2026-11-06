(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/rp_uci_int_cgW_runs.v, with its module paths, addresses and numbers changed; 160 of its 568 lines of code are new or changed and 157 lines of the source are left out. *)
(* rp_uci_int_cgW_runs: the footprint runs (lib/Lib/ExecF.v evtF) of rp_uci_int in image B (fuzz_uci.asan-ubsan
   0x7ffd4, 142 instructions, every one stepped), in the segment form of libreac/fuzz_decode's released
   lib/B/Prog/crtB_segs.v and lib/A/Prog/check_braid_F.v (origin/ossv/recipes 88154566652a) and the loop form of this
   unit's plain walk lib/Prog/rp_uci_int.v, whose model lemmas are used as they are. lib/B/Prog/rp_uci_int_cgW.v
   carries the runs into the cgif walk.
   - rui_seg_zero: the prologue (frame 0x30; ra s0 s1 s2 s3 saved at +0x28 .. +0x8), `beqz a1` at 0x7fff0 taken
     (n = 0), the epilogue at 0x801d8: return cur.
   - rui_seg_call: the prologue, `beqz a1` not taken, s2 = r + n, the three UBSan checks of the reply pointer, the
     shadow base loaded through its GOT word (0x8000c-0x80014), the arguments of memchr (r, '\n', n), the call of the
     memchr trampoline 0x4107c at 0x80020.
   - rui_seg_ret: from the return address 0x80024 to the return: the end pointer s2 (memchr's result, or r + n), the
     leading-blank loop, the sign, the digit loop, the trailing-blank loop, the int test, the epilogue.
   Each of the four reply-byte loads (0x80054, 0x800bc, 0x800f8, 0x8017c) is guarded by the ASan check of its shadow
   byte (sc_lead, sc_post, sc_digit, sc_trail). The branch into each __asan_report_load1 call (0x80080, 0x80208,
   0x80138, 0x801ac) is refuted by the shadow byte's value: it is 0, or the byte's offset in its granule is below it
   (the shadow premise of the reply). Each branch to the UBSan `unimp` at 0x801f8 is refuted: r + n wraps (0x80000),
   r = NULL (0x80004) and r + n = NULL (0x80008) by 0 < r and r + n <= 2 ^ 63; the cursor at -1 (0x80098) by the
   cursor lying in the reply; the multiply of the decimal accumulator (0x80110) by its bound 2 ^ 31 at the loop head;
   its negation (0x801c8) by the same bound. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_uci_int_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PRp := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int.

(* ---- tactics: crtA_segs.v's crt_finF, and the plain walk's branch tactics read at evtF ---- *)

Ltac rui_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac rui_w := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].
Ltac rui_finF := apply evtF_done; f_equal; rui_regs; rui_w.

Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac shn := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; zb_fold_lits.
Ltac norm := wsub; do 3 (shn; usub).
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu, zxb; rewrite ?zb_signed; norm;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
Ltac takeF_by b tac := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.
Ltac factF := wsub; usub; first [ reflexivity | lia ].

(* ---- bytes ---- *)

(* bytes_at read as one load of all its bytes *)
Lemma rui_rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* the plain walk's bytes_at_hd / bytes_at_tl / bytes_at_firstn (lib/Prog/rp_uci_int.v), at image B's segments *)
Lemma rui_bytes_hd : forall m P b l, bytes_at rsegs m P (b :: l) -> mrd rsegs m (wa P) = Some b.
Proof. intros m P b l (_ & _ & H). specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. exact H. Qed.

Lemma rui_bytes_tl : forall m P b l, bytes_at rsegs m P (b :: l) -> bytes_at rsegs m (P + 1) l.
Proof.
  intros m P b l H. apply (proj1 (bytes_at_app rsegs m P [b] l)) in H. destruct H as [_ H]. exact H.
Qed.

Lemma rui_bytes_firstn : forall m P bs k, bytes_at rsegs m P bs -> bytes_at rsegs m P (firstn k bs).
Proof.
  intros m P bs k H. rewrite <- (firstn_skipn k bs) in H.
  apply (proj1 (bytes_at_app rsegs m P _ _)) in H. destruct H as [H _]. exact H.
Qed.

(* ---- the prologue and the epilogue ---- *)

(* 0x801d8: a0 = (int) s0, ra s0 s1 s2 s3 loaded back from the frame, sp += 0x30, ret *)
Lemma rui_epi : forall (RNG : ExecF.footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (junk : list byte) (R : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  48 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  INT_MIN <= R <= INT_MAX ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 R) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x801d8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m junk R
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 FR HSP RFR HR.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. rewrite (PRp.swrap_int R HR).
  do 7 step.
  rui_finF.
Qed.

(* 0x7ffd4, n = 0: the prologue, `beqz a1` taken, the epilogue *)
Lemma rui_seg_zero : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  bv_unsigned a1 = 0 -> INT_MIN <= cur <= INT_MAX ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cur) a1 (Z_to_bv 64 cur) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 cur) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7ffd4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    cur lo ST LO RFR HN HC.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  carve_frame 48%nat ST.
  do 8 step.
  takeF true.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut; [eapply (rui_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm) |] end.
  all: cycle -1.
  { intros ms' ->. apply evtF_done.
    match goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity | exact MU]. }
  all: first [ eassumption | lia ].
Qed.

(* 0x7ffd4, n <> 0: the prologue, `beqz a1` not taken, s2 = r + n, the UBSan checks at 0x80000 (r + n wraps),
   0x80004 (r = NULL) and 0x80008 (r + n = NULL), the shadow base, memchr's arguments, the call at 0x80020 *)
Lemma rui_seg_call : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r n : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
  CELL_K + 8 <= bv_unsigned sp + -48 ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  bv_unsigned a0 = r -> bv_unsigned a1 = n -> 0 < r -> 0 < n -> r + n <= 2 ^ 63 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists m1 (junk : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x80024) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                     a2 a0 a0 (Z_to_bv 64 10) a1 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (r + n)) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x4107c) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\
       rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7ffd4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r n ST LO GCK CK DC RFR RGC RCK Ha0 Ha1 Hr Hn Hrn.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  unfold CELL_K, GOT_CELL_K, ASAN_K in GCK, CK, DC, RGC, RCK.
  carve_frame 48%nat ST.
  do 8 step.
  takeF false.
  do 4 step. takeF false.
  step. takeF false.
  step. takeF false.
  pose proof (rui_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rui_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 6 step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  eexists. split; [|split; [exact MU | eassumption]].
  unfold ASAN_K. f_equal; rui_regs; rui_w.
Qed.

(* ---- the UBSan conditions ---- *)

(* 0x80104-0x80110 `mulh a7, a2, a4; mul a2, a2, a4; srai t0, a2, 0x3f; bne a7, t0`: the product of the accumulator
   (at most 2 ^ 31) and 10 does not overflow, so the high word is the sign of the low word *)
Lemma rui_mul_ok : forall (a b : word) (v : Z), 0 <= v <= 2 ^ 31 -> bv_unsigned a = v -> bv_unsigned b = 10 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_signed a * bv_signed b) 64))
    (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (bv_unsigned a * bv_unsigned b))) 63)) = true.
Proof.
  intros a b v Hv Ha Hb. rewrite !zb_signed, Ha, Hb.
  rewrite (unsigned_lit (v * 10)) by lia.
  rewrite (proj2 (Z.ltb_lt v (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt 10 (2 ^ 63))) by lia.
  rewrite (proj2 (Z.ltb_lt (v * 10) (2 ^ 63))) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia. reflexivity.
Qed.

(* 0x801bc-0x801c8 `sgtz a0, a2; neg a2, a2; slti a1, a2, 0; bne a0, a1`: the negation of the value (at most
   2 ^ 31) does not overflow, so it is negative exactly when the value is positive *)
Lemma rui_neg_ok : forall v, 0 <= v <= 2 ^ 31 ->
  (bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 v)) =? bv_unsigned (v_slti (Z_to_bv 64 (0 - v)) 0)) = true.
Proof.
  intros v Hv. unfold v_slt, v_slti, c_lts, bv_lts, zsig.
  rewrite !zb_signed, !unsigned_lit_wrap.
  destruct (Z.eq_dec v 0) as [->|Hv0]; [vm_compute; reflexivity|].
  rewrite (Z.mod_small 0 (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  replace ((0 - v) mod 2 ^ 64) with (2 ^ 64 - v) by (Z.div_mod_to_equations; lia).
  destruct (Z.ltb_spec 0 (2 ^ 63)); [|lia]. destruct (Z.ltb_spec v (2 ^ 63)); [|lia].
  destruct (Z.ltb_spec (2 ^ 64 - v) (2 ^ 63)); [lia|]. cbv beta iota.
  destruct (Z.ltb_spec 0 v); [|lia]. destruct (Z.ltb_spec (2 ^ 64 - v - 2 ^ 64) 0); [|lia].
  reflexivity.
Qed.

(* 0x80094-0x80098 `addi a0, zero, -1; beq s1, a0`: the cursor, a byte of the reply, is not the last address *)
Ltac rui_cursor_ok H9 := unfold bv_eqb; rewrite H9; rewrite unsigned_lit_wrap; apply Z.eqb_neq;
  Z.div_mod_to_equations; lia.

(* ---- from the return address 0x80024 to the return ---- *)

Section Ret.
Variables (x1 x2 gp tp x7 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur E LO HI : Z) (aE : word)
  (RNG : ExecF.footprint).
Hypothesis HEw : bv_unsigned aE = E.
Hypothesis HEHI : E <= HI.
Hypothesis HHI : HI <= 2 ^ 63.
Hypothesis HLO0 : 0 <= LO.
(* the reply [LO, HI): each byte's shadow byte, read at (x >> 3) + the shadow base, lets the byte be loaded *)
Hypothesis SHD : forall x, LO <= x < HI ->
  exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k).
Hypothesis RDB : forall x, LO <= x < HI -> ExecF.rng RNG x 1.
Hypothesis RSH : forall x, LO <= x < HI -> ExecF.rng RNG (x / 8 + ASAN_K) 1.
Variable Q : machine_state -> Prop.

(* the parse's state: s2 (x18) is the end pointer aE, s3 (x19) the shadow base *)
Local Abbreviation ST pc x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 :=
  (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 aE (Z_to_bv 64 2147450880)
           s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* The four shadow checks. Each loads the shadow byte k of the address A (`srli; add s3; lb`), skips the check when
   k = 0 (`bnez`), else compares A & 7 with k (`andi; blt`); the branch to the report is the `blt` not taken, which
   needs k <> 0 and A mod 8 >= k, which SHD refutes. *)
Ltac sc_tac A EA RA CONT xa :=
  let k := fresh "k" in let M := fresh "M" in let SK := fresh "SK" in let RK := fresh "RK" in
  let RS := fresh "RS" in let MB := fresh "MB" in let C := fresh "C" in
  let g := fresh "g" in let G := fresh "G" in let h := fresh "h" in let H := fresh "H" in let R := fresh "R" in
  destruct (SHD A RA) as (k & M & SK); pose proof (RSH A RA) as RK;
  pose proof (u64_range xa) as RS; unfold ASAN_K in M, RK;
  step; gen_shr xa g G; rewrite EA in G;
  step; gen_addi g h H;
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R; step; clear R;
  step;
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB;
  destruct SK as [C|C];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply CONT
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    step; step; rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb];
    apply CONT ].

(* 0x80044 (address in a0, shadow byte in a5, offset in a6) -> 0x80054; report at 0x80080 *)
Lemma sc_lead : forall (x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y15 y16 : word, ExecF.evtF rsegs RNG Q (ST 0x80054 x5 x6 x8 x9 x10 x11 x12 x13 x14 y15 y16 x17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x80044 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 A EA RA CONT. sc_tac A EA RA CONT x10.
Qed.

(* 0x800ac (address in s1, shadow byte in a0, offset in a2) -> 0x800bc; report at 0x80208 *)
Lemma sc_post : forall (x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (A : Z),
  bv_unsigned x9 = A -> LO <= A < HI ->
  (forall y10 y12 : word, ExecF.evtF rsegs RNG Q (ST 0x800bc x5 x6 x8 x9 y10 x11 y12 x13 x14 x15 x16 x17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x800ac x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 A EA RA CONT. sc_tac A EA RA CONT x9.
Qed.

(* 0x800e8 (address in a0, shadow byte in a6, offset in a7) -> 0x800f8; report at 0x80138 *)
Lemma sc_digit : forall (x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y16 y17 : word, ExecF.evtF rsegs RNG Q (ST 0x800f8 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 y16 y17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x800e8 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 A EA RA CONT. sc_tac A EA RA CONT x10.
Qed.

(* 0x8016c (address in a0, shadow byte in a7, offset in t0) -> 0x8017c; report at 0x801ac *)
Lemma sc_trail : forall (x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (A : Z),
  bv_unsigned x10 = A -> LO <= A < HI ->
  (forall y5 y17 : word, ExecF.evtF rsegs RNG Q (ST 0x8017c y5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 y17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x8016c x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 A EA RA CONT. sc_tac A EA RA CONT x10.
Qed.

(* The return at 0x801d8 with s0 = R. *)
Definition KR (R : Z) : Prop := forall y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word,
  ExecF.evtF rsegs RNG Q (ST 0x801d8 y5 y6 (Z_to_bv 64 R) y9 y10 y11 y12 y13 y14 y15 y16 y17).

(* 0x8016c: the trailing-blank loop (s1 = p, a0 = p, a3 = the bytes left, a4 = 32, a5 = end, a6 = the blank mask
   0x100002200), by induction on the bytes left; it leaves to fin at the first non-blank or at the end *)
Lemma trail_loop : forall (x8 x11 x12 x14 x15 x16 : word),
  bv_unsigned x14 = 32 -> bv_unsigned x15 = E -> bv_unsigned x16 = 4294976000 ->
  forall k lb P (x5 x6 x9 x10 x13 x17 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P ->
  bv_unsigned x9 = P -> bv_unsigned x10 = P -> bv_unsigned x13 = Z.of_nat (length lb) ->
  (forall lt P' (y5 y6 y9 y10 y13 y17 : word), zbytes lt = skip is_trail_blank (zbytes lb) ->
     P' + Z.of_nat (length lt) = E -> bv_unsigned y9 = P' ->
     ExecF.evtF rsegs RNG Q (ST 0x801b4 y5 y6 x8 y9 y10 x11 x12 y13 x14 x15 x16 y17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x8016c x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x8 x11 x12 x14 x15 x16 H14 H15 H16 k. induction k as [|k IH];
    intros [|b lb] P x5 x6 x9 x10 x13 x17 HL HB HPE HLP H9 H10 H13 K; try discriminate.
  all: pose proof (byte_range b) as Rb.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: cbn [length] in HL, HPE, H13, BB.
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: apply (sc_trail x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 P); [exact H10 | lia |].
  all: intros y5 y17.
  all: pose proof (rdw0 m x9 _ _ (rui_bytes_hd m P b lb HB) H9) as R.
  all: pose proof (RDB P ltac:(lia)) as RB.
  all: step; clear R.
  all: step; destruct (Z.ltb_spec 32 (bv_unsigned b)) as [Hbig|Hsm].
  all: try (takeF true; apply (K (b :: lb) P); [rewrite PRp.zbytes_cons, PRp.skip_stop by (apply PRp.trail_big; lia); reflexivity | exact HPE | exact H9]).
  all: takeF false.
  all: step; step; step.
  all: destruct (is_trail_blank (bv_unsigned b)) eqn:TB.
  2,4: takeF_by true ltac:(rewrite (PRp.mask_cond x16 b H16 Hsm), TB; reflexivity);
       apply (K (b :: lb) P); [rewrite PRp.zbytes_cons, PRp.skip_stop by exact TB; reflexivity | exact HPE | exact H9].
  all: takeF_by false ltac:(rewrite (PRp.mask_cond x16 b H16 Hsm), TB; reflexivity).
  all: step; step; step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    takeF false. step. step.
    apply (K [] E); [rewrite PRp.zbytes_cons, PRp.skip_go by exact TB; reflexivity | cbn; lia | exact H15].
  - takeF true.
    apply (IH lb (P + 1)); [lia | exact (rui_bytes_tl m P b lb HB) | lia | lia | factF | factF | factF |].
    intros lt P' y5' y6' y9 y10 y13 y17' Hz HP' H9'.
    apply (K lt P'); [rewrite PRp.zbytes_cons, PRp.skip_go by exact TB; exact Hz | exact HP' | exact H9'].
Qed.

(* 0x801b4: `p == end`, the sign (a1), the negation of the value (a2) with its UBSan check (0x801c8), the int test,
   s0 := value *)
Lemma fin : forall (neg : bool) (v : Z) (lt : list byte) (P' : Z) (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word),
  P' + Z.of_nat (length lt) = E -> bv_unsigned x9 = P' ->
  bv_unsigned x11 = (if neg then 0 else 1) -> bv_unsigned x12 = v -> 0 <= v <= 2 ^ 31 -> INT_MIN <= cur <= INT_MAX ->
  KR (match zbytes lt with [] => PRp.fin_val neg v cur | _ :: _ => cur end) ->
  ExecF.evtF rsegs RNG Q (ST 0x801b4 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros neg v lt P' x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 HPE H9 H11 H12 Hv HC K. unfold KR in K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  assert (E12 : x12 = Z_to_bv 64 v) by (rewrite <- H12; symmetry; apply Z_to_bv_bv_unsigned). subst x12.
  step. destruct lt as [|b lt].
  2: { cbn [length] in HPE. takeF true. apply K. }
  cbn [length Z.of_nat] in HPE. takeF false. cbn [zbytes map] in K.
  unfold INT_MIN, INT_MAX in HC.
  step. destruct neg.
  - takeF false. step. step. step. step.
    takeF_by false ltac:(unfold bv_eqb; norm; rewrite (rui_neg_ok v Hv); reflexivity).
    step. step.
    takeF_by false ltac:(rewrite PRp.sext_cond by (rewrite (unsigned_lit v) by lia; lia);
      rewrite (unsigned_lit v) by lia; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
    step. rewrite (unsigned_lit v) by lia.
    assert (FV : PRp.fin_val true v cur = 0 - v)
      by (unfold PRp.fin_val, INT_MIN, INT_MAX; rewrite !(proj2 (Z.ltb_ge _ _)) by lia; cbn; lia).
    rewrite FV in K. apply K.
  - takeF true. step. step.
    destruct (Z.leb_spec v (2 ^ 31 - 1)) as [Hin|Hout].
    + takeF_by false ltac:(rewrite PRp.sext_cond by lia; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
      step.
      assert (FV : PRp.fin_val false v cur = v)
        by (unfold PRp.fin_val, INT_MIN, INT_MAX; rewrite !(proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      rewrite FV in K. apply K.
    + takeF_by true ltac:(rewrite PRp.sext_cond by lia; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
      assert (FV : PRp.fin_val false v cur = cur)
        by (unfold PRp.fin_val, INT_MIN, INT_MAX; rewrite (proj2 (Z.ltb_lt (2 ^ 31 - 1) v)) by lia;
            rewrite orb_true_r; reflexivity).
      rewrite FV in K. apply K.
Qed.

(* 0x8014c: after the digits; the trailing-blank loop, then fin *)
Lemma tail : forall (neg : bool) (v : Z) (lb : list byte) (P : Z) (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P -> bv_unsigned x9 = P ->
  bv_unsigned x11 = (if neg then 0 else 1) -> bv_unsigned x12 = v -> 0 <= v <= 2 ^ 31 -> INT_MIN <= cur <= INT_MAX ->
  KR (finish neg v (zbytes lb) cur) ->
  ExecF.evtF rsegs RNG Q (ST 0x8014c x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros neg v lb P x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 HB HPE HLP H9 H11 H12 Hv HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE, BB. takeF true.
    exact (fin neg v [] P x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 ltac:(cbn; lia) H9 H11 H12 Hv HC K).
  - cbn [length] in HPE, BB. takeF false.
    do 7 step.
    eapply (trail_loop (Z_to_bv 64 cur) x11 x12) with (k := length lb) (lb := b :: lb) (P := P).
    1-3: first [ factF | vm_compute; reflexivity ].
    1: reflexivity.
    1: exact HB.
    1: cbn [length]; lia.
    1: exact HLP.
    1: exact H9.
    1: factF.
    1: cbn [length]; factF.
    intros lt P' y5 y6 y9 y10 y13 y17 Hz HP' H9'.
    eapply (fin neg v lt P' y5 y6 y9 y10 x11 x12); [exact HP' | exact H9' | exact H11 | exact H12 | exact Hv | exact HC |].
    unfold finish in K. rewrite <- Hz in K. exact K.
Qed.

(* 0x800e8: the digit loop (s1 = p, a0 = p, a2 = v), v = v * 10 + d with the UBSan check of the multiply (0x80110),
   and the early `return cur` once v > 2^31 *)
Lemma digit_loop : forall (neg : bool) (x11 x13 x14 x15 : word),
  bv_unsigned x11 = (if neg then 0 else 1) -> bv_unsigned x13 = 9 -> bv_unsigned x14 = 10 ->
  bv_unsigned x15 = 2 ^ 31 -> INT_MIN <= cur <= INT_MAX ->
  forall k (lb : list byte) (P v : Z) (x5 x6 x9 x10 x12 x16 x17 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P ->
  bv_unsigned x9 = P -> bv_unsigned x10 = P ->
  bv_unsigned x12 = v -> 0 <= v <= 2 ^ 31 ->
  KR (match digits_rp v (zbytes lb) with None => cur | Some (v', rest) => finish neg v' rest cur end) ->
  ExecF.evtF rsegs RNG Q (ST 0x800e8 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros neg x11 x13 x14 x15 H11 H13 H14 H15 HC k. induction k as [|k IH];
    intros [|b lb] P v x5 x6 x9 x10 x12 x16 x17 HL HB HPE HLP H9 H10 H12 Hv K; try discriminate.
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: cbn [length] in HL, HPE, BB.
  all: pose proof (byte_range b) as Rb.
  all: apply (sc_digit x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17 P); [exact H10 | lia |].
  all: intros y16 y17.
  all: pose proof (rdw0 m x9 _ _ (rui_bytes_hd m P b lb HB) H9) as R.
  all: pose proof (RDB P ltac:(lia)) as RB.
  all: step; clear R.
  all: step. all: step.
  all: destruct (is_digit (bv_unsigned b)) eqn:DG.
  2,4: takeF_by true ltac:(rewrite (PRp.digit_cond x13 b H13), DG; reflexivity);
       rewrite PRp.zbytes_cons, PRp.digits_stop in K by exact DG;
       exact (tail neg v (b :: lb) P x5 x6 x9 x10 x11 x12 x13 x14 x15 _ _ HB HPE HLP H9 H11 H12 Hv HC K).
  all: takeF_by false ltac:(rewrite (PRp.digit_cond x13 b H13), DG; reflexivity).
  all: step; step; step; step.
  all: takeF_by false ltac:(rewrite (rui_mul_ok _ _ v Hv H12 H14); reflexivity).
  all: step; step; step.
  all: assert (DGb : 48 <= bv_unsigned b <= 57)
         by (unfold is_digit in DG; apply andb_true_iff in DG as [D1 D2]; apply Z.leb_le in D1, D2; lia).
  all: unfold zxb; rewrite (unsigned_lit (bv_unsigned b)) by lia; rewrite (PRp.land_digit (bv_unsigned b)) by lia.
  all: rewrite H12, H14.
  all: rewrite PRp.zbytes_cons, PRp.digits_go in K by exact DG.
  all: destruct (Z.ltb_spec (2 ^ 31) (v * 10 + (bv_unsigned b - 48))) as [Hov|Hok].
  1,3: takeF true; unfold KR in K; apply K.
  all: takeF false.
  all: step; step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    cbn [length Z.of_nat] in HPE.
    takeF false. step. step.
    eapply (tail neg (v * 10 + (bv_unsigned b - 48)) [] E _ x6 aE _ x11);
      [exact (bytes_at_nil rsegs m E ltac:(lia)) | cbn; lia | lia | exact HEw | exact H11 | factF | lia | exact HC
      | exact K].
  - takeF true.
    apply (IH lb (P + 1) (v * 10 + (bv_unsigned b - 48)));
      [lia | exact (rui_bytes_tl m P b lb HB) | lia | lia | factF | factF | factF | lia | exact K].
Qed.

(* 0x800a8: past the optional sign; `p == end` or a non-digit returns cur, else the digit loop from v = 0 *)
Lemma post_sign : forall (neg : bool) (lb : list byte) (P : Z) (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P -> bv_unsigned x9 = P ->
  bv_unsigned x11 = (if neg then 0 else 1) -> INT_MIN <= cur <= INT_MAX ->
  KR (PRp.after_sign neg (zbytes lb) cur) ->
  ExecF.evtF rsegs RNG Q (ST 0x800a8 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros neg lb P x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 HB HPE HLP H9 H11 HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE. takeF true. unfold KR in K. apply K.
  - cbn [length] in HPE, BB. takeF false.
    pose proof (byte_range b) as Rb.
    apply (sc_post x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17 P); [exact H9 | lia |].
    intros y10 y12.
    pose proof (rdw0 m x9 _ _ (rui_bytes_hd m P b lb HB) H9) as R.
    pose proof (RDB P ltac:(lia)) as RB.
    step; clear R. step. step. step.
    destruct (is_digit (bv_unsigned b)) eqn:DG.
    + takeF_by false ltac:(rewrite PRp.digit_cond2, DG; reflexivity).
      step. step. takeF false.
      do 5 step.
      rewrite PRp.zbytes_cons, PRp.after_sign_digit in K by exact DG.
      eapply (digit_loop neg x11) with (k := length lb) (lb := b :: lb) (P := P) (v := 0).
      all: first [ exact H11 | exact HC | exact HB | exact HPE | exact HLP | exact H9 | exact K | reflexivity
                 | factF | (vm_compute; reflexivity) | lia ].
    + takeF_by true ltac:(rewrite PRp.digit_cond2, DG; reflexivity).
      rewrite PRp.zbytes_cons, PRp.after_sign_nondigit in K by exact DG. unfold KR in K. apply K.
Qed.

(* 0x80044: one byte of the leading-blank loop (a1 = 1, a2 = 31, a3 = 9, a4 = 32), and the sign check it falls
   into (0x80084-0x800a4), with the UBSan check of the cursor's increment (0x80098) *)
Lemma lead_body : forall (x11 x12 x13 x14 : word),
  bv_unsigned x11 = 1 -> bv_unsigned x12 = 31 -> bv_unsigned x13 = 9 -> bv_unsigned x14 = 32 ->
  INT_MIN <= cur <= INT_MAX ->
  forall (b : byte) (lb : list byte) (P : Z) (x5 x6 x9 x10 x15 x16 x17 : word),
  bytes_at rsegs m P (b :: lb) -> P + Z.of_nat (length (b :: lb)) = E -> LO <= P ->
  bv_unsigned x9 = P -> bv_unsigned x10 = P ->
  KR (PRp.parse_m (zbytes (b :: lb)) cur) ->
  (is_lead_blank (bv_unsigned b) = true -> forall y15 y16 : word,
     ExecF.evtF rsegs RNG Q (ST 0x80068 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 y15 y16 x17)) ->
  ExecF.evtF rsegs RNG Q (ST 0x80044 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x11 x12 x13 x14 H11 H12 H13 H14 HC b lb P x5 x6 x9 x10 x15 x16 x17 HB HPE HLP H9 H10 K KA.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  cbn [length] in HPE, BB.
  pose proof (byte_range b) as Rb.
  apply (sc_lead x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17 P); [exact H10 | lia |].
  intros y15 y16.
  pose proof (rdw0 m x9 _ _ (rui_bytes_hd m P b lb HB) H9) as R.
  pose proof (RDB P ltac:(lia)) as RB.
  step; clear R. step.
  rewrite PRp.zbytes_cons in K.
  destruct (Z.leb_spec (bv_unsigned b) 31) as [Lo|Hi].
  - takeF true. step.
    destruct (Z.eq_dec (bv_unsigned b) 9) as [E9|N9].
    + takeF false. apply KA. unfold is_lead_blank. rewrite E9. reflexivity.
    + takeF true.
      rewrite PRp.parse_nosign in K
        by (first [unfold is_lead_blank; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity | lia]).
      exact (post_sign false (b :: lb) P x5 x6 x9 _ x11 x12 x13 x14 _ _ x17 HB ltac:(cbn [length]; lia) HLP H9 H11 HC K).
  - takeF false. step.
    destruct (Z.eq_dec (bv_unsigned b) 32) as [E32|N32].
    + takeF false. step. apply KA. unfold is_lead_blank. rewrite E32. reflexivity.
    + takeF true. step. step.
      destruct (Z.eq_dec (bv_unsigned b) 43) as [E43|N43].
      * takeF true. step. step.
        takeF_by false ltac:(rui_cursor_ok H9).
        step. step. step.
        eapply (post_sign false lb (P + 1));
          [ exact (rui_bytes_tl m P b lb HB) | lia | lia | factF | unfold zxb; rewrite E43; vm_compute; reflexivity
          | exact HC | rewrite E43, PRp.parse_plus in K; exact K ].
      * takeF false. step. step.
        destruct (Z.eq_dec (bv_unsigned b) 45) as [E45|N45].
        -- takeF false. step. step.
           takeF_by false ltac:(rui_cursor_ok H9).
           step. step. step.
           eapply (post_sign true lb (P + 1));
             [ exact (rui_bytes_tl m P b lb HB) | lia | lia | factF | unfold zxb; rewrite E45; vm_compute; reflexivity
             | exact HC | rewrite E45, PRp.parse_minus in K; exact K ].
        -- takeF true.
           rewrite PRp.parse_nosign in K
             by (first [unfold is_lead_blank; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity | lia]).
           exact (post_sign false (b :: lb) P x5 x6 x9 _ x11 x12 x13 x14 _ _ x17 HB ltac:(cbn [length]; lia) HLP H9 H11 HC K).
Qed.

(* the leading-blank loop (0x80044-0x80070), by induction on the bytes left; at the end of the reply it returns cur
   (0x8013c-0x80144) *)
Lemma lead_loop : forall (x11 x12 x13 x14 : word),
  bv_unsigned x11 = 1 -> bv_unsigned x12 = 31 -> bv_unsigned x13 = 9 -> bv_unsigned x14 = 32 ->
  INT_MIN <= cur <= INT_MAX ->
  forall k (lb : list byte) (P : Z) (x5 x6 x9 x10 x15 x16 x17 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P ->
  bv_unsigned x9 = P -> bv_unsigned x10 = P ->
  KR (PRp.parse_m (zbytes lb) cur) ->
  ExecF.evtF rsegs RNG Q (ST 0x80044 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros x11 x12 x13 x14 H11 H12 H13 H14 HC k. induction k as [|k IH];
    intros [|b lb] P x5 x6 x9 x10 x15 x16 x17 HL HB HPE HLP H9 H10 K; try discriminate.
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: apply (lead_body x11 x12 x13 x14 H11 H12 H13 H14 HC b lb P x5 x6 x9 x10 x15 x16 x17 HB HPE HLP H9 H10 K).
  all: intros TB y15 y16.
  all: cbn [length] in HL, HPE, BB.
  all: rewrite PRp.zbytes_cons, PRp.parse_blank in K by exact TB.
  all: step; step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    cbn [length Z.of_nat] in HPE.
    takeF false. step. step. step.
    takeF false. step.
    unfold KR in K. apply K.
  - takeF true.
    apply (IH lb (P + 1)); [lia | exact (rui_bytes_tl m P b lb HB) | lia | lia | factF | factF | exact K].
Qed.

(* 0x80030: a1 = 1 (no sign yet); `p < end` enters the leading-blank loop, else straight to 0x800a8 *)
Lemma entry : forall (lb : list byte) (P : Z) (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> LO <= P -> bv_unsigned x9 = P ->
  bv_unsigned x11 = 1 -> INT_MIN <= cur <= INT_MAX ->
  KR (PRp.parse_m (zbytes lb) cur) ->
  ExecF.evtF rsegs RNG Q (ST 0x80030 x5 x6 (Z_to_bv 64 cur) x9 x10 x11 x12 x13 x14 x15 x16 x17).
Proof.
  intros lb P x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 HB HPE HLP H9 H11 HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE. takeF true.
    eapply (post_sign false [] P); [exact HB | cbn; lia | exact HLP | exact H9 | exact H11 | exact HC | exact K].
  - cbn [length] in HPE, BB. takeF false. do 4 step.
    eapply (lead_loop _ _ _ _) with (k := length lb) (lb := b :: lb) (P := P).
    all: first [ exact HC | exact HB | exact HPE | exact HLP | exact H9 | exact H11 | exact K | reflexivity
               | factF | (vm_compute; reflexivity) ].
Qed.

End Ret.

(* 0x80024, after memchr: a0 is memchr's result (r + k for the first LF at k, else 0), so the end pointer s2 is r + k
   or stays r + n (`beqz a0`, `mv s2, a0`); then the parse from 0x80030 over the first line, whose value is
   rp_uci_int_m of the n bytes (the plain walk's model_line), returned by the epilogue. *)
Theorem rui_seg_ret : forall (RNG : ExecF.footprint)
    (x1 gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (ra sp c0 c1 c2 c3 a0w : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (junk bs : list byte) (r n cur k : Z),
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 c3; C8 c2; C8 c1; C8 c0; C8 ra] ->
  48 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp + -48) 48 ->
  bytes_at rsegs m r bs -> Z.of_nat (length bs) = n -> 0 < n -> 0 < r -> r + n <= 2 ^ 63 ->
  (forall x, r <= x < r + n ->
     exists kb : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some kb /\ (bv_signed kb = 0 \/ x mod 8 < bv_signed kb)) ->
  (forall x, r <= x < r + n -> ExecF.rng RNG x 1) ->
  (forall x, r <= x < r + n -> ExecF.rng RNG (x / 8 + ASAN_K) 1) ->
  0 <= k <= n -> find_byte 10 bs = (if k <? n then Some (Z.to_nat k) else None) ->
  bv_unsigned a0w = (if k <? n then r + k else 0) ->
  INT_MIN <= cur <= INT_MAX ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y5 y6 y11 y12 y13 y14 y15 y16 y17 : word,
       ms' = MS (mkR ra sp gp tp y5 y6 x7 c0 c1 (Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur))
                     y11 y12 y13 y14 y15 y16 y17 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 cur) (Z_to_bv 64 r) a0w
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (r + n)) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x80024) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    ra sp c0 c1 c2 c3 a0w F fc m junk bs r n cur k FR HSP RFR HB HL Hn Hr Hrn SH RD RS Hk FB Ha0 HC.
  change (Z_to_bv 64 ASAN_K) with (Z_to_bv 64 2147450880).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  assert (Hbs : bs <> []) by (intros ->; cbn in HL; lia).
  set (R := rp_uci_int_m (zbytes bs) cur).
  assert (HR : INT_MIN <= R <= INT_MAX) by (apply rp_uci_int_range; exact HC).
  assert (KE : forall (s2w : word) Q', (forall y5 y6 y11 y12 y13 y14 y15 y16 y17 : word,
      Q' (MS (mkR ra sp gp tp y5 y6 x7 c0 c1 (Z_to_bv 64 R) y11 y12 y13 y14 y15 y16 y17
                  c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m (seg_rom rsegs))) ->
    KR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x7 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
       F fc m s2w RNG Q' R).
  { intros s2w Q' HQ. unfold KR. intros y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y17.
    eapply evtF_mono; [eapply (rui_epi RNG ra sp gp tp c0 c1 c2 c3); [exact FR | exact HSP | exact RFR | exact HR] |].
    intros ms' ->. apply HQ. }
  step.
  destruct (Z.lt_ge_cases k n) as [Hkn|Hkn].
  - assert (Ek : (k <? n) = true) by (apply Z.ltb_lt; exact Hkn). rewrite Ek in Ha0, FB. cbv iota in Ha0, FB.
    takeF false. step. step.
    assert (PL : PRp.parse_m (zbytes (firstn (Z.to_nat k) bs)) cur = R)
      by (unfold R; rewrite (PRp.model_line bs cur Hbs), FB; reflexivity).
    eapply entry with (E := r + k) (LO := r) (HI := r + n) (lb := firstn (Z.to_nat k) bs) (P := r).
    all: first [ exact Ha0 | exact SH | exact RD | exact RS | exact HC
               | exact (rui_bytes_firstn m r bs (Z.to_nat k) HB)
               | (rewrite length_firstn; lia) | lia | factF
               | (rewrite PL; apply KE; intros; do 9 eexists; reflexivity) ].
  - assert (Ek : (k <? n) = false) by (apply Z.ltb_ge; exact Hkn). rewrite Ek in Ha0, FB. cbv iota in Ha0, FB.
    takeF true. step.
    assert (PL : PRp.parse_m (zbytes bs) cur = R)
      by (unfold R; rewrite (PRp.model_line bs cur Hbs), FB; reflexivity).
    eapply entry with (E := r + n) (LO := r) (HI := r + n) (lb := bs) (P := r).
    all: first [ exact SH | exact RD | exact RS | exact HC | exact HB | lia | factF
               | (rewrite PL; apply KE; intros; do 9 eexists; reflexivity) ].
Qed.
