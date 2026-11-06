(* The assembly of the slot proof of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan build, patched image) from its
   segment lemmas (slot-plan-ubsan.md section 5; the twin of lib/Prog/Seg/Slot.v).
   - Section Stmts: the statement S_<SEG> of every segment lemma that is not yet proved (continuation form:
     the H of each exit cut -> the H of the entry cut), and seg_lemmas, their conjunction.
   - Section Bridge: the run for n >= 2^26 (ENTRY to ret through 0x13300 -> 0x14114, outside GV), Post ->
     lib_post_g, and slot_lib: H(ENTRY) -> the slot obligation lib_contract_g for every j.
   - Section Slot: the segment lemmas as hypotheses (seg_A01 is the proved lemma of Seg/A01.v), the loops R00
     (loop_rt), F00 (loop_frames) and W00 (loop_rows) by induction on 7 - b, 256 - j and 11 - i, H(ENTRY) in
     the discharge order of plan-ubsan section 5, and slot_holds : slot_goal.
   R10, R11 and R13 keep the guarded forms of the plain assembly: R11 needs H(U134c8) only at b = 6 and
   H(U135b4) only at b = 5, R13 needs H(U1354c) only at b = 0 (each of these H depends on the loop's turn
   b + 1, so the unguarded forms are circular at b = 6, 5 and 1). The ubsan-only shapes (plan-ubsan 2): A02 has
   one exit; F03 exits to U1386c (len >= 50) and U1389c; F05 (U1386c) and F06 (U138ac) both exit to U13954;
   I03 (U13a28 -> U13a64) and G07 (U13b10 -> U13b68) are new. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot A01.
Import ListNotations.
Open Scope Z_scope.

(* ---- The segment lemmas still to prove (seg-brief-ubsan.md, slot-plan-ubsan.md sections 2 and 5) ---- *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* Start (A01 is Seg/A01.v). *)
Definition S_A02 : Prop := forall t : Z, Hcut B APIf ra (Inv_U13340 B APIf ra empty) -> Hat B APIf ra (Inv_U13310_at B APIf ra empty) t.
Definition S_A03 : Prop := Hcut B APIf ra (Inv_U13360 B APIf ra empty) -> Hcut B APIf ra (Inv_U136e4 B APIf ra empty) -> Hcut B APIf ra (Inv_U13340 B APIf ra empty).
(* Round trip. *)
Definition S_R01 : Prop := Hcut B APIf ra (Inv_U1336c B APIf ra empty) -> Hcut B APIf ra (Inv_U13360 B APIf ra empty).
Definition S_R02 : Prop := Hcut B APIf ra (Inv_U133a8 B APIf ra empty) -> Hcut B APIf ra (Inv_U1336c B APIf ra empty).
Definition S_R03 : Prop := Hcut B APIf ra (Inv_U133b8 B APIf ra empty) -> Hcut B APIf ra (Inv_U133a8 B APIf ra empty).
Definition S_R04 : Prop := Hat B APIf ra (Inv_U133e8_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_U133b8 B APIf ra empty).
Definition S_R05 : Prop := forall b : nat, Hat B APIf ra (Inv_U1340c_at B APIf ra empty) b -> Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b.
Definition S_R06 : Prop := forall b : nat, Hat B APIf ra (Inv_U13450_at B APIf ra empty) b -> Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b -> Hat B APIf ra (Inv_U1340c_at B APIf ra empty) b.
Definition S_R07 : Prop := forall b : nat, Hat B APIf ra (Inv_U13464_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13450_at B APIf ra empty) b.
Definition S_R08 : Prop := forall b : nat, Hat B APIf ra (Inv_U13474_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13464_at B APIf ra empty) b.
Definition S_R09 : Prop := forall b : nat,
  Hat B APIf ra (Inv_U134a8_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134ac_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13508_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13474_at B APIf ra empty) b.
Definition S_R10 : Prop :=
  (forall b : nat, Hat B APIf ra (Inv_U134fc_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134a8_at B APIf ra empty) b) /\ (Hat B APIf ra (Inv_U134fc_at B APIf ra empty) 6%nat -> Hcut B APIf ra (Inv_U134e0 B APIf ra empty)).
Definition S_R11 : Prop := forall b : nat,
  (b = 6%nat -> Hcut B APIf ra (Inv_U134e0 B APIf ra empty)) -> (b = 5%nat -> Hcut B APIf ra (Inv_U135cc B APIf ra empty)) -> Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134ac_at B APIf ra empty) b.
Definition S_R12 : Prop := forall b : nat, Hat B APIf ra (Inv_U13644_at B APIf ra empty) b -> Hat B APIf ra (Inv_U134fc_at B APIf ra empty) b.
Definition S_R13 : Prop := forall b : nat,
  (b = 0%nat -> Hcut B APIf ra (Inv_U13564 B APIf ra empty)) -> Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13508_at B APIf ra empty) b.
Definition S_R14 : Prop := Hcut B APIf ra (Inv_U13580 B APIf ra empty) -> Hcut B APIf ra (Inv_U13564 B APIf ra empty).
Definition S_R15 : Prop := Hcut B APIf ra (Inv_U135b0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13580 B APIf ra empty).
Definition S_R16 : Prop := Hcut B APIf ra (Inv_U135c4 B APIf ra empty) -> Hcut B APIf ra (Inv_U135b0 B APIf ra empty).
Definition S_R17 : Prop := Hat B APIf ra (Inv_U13644_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_U135c4 B APIf ra empty).
Definition S_R18 : Prop := Hcut B APIf ra (Inv_U135f0 B APIf ra empty) -> Hcut B APIf ra (Inv_U135cc B APIf ra empty).
Definition S_R19 : Prop := Hat B APIf ra (Inv_U13644_at B APIf ra empty) 5%nat -> Hcut B APIf ra (Inv_U135f0 B APIf ra empty).
Definition S_R20 : Prop := forall b : nat, Hat B APIf ra (Inv_U13644_at B APIf ra empty) b -> Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b.
Definition S_R21 : Prop := forall b : nat, Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13644_at B APIf ra empty) b.
Definition S_R22 : Prop := forall b : nat, Hat B APIf ra (Inv_U133e8_at B APIf ra empty) (S b) -> Hcut B APIf ra (Inv_U13654 B APIf ra empty) -> Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b.
Definition S_R23 : Prop := Hcut B APIf ra (Inv_U136c4 B APIf ra empty) -> Hcut B APIf ra (Inv_U136e4 B APIf ra empty) -> Hcut B APIf ra (Inv_U13654 B APIf ra empty).
Definition S_R24 : Prop := Hcut B APIf ra (Inv_U136e4 B APIf ra empty) -> Hcut B APIf ra (Inv_U136c4 B APIf ra empty).
(* Init and P8. *)
Definition S_P01 : Prop := Hcut B APIf ra (Inv_U136ec B APIf ra empty) -> Hcut B APIf ra (Inv_U136e4 B APIf ra empty).
Definition S_P02 : Prop := Hcut B APIf ra (Inv_U136fc B APIf ra empty) -> Hcut B APIf ra (Inv_U136ec B APIf ra empty).
Definition S_P03 : Prop := Hcut B APIf ra (Inv_U1372c B APIf ra empty) -> Hcut B APIf ra (Inv_U136fc B APIf ra empty).
Definition S_P04 : Prop := Hcut B APIf ra (Inv_U13750 B APIf ra empty) -> Hcut B APIf ra (Inv_U1372c B APIf ra empty).
Definition S_P05 : Prop := Hcut B APIf ra (Inv_U13760 B APIf ra empty) -> Hcut B APIf ra (Inv_U13750 B APIf ra empty).
Definition S_P06 : Prop := Hcut B APIf ra (Inv_U13774 B APIf ra empty) -> Hcut B APIf ra (Inv_U13760 B APIf ra empty).
Definition S_P07 : Prop := Hcut B APIf ra (Inv_U13784 B APIf ra empty) -> Hcut B APIf ra (Inv_U13774 B APIf ra empty).
Definition S_P08 : Prop := Hcut B APIf ra (Inv_U1379c B APIf ra empty) -> Hcut B APIf ra (Inv_U13784 B APIf ra empty).
Definition S_P09 : Prop := Hat B APIf ra (Inv_U137d0_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_U140f8 B APIf ra empty) -> Hcut B APIf ra (Inv_U1379c B APIf ra empty).
(* Frame loop, turn j. *)
Definition S_F01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13820_at B APIf ra empty) j -> Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j.
Definition S_F02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13844_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13898_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13820_at B APIf ra empty) j.
Definition S_F03 : Prop := forall j : nat, Hat B APIf ra (Inv_U13868_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13898_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13844_at B APIf ra empty) j.
Definition S_F04 : Prop := forall j : nat, Hat B APIf ra (Inv_U138a8_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13898_at B APIf ra empty) j.
Definition S_F05 : Prop := forall j : nat, Hat B APIf ra (Inv_U13954_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13868_at B APIf ra empty) j.
Definition S_F06 : Prop := forall j : nat, Hat B APIf ra (Inv_U13954_at B APIf ra empty) j -> Hat B APIf ra (Inv_U138a8_at B APIf ra empty) j.
Definition S_F07 : Prop := forall j : nat, Hat B APIf ra (Inv_U13964_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13954_at B APIf ra empty) j.
Definition S_F08 : Prop := forall j : nat, Hat B APIf ra (Inv_U13978_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13964_at B APIf ra empty) j.
Definition S_F09 : Prop := forall j : nat, Hat B APIf ra (Inv_U13984_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13978_at B APIf ra empty) j.
Definition S_F10 : Prop := forall j : nat, Hat B APIf ra (Inv_U139bc_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13984_at B APIf ra empty) j.
Definition S_I01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13a14_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a68_at B APIf ra empty) j -> Hat B APIf ra (Inv_U139bc_at B APIf ra empty) j.
Definition S_I02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13a28_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a14_at B APIf ra empty) j.
Definition S_I03 : Prop := forall j : nat, Hat B APIf ra (Inv_U13a64_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a28_at B APIf ra empty) j.
Definition S_G01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13a78_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a64_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U13a68_at B APIf ra empty) j.
Definition S_G02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13a94_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a78_at B APIf ra empty) j.
Definition S_G03 : Prop := forall j : nat, Hat B APIf ra (Inv_U13ab0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13ab4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a94_at B APIf ra empty) j.
Definition S_G04 : Prop := forall j : nat,
  Hat B APIf ra (Inv_U13af0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13b64_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13ab0_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U13ab4_at B APIf ra empty) j.
Definition S_G05 : Prop := forall j : nat, Hat B APIf ra (Inv_U13b04_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13af0_at B APIf ra empty) j.
Definition S_G07 : Prop := forall j : nat, Hat B APIf ra (Inv_U13b60_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13b04_at B APIf ra empty) j.
Definition S_G06 : Prop := forall j : nat, Hat B APIf ra (Inv_U13c58_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13b60_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U13b64_at B APIf ra empty) j.
(* is_8819, check_ports, classify, match, latch. *)
Definition S_E01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13c6c_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13c58_at B APIf ra empty) j.
Definition S_E02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13c88_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13c6c_at B APIf ra empty) j.
Definition S_E03 : Prop := forall j : nat, Hat B APIf ra (Inv_U13cf4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13c88_at B APIf ra empty) j.
Definition S_E04 : Prop := forall j : nat, Hat B APIf ra (Inv_U13da0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13cf4_at B APIf ra empty) j.
Definition S_Q01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13dc0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13da0_at B APIf ra empty) j.
Definition S_Q02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13dd8_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13dc0_at B APIf ra empty) j.
Definition S_Q03 : Prop := forall j : nat, Hat B APIf ra (Inv_U13de8_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13dd8_at B APIf ra empty) j.
Definition S_Q04 : Prop := forall j : nat, Hat B APIf ra (Inv_U13e28_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13de8_at B APIf ra empty) j.
Definition S_Q05 : Prop := forall j : nat, Hat B APIf ra (Inv_U13ed4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13e28_at B APIf ra empty) j.
Definition S_Q06 : Prop := forall j : nat, Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13ed4_at B APIf ra empty) j.
Definition S_C01 : Prop := forall j : nat, Hat B APIf ra (Inv_U13fb8_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j.
Definition S_C02 : Prop := forall j : nat, Hat B APIf ra (Inv_U13fec_at B APIf ra empty) j -> Hat B APIf ra (Inv_U14008_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13fb8_at B APIf ra empty) j.
Definition S_C03 : Prop := forall j : nat,
  Hat B APIf ra (Inv_U14048_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13fec_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U14008_at B APIf ra empty) j.
Definition S_W01 : Prop := forall j : nat, Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j 0%nat -> Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U14048_at B APIf ra empty) j.
Definition S_W02 : Prop := forall j i : nat, Hat2 B APIf ra (Inv_U14090_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i.
Definition S_W03 : Prop := forall j i : nat, Hat2 B APIf ra (Inv_U140a4_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_U140b0_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_U14090_at B APIf ra empty) j i.
Definition S_W04 : Prop := forall j i : nat,
  Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j (S i) -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_U140a4_at B APIf ra empty) j i /\ Hat2 B APIf ra (Inv_U140b0_at B APIf ra empty) j i.
Definition S_C04 : Prop := forall j : nat, Hat B APIf ra (Inv_U140d0_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j.
Definition S_C05 : Prop := forall j : nat, Hat B APIf ra (Inv_U140dc_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140d0_at B APIf ra empty) j.
Definition S_C06 : Prop := forall j : nat, Hat B APIf ra (Inv_U137d0_at B APIf ra empty) (S j) -> Hcut B APIf ra (Inv_U140f8 B APIf ra empty) -> Hat B APIf ra (Inv_U140dc_at B APIf ra empty) j.
Definition S_X01 : Prop := Hcut B APIf ra (Inv_U14110 B APIf ra empty) -> Hcut B APIf ra (Inv_U14114 B APIf ra empty) -> Hcut B APIf ra (Inv_U140f8 B APIf ra empty).
Definition S_X02 : Prop := Hcut B APIf ra (Inv_U14110 B APIf ra empty) /\ Hcut B APIf ra (Inv_U14114 B APIf ra empty).

Definition seg_lemmas : Prop :=
  S_A02 /\ S_A03 /\
  S_R01 /\ S_R02 /\ S_R03 /\ S_R04 /\ S_R05 /\ S_R06 /\ S_R07 /\ S_R08 /\ S_R09 /\ S_R10 /\ S_R11 /\ S_R12 /\
  S_R13 /\ S_R14 /\ S_R15 /\ S_R16 /\ S_R17 /\ S_R18 /\ S_R19 /\ S_R20 /\ S_R21 /\ S_R22 /\ S_R23 /\ S_R24 /\
  S_P01 /\ S_P02 /\ S_P03 /\ S_P04 /\ S_P05 /\ S_P06 /\ S_P07 /\ S_P08 /\ S_P09 /\
  S_F01 /\ S_F02 /\ S_F03 /\ S_F04 /\ S_F05 /\ S_F06 /\ S_F07 /\ S_F08 /\ S_F09 /\ S_F10 /\
  S_I01 /\ S_I02 /\ S_I03 /\ S_G01 /\ S_G02 /\ S_G03 /\ S_G04 /\ S_G05 /\ S_G07 /\ S_G06 /\
  S_E01 /\ S_E02 /\ S_E03 /\ S_E04 /\ S_Q01 /\ S_Q02 /\ S_Q03 /\ S_Q04 /\ S_Q05 /\ S_Q06 /\
  S_C01 /\ S_C02 /\ S_C03 /\ S_W01 /\ S_W02 /\ S_W03 /\ S_W04 /\ S_C04 /\ S_C05 /\ S_C06 /\
  S_X01 /\ S_X02.

End Stmts.

(* ---- n >= 2^26 (libreac v1.9.0): [0x132c4, 0x13300] then the branch to 0x14114 and the epilogue
   [0x14114, 0x14150] ---- *)
Lemma top_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

Lemma early_cond : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = true.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (H1 : 1 <= u / 2 ^ 26) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : u / 2 ^ 26 < 2 ^ 38) by (apply Z.div_lt_upper_bound; lia).
  rewrite (top_bv_eqb (u / 2 ^ 26) 0) by lia.
  destruct (Z.eqb_spec (u / 2 ^ 26) 0); [lia | reflexivity].
Qed.

Lemma early_evt :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z),
    stk rsegs m lo S -> lo + 1936 <= S -> S < 2 ^ 64 -> mem_inv rsegs m ->
    2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (sp' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         sp' = Z_to_bv 64 S /\
         munch [(S - 1936, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132c4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo ST LO HS MI Ha1.
  pose proof (munch_refl [(S - 1936, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  carve_frame 1936%nat ST.
  do 16 step.
  if_true_by (early_cond (bv_unsigned a1) ltac:(lia)).
  do 16 step.
  release_frame FR ST S.
  finish.
  all: try (f_equal; lia).
Qed.

Lemma top_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia | rewrite KindBGlue.kb_mod2_land; exact Hz].
Qed.

Lemma top_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

(* ---- H(ENTRY) -> the slot obligation ---- *)
Section Bridge.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

(* frame_facts taken apart by the TYPE of each conjunct, never by its position. *)
Ltac slot_ff := let H := fresh "FFd" in pose proof FF as H; red in H; decompose [and] H.

Lemma slot_ff_libk : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Proof. slot_ff. assumption. Qed.

Lemma slot_ff_delta : forall n b, @lib_delta LS n b = b.
Proof. slot_ff. assumption. Qed.

Lemma slot_ff_room : forall b n, @lib_room LS b n -> slot_room b.
Proof. slot_ff. unfold slot_room. assumption. Qed.

Lemma slot_ff_ra : ra mod 2 = 0.
Proof. slot_ff. assumption. Qed.

(* The n >= 2^26 run in the ubsan build: A01's second exit (0x13300 -> 0x14114) and the epilogue. *)
Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  SR (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post B APIf ra g).
Proof.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof slot_ff_ra as HRA.
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof alloc_ceiling_lt as Hac47.
  pose proof sl_ceil as HTOP.
  unfold SLOT_STACK in *.
  assert (Esp : spZ (g_regs g) = g_S g) by exact Hspz.
  destruct Hpp as [[Hn0 _] | [Hnpos (q & Hq & Eq)]]; [lia|].
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (g_n g) HM Hq) as [Hq1 Hq2].
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = g_n g) by (rewrite Hnn; apply MState.unsigned_lit; lia).
  rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY. rewrite Hsp.
    apply early_evt with (lo := g_S g - 65536).
    + apply sl_stk_norm; [exact HMI | unfold SL_TOP in *; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (sp' & a2' & m'' & HE & Esp' & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 1936, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 1936 <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (sl_unch _ _ _ (g_S g - 1936) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - 1936) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (LOW : forall a, 0 <= a < YM05.alloc_ceiling -> m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha. apply UN; lia. }
    apply SR_ret. unfold Post. rewrite SEGS.
    exists (g_L g), (g_A g), regs', m', (g_md g).
    split; [rewrite Hra, (top_ret_pc_ra ra HRA); reflexivity|].
    split.
    + unfold lib_post. rewrite SEGS.
      split.
      { apply (KindBGlue.kb_MR_A B API (g_L g) (g_A g) (g_mem g) m' (g_md g) [(g_S g - 1936, g_S g)] HM).
        - intros x Hx0. apply MU'. exact Hx0.
        - intros x Hx1 _. cbn [Frame.outside]. split; [lia | exact I]. }
      split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
      split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr. rewrite (sl_getr_eqv _ _ _ Hx).
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          first [reflexivity | symmetry; exact Hsp]. }
      split; [exists (m_vmmaps (g_md g)); apply with_vmmaps_self|].
      split; [intros q0 k Hq0; exists q0; split; [exact Hq0 | reflexivity]|].
      split.
      { intros a Ha Hns. unfold lib_scratch in Hns. rewrite Esp in Hns. apply sl_eq_at. apply UN; [lia|].
        intros Hin. apply Hns. left. unfold SLOT_STACK. lia. }
      split.
      { intros a Himg _ _ _ _. pose proof (sl_in_img_top B a SEGS Himg) as Hl0.
        apply sl_eq_at. apply LOW. lia. }
      split.
      { intros q0 k i Hq0 _ Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q0 k HM Hq0) as [R1 R2].
        exact (proj1 (sl_eq_at _ _ _ (LOW (ptr_addr (g_L g) q0 + i) ltac:(lia)))). }
      intros a Hs.
      assert (Hw : writable_at rsegs (g_mem g) a)
        by (rewrite <- SEGS; destruct Hs as [Hs|Hs]; [apply Hstw; exact Hs | apply Herr; exact Hs]).
      unfold writable_at in *. apply WM'. exact Hw.
    + split.
      { apply (sl_sink_keep B APIf ra empty FF (g_mem g) m' (g_md g)); [| exact Hsn].
        intros a Ha. apply LOW. lia. }
      split; [unfold MI; try rewrite SEGS; exact Hro'|].
      split; [exact Hres|].
      intros i Hi. try rewrite SEGS.
      exact (proj1 (sl_eq_at _ _ _ (LOW (g_p g + i) ltac:(rewrite <- Eq; lia)))).
Qed.

Lemma slot_post_g : forall g c', Post B APIf ra g c' -> Fs.fs_sorted (m_fs (g_md g)) = true -> frm_zero fp_csr ->
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) (g_n g) (g_b g)
      (LL 0 (m_fs (g_md g)) []) L' A' regs' mem' md' /\ True.
Proof.
  intros g c' (L' & A' & regs' & mem' & md' & -> & HLP & HSN & HMI & HRE & HPAY) Hsorted Hfrm.
  exists fx, L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hfrm|]. split; [|exact I].
  destruct HLP as (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12).
  unfold lib_post_g. cbn [ll_ret ll_out ll_fs].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|].
  split; [exists vm', (m_fds (g_md g)), (m_statpins (g_md g)); split; [rewrite Hmd; apply with_vmmaps_os_upd |
          intros k; reflexivity]|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [intros a (lo & len & [] & _)|].
  split; [exact H11|]. split; [exact H12|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
  split; [exact HSN|]. split; [exact HMI|].
  split; [rewrite slot_ff_delta; exact HRE|].
  exact HPAY.
Qed.

Lemma slot_lib : Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros HE j L A regs mem md p n pl b K Hpre _ HR HRO _ Hfrm HK.
  rewrite slot_ff_libk.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hfdc & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n, nlen; cbn [g_in g]; lia).
  assert (HKg : forall c', Post B APIf ra g c' -> realizes (ms_segs B) c' (K (LL 0 (m_fs md) []))).
  { intros c' Hc'. apply HK.
    destruct (slot_post_g g c' Hc' Hsorted Hfrm) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & _).
    exists fx', L', A', regs', mem', md'. split; [exact E|]. split; [exact F0|]. split; [|exact I].
    rewrite Egn in LP. exact LP. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsm|Hbig].
  - assert (HEN : Inv_ENTRY B APIf ra empty g
                    (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)).
    { unfold SLOT_K, SLOT_STACK in *.
      split; [reflexivity|].
      split.
      { split; [rewrite Egn; lia|]. split.
        { destruct Hpp as [[-> ->] | [Hn0 (q & Hq & <-)]]; [left; rewrite Egn; split; reflexivity|].
          right. rewrite Egn. split; [exact Hn0|]. apply top_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [exact (slot_ff_room b n Hroom)|]. split; [exact Hsp|]. split; [exact Htp|].
        (* PB: the input block lies in [4096, alloc_ceiling) (mr_blocks_range). *)
        destruct Hpp as [[Hn0 _] | [Hn0 (q & Hq & Eq)]]; [left; rewrite Egn; exact Hn0|].
        right. change (g_p g) with p. rewrite Egn.
        pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as [R1 R2]. lia. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|]. exact Hres. }
    exact (SR_realizes (ms_segs B) _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes (ms_segs B) _ _ _ (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
             ltac:(rewrite Egn; exact HP0) HSink HRO Hres) HKg).
Qed.

End Bridge.

(* ---- The composition (slot-plan-ubsan.md section 5) ---- *)
Section Slot.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Hypothesis seg_A02 : S_A02 B APIf ra empty.
Hypothesis seg_A03 : S_A03 B APIf ra empty.
Hypothesis seg_R01 : S_R01 B APIf ra empty.
Hypothesis seg_R02 : S_R02 B APIf ra empty.
Hypothesis seg_R03 : S_R03 B APIf ra empty.
Hypothesis seg_R04 : S_R04 B APIf ra empty.
Hypothesis seg_R05 : S_R05 B APIf ra empty.
Hypothesis seg_R06 : S_R06 B APIf ra empty.
Hypothesis seg_R07 : S_R07 B APIf ra empty.
Hypothesis seg_R08 : S_R08 B APIf ra empty.
Hypothesis seg_R09 : S_R09 B APIf ra empty.
Hypothesis seg_R10 : S_R10 B APIf ra empty.
Hypothesis seg_R11 : S_R11 B APIf ra empty.
Hypothesis seg_R12 : S_R12 B APIf ra empty.
Hypothesis seg_R13 : S_R13 B APIf ra empty.
Hypothesis seg_R14 : S_R14 B APIf ra empty.
Hypothesis seg_R15 : S_R15 B APIf ra empty.
Hypothesis seg_R16 : S_R16 B APIf ra empty.
Hypothesis seg_R17 : S_R17 B APIf ra empty.
Hypothesis seg_R18 : S_R18 B APIf ra empty.
Hypothesis seg_R19 : S_R19 B APIf ra empty.
Hypothesis seg_R20 : S_R20 B APIf ra empty.
Hypothesis seg_R21 : S_R21 B APIf ra empty.
Hypothesis seg_R22 : S_R22 B APIf ra empty.
Hypothesis seg_R23 : S_R23 B APIf ra empty.
Hypothesis seg_R24 : S_R24 B APIf ra empty.
Hypothesis seg_P01 : S_P01 B APIf ra empty.
Hypothesis seg_P02 : S_P02 B APIf ra empty.
Hypothesis seg_P03 : S_P03 B APIf ra empty.
Hypothesis seg_P04 : S_P04 B APIf ra empty.
Hypothesis seg_P05 : S_P05 B APIf ra empty.
Hypothesis seg_P06 : S_P06 B APIf ra empty.
Hypothesis seg_P07 : S_P07 B APIf ra empty.
Hypothesis seg_P08 : S_P08 B APIf ra empty.
Hypothesis seg_P09 : S_P09 B APIf ra empty.
Hypothesis seg_F01 : S_F01 B APIf ra empty.
Hypothesis seg_F02 : S_F02 B APIf ra empty.
Hypothesis seg_F03 : S_F03 B APIf ra empty.
Hypothesis seg_F04 : S_F04 B APIf ra empty.
Hypothesis seg_F05 : S_F05 B APIf ra empty.
Hypothesis seg_F06 : S_F06 B APIf ra empty.
Hypothesis seg_F07 : S_F07 B APIf ra empty.
Hypothesis seg_F08 : S_F08 B APIf ra empty.
Hypothesis seg_F09 : S_F09 B APIf ra empty.
Hypothesis seg_F10 : S_F10 B APIf ra empty.
Hypothesis seg_I01 : S_I01 B APIf ra empty.
Hypothesis seg_I02 : S_I02 B APIf ra empty.
Hypothesis seg_I03 : S_I03 B APIf ra empty.
Hypothesis seg_G01 : S_G01 B APIf ra empty.
Hypothesis seg_G02 : S_G02 B APIf ra empty.
Hypothesis seg_G03 : S_G03 B APIf ra empty.
Hypothesis seg_G04 : S_G04 B APIf ra empty.
Hypothesis seg_G05 : S_G05 B APIf ra empty.
Hypothesis seg_G07 : S_G07 B APIf ra empty.
Hypothesis seg_G06 : S_G06 B APIf ra empty.
Hypothesis seg_E01 : S_E01 B APIf ra empty.
Hypothesis seg_E02 : S_E02 B APIf ra empty.
Hypothesis seg_E03 : S_E03 B APIf ra empty.
Hypothesis seg_E04 : S_E04 B APIf ra empty.
Hypothesis seg_Q01 : S_Q01 B APIf ra empty.
Hypothesis seg_Q02 : S_Q02 B APIf ra empty.
Hypothesis seg_Q03 : S_Q03 B APIf ra empty.
Hypothesis seg_Q04 : S_Q04 B APIf ra empty.
Hypothesis seg_Q05 : S_Q05 B APIf ra empty.
Hypothesis seg_Q06 : S_Q06 B APIf ra empty.
Hypothesis seg_C01 : S_C01 B APIf ra empty.
Hypothesis seg_C02 : S_C02 B APIf ra empty.
Hypothesis seg_C03 : S_C03 B APIf ra empty.
Hypothesis seg_W01 : S_W01 B APIf ra empty.
Hypothesis seg_W02 : S_W02 B APIf ra empty.
Hypothesis seg_W03 : S_W03 B APIf ra empty.
Hypothesis seg_W04 : S_W04 B APIf ra empty.
Hypothesis seg_C04 : S_C04 B APIf ra empty.
Hypothesis seg_C05 : S_C05 B APIf ra empty.
Hypothesis seg_C06 : S_C06 B APIf ra empty.
Hypothesis seg_X01 : S_X01 B APIf ra empty.
Hypothesis seg_X02 : S_X02 B APIf ra empty.

(* Past the last turn the loop cuts hold no state: b <= 6 (RB), j <= 255 (LK), i <= 10 (WB). *)
Lemma vac_U133d0 : forall b, (6 < b)%nat -> Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b.
Proof. intros b Hb g c (L & A & regs & mem & md & _ & _ & _ & Hb' & _). lia. Qed.

Lemma vac_U137d0 : forall j, (255 < j)%nat -> Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j.
Proof. intros j Hj g c (L & A & regs & mem & md & _ & _ & _ & (Hj' & _) & _). lia. Qed.

Lemma vac_U14070 : forall j i, (10 < i)%nat -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i.
Proof. intros j i Hi g c (phi & L & A & regs & mem & md & _ & _ & _ & _ & Hi' & _). lia. Qed.

(* W00: row i of row_of_block. *)
Lemma turn_rows : forall j i, Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j (S i) -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i.
Proof.
  intros j i Hd0 Hcc HS.
  destruct (seg_W04 j i Hd0 HS Hcc) as [Hb0 Hbc].
  exact (seg_W02 j i (seg_W03 j i Hb0 Hbc)).
Qed.

Lemma loop_rows : forall j, Hat B APIf ra (Inv_U140c4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j -> forall i, Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i.
Proof.
  intros j Hd0 Hcc.
  assert (IND : forall k i, (11 <= i + k)%nat -> Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i).
  { induction k as [|k IH]; intros i Hk.
    - exact (vac_U14070 j i ltac:(lia)).
    - destruct (Nat.lt_ge_cases 10 i) as [Hi|Hi]; [exact (vac_U14070 j i Hi)|].
      exact (turn_rows j i Hd0 Hcc (IH (S i) ltac:(lia))). }
  intros i. exact (IND 11%nat i ltac:(lia)).
Qed.

(* F00: frame turn j (F01 .. C06, W00 inside), in the order of plan-ubsan section 5 step 2. *)
Lemma turn_frames : forall j, Hcut B APIf ra (Inv_U140f8 B APIf ra empty) -> Hat B APIf ra (Inv_U137d0_at B APIf ra empty) (S j) -> Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j.
Proof.
  intros j H108 HS.
  pose proof (seg_C06 j HS H108) as He8.
  pose proof (seg_C05 j He8) as Hdc.
  destruct (seg_C04 j Hdc) as [Hcc Hd0].
  pose proof (loop_rows j Hd0 Hcc 0%nat) as H070.
  pose proof (seg_W01 j H070 Hd0) as H054.
  destruct (seg_C03 j H054 Hcc) as [Hff8 H014].
  pose proof (seg_C02 j Hff8 H014) as Hfc4.
  pose proof (seg_C01 j Hfc4) as Hfa4.
  pose proof (seg_Q06 j Hfa4) as Hee0.
  pose proof (seg_Q05 j Hee0) as He34.
  pose proof (seg_Q04 j He34 Hfa4) as Hdf4.
  pose proof (seg_Q03 j Hdf4) as Hde4.
  pose proof (seg_Q02 j Hde4) as Hdcc.
  pose proof (seg_Q01 j Hdcc) as Hdac.
  pose proof (seg_E04 j Hdac) as Hd00.
  pose proof (seg_E03 j Hd00) as Hc94.
  pose proof (seg_E02 j Hc94) as Hc78.
  pose proof (seg_E01 j Hc78 Hfa4) as Hc64.
  destruct (seg_G06 j Hc64) as [Hb68 Hb6c].
  pose proof (seg_G07 j Hb68) as Hb10.
  pose proof (seg_G05 j Hb10) as Haf8.
  destruct (seg_G04 j Haf8 Hb6c) as [Hab0 Hab4].
  pose proof (seg_G03 j Hab0 Hab4) as Ha94.
  pose proof (seg_G02 j Ha94) as Ha78.
  destruct (seg_G01 j Ha78) as [Ha64 Ha68].
  pose proof (seg_I03 j Ha64) as Ha28.
  pose proof (seg_I02 j Ha28) as Ha14.
  pose proof (seg_I01 j Ha14 Ha68) as H9bc.
  pose proof (seg_F10 j H9bc) as H984.
  pose proof (seg_F09 j H984) as H978.
  pose proof (seg_F08 j H978) as H964.
  pose proof (seg_F07 j H964) as H954.
  pose proof (seg_F06 j H954) as H8ac.
  pose proof (seg_F05 j H954) as H86c.
  pose proof (seg_F04 j H8ac) as H89c.
  pose proof (seg_F03 j H86c H89c) as H848.
  pose proof (seg_F02 j H848 H89c) as H820.
  exact (seg_F01 j H820).
Qed.

Lemma loop_frames : Hcut B APIf ra (Inv_U140f8 B APIf ra empty) -> forall j, Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j.
Proof.
  intros H108.
  assert (IND : forall k j, (256 <= j + k)%nat -> Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j).
  { induction k as [|k IH]; intros j Hk.
    - exact (vac_U137d0 j ltac:(lia)).
    - destruct (Nat.lt_ge_cases 255 j) as [Hj|Hj]; [exact (vac_U137d0 j Hj)|].
      exact (turn_frames j H108 (IH (S j) ltac:(lia))). }
  intros j. exact (IND 256%nat j ltac:(lia)).
Qed.

(* R00: round-trip turn b (R05 .. R22). H(U134c8) is the b = 6 arm and needs only turn 7, which holds no
   state; H(U135b4) (b = 5) needs turn 6 and H(U1354c) (b = 0) needs turn 1: both are H(U133d0)[b + 1]. *)
Lemma rt_U134c8 : Hcut B APIf ra (Inv_U13654 B APIf ra empty) -> Hcut B APIf ra (Inv_U134e0 B APIf ra empty).
Proof.
  intros H63c. pose proof seg_R10 as [_ R10b].
  exact (R10b (seg_R12 6%nat (seg_R21 6%nat (seg_R22 6%nat (vac_U133d0 7%nat ltac:(lia)) H63c)))).
Qed.

Lemma turn_rt : forall b, Hcut B APIf ra (Inv_U13654 B APIf ra empty) -> Hat B APIf ra (Inv_U133e8_at B APIf ra empty) (S b) -> Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b.
Proof.
  intros b H63c HS.
  pose proof seg_R10 as [R10a _].
  pose proof (seg_R22 b HS H63c) as H634.
  pose proof (seg_R21 b H634) as H62c.
  pose proof (seg_R12 b H62c) as H4e4.
  pose proof (seg_R20 b H62c) as H5e0.
  pose proof (R10a b H4e4) as H490.
  pose proof (rt_U134c8 H63c) as H4c8.
  assert (H5b4 : b = 5%nat -> Hcut B APIf ra (Inv_U135cc B APIf ra empty)).
  { intros ->. exact (seg_R18 (seg_R19 H62c)). }
  assert (H54c : b = 0%nat -> Hcut B APIf ra (Inv_U13564 B APIf ra empty)).
  { intros ->. exact (seg_R14 (seg_R15 (seg_R16 (seg_R17 H62c)))). }
  pose proof (seg_R11 b (fun _ => H4c8) H5b4 H5e0) as H494.
  pose proof (seg_R13 b H54c H5e0) as H4f0.
  pose proof (seg_R09 b H490 H494 H4f0) as H45c.
  pose proof (seg_R08 b H45c) as H44c.
  pose proof (seg_R07 b H44c) as H438.
  pose proof (seg_R06 b H438 H634) as H3f4.
  exact (seg_R05 b H3f4).
Qed.

Lemma loop_rt : Hcut B APIf ra (Inv_U13654 B APIf ra empty) -> forall b, Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b.
Proof.
  intros H63c.
  assert (IND : forall k b, (7 <= b + k)%nat -> Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b).
  { induction k as [|k IH]; intros b Hk.
    - exact (vac_U133d0 b ltac:(lia)).
    - destruct (Nat.lt_ge_cases 6 b) as [Hb|Hb]; [exact (vac_U133d0 b Hb)|].
      exact (turn_rt b H63c (IH (S b) ltac:(lia))). }
  intros b. exact (IND 7%nat b ltac:(lia)).
Qed.

(* Plan-ubsan section 5, steps 1-5. *)
Lemma slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  pose proof seg_X02 as [H120 H124].
  pose proof (seg_X01 H120 H124) as H108.
  pose proof (loop_frames H108 0%nat) as H7d0.
  pose proof (seg_P09 H7d0 H108) as H774.
  pose proof (seg_P08 H774) as H75c.
  pose proof (seg_P07 H75c) as H74c.
  pose proof (seg_P06 H74c) as H738.
  pose proof (seg_P05 H738) as H728.
  pose proof (seg_P04 H728) as H704.
  pose proof (seg_P03 H704) as H6d4.
  pose proof (seg_P02 H6d4) as H6c4.
  pose proof (seg_P01 H6c4) as H6bc.
  pose proof (seg_R24 H6bc) as H6ac.
  pose proof (seg_R23 H6ac H6bc) as H63c.
  pose proof (loop_rt H63c 0%nat) as H3d0.
  pose proof (seg_R04 H3d0) as H3a0.
  pose proof (seg_R03 H3a0) as H390.
  pose proof (seg_R02 H390) as H354.
  pose proof (seg_R01 H354) as H348.
  pose proof (seg_A03 H348 H6bc) as H328.
  pose proof (seg_A02 0 H328) as H2f8.
  exact (seg_A01 B APIf ra empty FF H2f8 H124).
Qed.

(* Step 6: the slot obligation, n >= 2^26 included. *)
Theorem slot_holds : slot_goal B APIf ra empty.
Proof. intros j _. exact (slot_lib B APIf ra empty FF slot_entry j). Qed.

End Slot.

Section Bundle.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Theorem slot_of_lemmas : frame_facts B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty ->
  slot_goal B APIf ra empty.
Proof.
  intros FF H. unfold seg_lemmas in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  eapply slot_holds; eassumption.
Qed.

End Bundle.
