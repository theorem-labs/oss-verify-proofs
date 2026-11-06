(* The assembly of the slot proof of fuzz_ctrl LLVMFuzzerTestOneInput (plain build, libreac v1.9.0) from its
   segment lemmas (slot-plan.md section 5).
   - Section Stmts: the statement S_<SEG> of every segment lemma that is not yet proved (continuation form:
     the H of each exit cut -> the H of the entry cut), and seg_lemmas, their conjunction.
   - Section Bridge: the run for n >= 2^26 (ENTRY to ret through 0x13234 -> 0x13dd0, outside GV), Post ->
     lib_post_g, and slot_lib: H(ENTRY) -> the slot obligation lib_contract_g for every j.
   - Section Slot: the segment lemmas as hypotheses (seg_A01 is the proved lemma of Seg/A01.v), the loops R00
     (loop_rt), F00 (loop_frames) and W00 (loop_rows) by induction on 7 - b, 256 - j and 11 - i, H(ENTRY) in
     the discharge order of plan section 5, and slot_holds : slot_goal.
   R10, R11 and R13 are stated so that the round-trip loop composes: R11 needs H(K13408) only at b = 6 and
   H(K134bc) only at b = 5, R13 needs H(K13464) only at b = 0 (each of these H depends on the loop's turn
   b + 1, so the unguarded forms are circular at b = 6, 5 and 1).
   libreac v1.9.0 (libreac-v190/plain/fuzz_ctrl; plain segment table v190-segment-table-plain.md (a working note, not in this delivery)):
   every cut name follows lib/Prog/SlotInv.v's renames (56 cuts, K135a0 -> K135b0 ..
   K13d9c -> K13dd0; so do the lemma names vac_K13694 (was vac_K1368c) and vac_K13d4c (was vac_K13d1c)); every
   S_<SEG> keeps its v1.8 shape on the renamed cuts. K13598 stays at 0x13598, so the new memset of `first`
   (0x13598 .. 0x135a4) is inside S_P01 (K135b0 -> K13598). The early run is the v1.8 one with the frame 1936 (was
   1920) and the branch target 0x13dd0 (was 0x13d9c): the v1.9.0 listing 0x131f8 .. 0x13234, 0x13dd0 .. 0x13e0c has
   the same 32 instructions. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot A01.
Import ListNotations.
Open Scope Z_scope.

(* ---- The segment lemmas still to prove (seg-brief.md, slot-plan.md sections 2 and 5) ---- *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.


(* Start (A01 is Seg/A01.v). *)
Definition S_A02 : Prop := forall t : Z, Hcut B APIf ra (Inv_K13288 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hat B APIf ra (Inv_K1324c_at B APIf ra empty) t.
Definition S_A03 : Prop := Hcut B APIf ra (Inv_K132a0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hcut B APIf ra (Inv_K13288 B APIf ra empty).
(* Round trip. *)
Definition S_R01 : Prop := Hcut B APIf ra (Inv_K132ac B APIf ra empty) -> Hcut B APIf ra (Inv_K132a0 B APIf ra empty).
Definition S_R02 : Prop := Hcut B APIf ra (Inv_K132d4 B APIf ra empty) -> Hcut B APIf ra (Inv_K132ac B APIf ra empty).
Definition S_R03 : Prop := Hcut B APIf ra (Inv_K132e4 B APIf ra empty) -> Hcut B APIf ra (Inv_K132d4 B APIf ra empty).
Definition S_R04 : Prop := Hat B APIf ra (Inv_K1330c_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_K132e4 B APIf ra empty).
Definition S_R05 : Prop := forall b : nat, Hat B APIf ra (Inv_K13330_at B APIf ra empty) b -> Hat B APIf ra (Inv_K1330c_at B APIf ra empty) b.
Definition S_R06 : Prop := forall b : nat, Hat B APIf ra (Inv_K13374_at B APIf ra empty) b -> Hat B APIf ra (Inv_K1351c_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13330_at B APIf ra empty) b.
Definition S_R07 : Prop := forall b : nat, Hat B APIf ra (Inv_K13388_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13374_at B APIf ra empty) b.
Definition S_R08 : Prop := forall b : nat, Hat B APIf ra (Inv_K13398_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13388_at B APIf ra empty) b.
Definition S_R09 : Prop := forall b : nat,
  Hat B APIf ra (Inv_K133cc_at B APIf ra empty) b -> Hat B APIf ra (Inv_K133d4_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13428_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13398_at B APIf ra empty) b.
Definition S_R10 : Prop :=
  (forall b : nat, Hat B APIf ra (Inv_K13420_at B APIf ra empty) b -> Hat B APIf ra (Inv_K133cc_at B APIf ra empty) b) /\ (Hat B APIf ra (Inv_K13420_at B APIf ra empty) 6%nat -> Hcut B APIf ra (Inv_K13408 B APIf ra empty)).
Definition S_R11 : Prop := forall b : nat,
  (b = 6%nat -> Hcut B APIf ra (Inv_K13408 B APIf ra empty)) -> (b = 5%nat -> Hcut B APIf ra (Inv_K134bc B APIf ra empty)) -> Hat B APIf ra (Inv_K134e8_at B APIf ra empty) b -> Hat B APIf ra (Inv_K133d4_at B APIf ra empty) b.
Definition S_R12 : Prop := forall b : nat, Hat B APIf ra (Inv_K13514_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13420_at B APIf ra empty) b.
Definition S_R13 : Prop := forall b : nat,
  (b = 0%nat -> Hcut B APIf ra (Inv_K13464 B APIf ra empty)) -> Hat B APIf ra (Inv_K134e8_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13428_at B APIf ra empty) b.
Definition S_R14 : Prop := Hcut B APIf ra (Inv_K13478 B APIf ra empty) -> Hcut B APIf ra (Inv_K13464 B APIf ra empty).
Definition S_R15 : Prop := Hcut B APIf ra (Inv_K134a0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13478 B APIf ra empty).
Definition S_R16 : Prop := Hcut B APIf ra (Inv_K134b4 B APIf ra empty) -> Hcut B APIf ra (Inv_K134a0 B APIf ra empty).
Definition S_R17 : Prop := Hat B APIf ra (Inv_K13514_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_K134b4 B APIf ra empty).
Definition S_R18 : Prop := Hcut B APIf ra (Inv_K134e0 B APIf ra empty) -> Hcut B APIf ra (Inv_K134bc B APIf ra empty).
Definition S_R19 : Prop := Hat B APIf ra (Inv_K13514_at B APIf ra empty) 5%nat -> Hcut B APIf ra (Inv_K134e0 B APIf ra empty).
Definition S_R20 : Prop := forall b : nat, Hat B APIf ra (Inv_K13514_at B APIf ra empty) b -> Hat B APIf ra (Inv_K134e8_at B APIf ra empty) b.
Definition S_R21 : Prop := forall b : nat, Hat B APIf ra (Inv_K1351c_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13514_at B APIf ra empty) b.
Definition S_R22 : Prop := forall b : nat, Hat B APIf ra (Inv_K1330c_at B APIf ra empty) (S b) -> Hcut B APIf ra (Inv_K13524 B APIf ra empty) -> Hat B APIf ra (Inv_K1351c_at B APIf ra empty) b.
Definition S_R23 : Prop := Hcut B APIf ra (Inv_K1358c B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hcut B APIf ra (Inv_K13524 B APIf ra empty).
Definition S_R24 : Prop := Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hcut B APIf ra (Inv_K1358c B APIf ra empty).
(* Init and P8. *)
Definition S_P01 : Prop := Hcut B APIf ra (Inv_K135b0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty).
Definition S_P02 : Prop := Hcut B APIf ra (Inv_K135c0 B APIf ra empty) -> Hcut B APIf ra (Inv_K135b0 B APIf ra empty).
Definition S_P03 : Prop := Hcut B APIf ra (Inv_K135f0 B APIf ra empty) -> Hcut B APIf ra (Inv_K135c0 B APIf ra empty).
Definition S_P04 : Prop := Hcut B APIf ra (Inv_K13614 B APIf ra empty) -> Hcut B APIf ra (Inv_K135f0 B APIf ra empty).
Definition S_P05 : Prop := Hcut B APIf ra (Inv_K13624 B APIf ra empty) -> Hcut B APIf ra (Inv_K13614 B APIf ra empty).
Definition S_P06 : Prop := Hcut B APIf ra (Inv_K13638 B APIf ra empty) -> Hcut B APIf ra (Inv_K13624 B APIf ra empty).
Definition S_P07 : Prop := Hcut B APIf ra (Inv_K13648 B APIf ra empty) -> Hcut B APIf ra (Inv_K13638 B APIf ra empty).
Definition S_P08 : Prop := Hcut B APIf ra (Inv_K13660 B APIf ra empty) -> Hcut B APIf ra (Inv_K13648 B APIf ra empty).
Definition S_P09 : Prop := Hat B APIf ra (Inv_K13694_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_K13db4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13660 B APIf ra empty).
(* Frame loop, turn j. *)
Definition S_F01 : Prop := forall j : nat, Hat B APIf ra (Inv_K136d4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Definition S_F02 : Prop := forall j : nat, Hat B APIf ra (Inv_K136f8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13734_at B APIf ra empty) j -> Hat B APIf ra (Inv_K136d4_at B APIf ra empty) j.
Definition S_F03 : Prop := forall j : nat, Hat B APIf ra (Inv_K1370c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K136f8_at B APIf ra empty) j.
Definition S_F04 : Prop := forall j : nat, Hat B APIf ra (Inv_K13748_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13734_at B APIf ra empty) j.
Definition S_F05 : Prop := forall j : nat, Hat B APIf ra (Inv_K1374c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K137c8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K1370c_at B APIf ra empty) j.
Definition S_F06 : Prop := forall j : nat, Hat B APIf ra (Inv_K137c8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13748_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K1374c_at B APIf ra empty) j.
Definition S_F07 : Prop := forall j : nat, Hat B APIf ra (Inv_K137d8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K137c8_at B APIf ra empty) j.
Definition S_F08 : Prop := forall j : nat, Hat B APIf ra (Inv_K137ec_at B APIf ra empty) j -> Hat B APIf ra (Inv_K137d8_at B APIf ra empty) j.
Definition S_F09 : Prop := forall j : nat, Hat B APIf ra (Inv_K137f8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K137ec_at B APIf ra empty) j.
Definition S_F10 : Prop := forall j : nat, Hat B APIf ra (Inv_K13830_at B APIf ra empty) j -> Hat B APIf ra (Inv_K137f8_at B APIf ra empty) j.
Definition S_I01 : Prop := forall j : nat, Hat B APIf ra (Inv_K13874_at B APIf ra empty) j -> Hat B APIf ra (Inv_K138c8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13830_at B APIf ra empty) j.
Definition S_I02 : Prop := forall j : nat, Hat B APIf ra (Inv_K138c4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13874_at B APIf ra empty) j.
Definition S_G01 : Prop := forall j : nat, Hat B APIf ra (Inv_K138d8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K138c4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K138c8_at B APIf ra empty) j.
Definition S_G02 : Prop := forall j : nat, Hat B APIf ra (Inv_K138f4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K138d8_at B APIf ra empty) j.
Definition S_G03 : Prop := forall j : nat, Hat B APIf ra (Inv_K13910_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13914_at B APIf ra empty) j -> Hat B APIf ra (Inv_K138f4_at B APIf ra empty) j.
Definition S_G04 : Prop := forall j : nat,
  Hat B APIf ra (Inv_K13950_at B APIf ra empty) j -> Hat B APIf ra (Inv_K139e8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13910_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13914_at B APIf ra empty) j.
Definition S_G05 : Prop := forall j : nat, Hat B APIf ra (Inv_K139e4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13950_at B APIf ra empty) j.
Definition S_G06 : Prop := forall j : nat, Hat B APIf ra (Inv_K13a80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K139e4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K139e8_at B APIf ra empty) j.
(* is_8819, check_ports, classify, match, latch. *)
Definition S_E01 : Prop := forall j : nat, Hat B APIf ra (Inv_K13a94_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13a80_at B APIf ra empty) j.
Definition S_E02 : Prop := forall j : nat, Hat B APIf ra (Inv_K13aa8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13a94_at B APIf ra empty) j.
Definition S_E03 : Prop := forall j : nat, Hat B APIf ra (Inv_K13af0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13aa8_at B APIf ra empty) j.
Definition S_E04 : Prop := forall j : nat, Hat B APIf ra (Inv_K13b64_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13af0_at B APIf ra empty) j.
Definition S_Q01 : Prop := forall j : nat, Hat B APIf ra (Inv_K13b80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13b64_at B APIf ra empty) j.
Definition S_Q02 : Prop := forall j : nat, Hat B APIf ra (Inv_K13b98_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13b80_at B APIf ra empty) j.
Definition S_Q03 : Prop := forall j : nat, Hat B APIf ra (Inv_K13ba8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13b98_at B APIf ra empty) j.
Definition S_Q04 : Prop := forall j : nat, Hat B APIf ra (Inv_K13bd8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ba8_at B APIf ra empty) j.
Definition S_Q05 : Prop := forall j : nat, Hat B APIf ra (Inv_K13c40_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13bd8_at B APIf ra empty) j.
Definition S_Q06 : Prop := forall j : nat, Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13c40_at B APIf ra empty) j.
Definition S_C01 : Prop := forall j : nat, Hat B APIf ra (Inv_K13cc0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j.
Definition S_C02 : Prop := forall j : nat, Hat B APIf ra (Inv_K13cf4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d0c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13cc0_at B APIf ra empty) j.
Definition S_C03 : Prop := forall j : nat,
  Hat B APIf ra (Inv_K13d38_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13cf4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13d0c_at B APIf ra empty) j.
Definition S_W01 : Prop := forall j : nat, Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j 0%nat -> Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d38_at B APIf ra empty) j.
Definition S_W02 : Prop := forall j i : nat, Hat2 B APIf ra (Inv_K13d58_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Definition S_W03 : Prop := forall j i : nat, Hat2 B APIf ra (Inv_K13d6c_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_K13d70_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_K13d58_at B APIf ra empty) j i.
Definition S_W04 : Prop := forall j i : nat,
  Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j (S i) -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_K13d6c_at B APIf ra empty) j i /\ Hat2 B APIf ra (Inv_K13d70_at B APIf ra empty) j i.
Definition S_C04 : Prop := forall j : nat, Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j.
Definition S_C05 : Prop := forall j : nat, Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j.
Definition S_C06 : Prop := forall j : nat, Hat B APIf ra (Inv_K13694_at B APIf ra empty) (S j) -> Hcut B APIf ra (Inv_K13db4 B APIf ra empty) -> Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j.
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K13dcc B APIf ra empty) -> Hcut B APIf ra (Inv_K13dd0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13db4 B APIf ra empty).
Definition S_X02 : Prop := Hcut B APIf ra (Inv_K13dcc B APIf ra empty) /\ Hcut B APIf ra (Inv_K13dd0 B APIf ra empty).

Definition seg_lemmas : Prop :=
  S_A02 /\ S_A03 /\
  S_R01 /\ S_R02 /\ S_R03 /\ S_R04 /\ S_R05 /\ S_R06 /\ S_R07 /\ S_R08 /\ S_R09 /\ S_R10 /\ S_R11 /\ S_R12 /\
  S_R13 /\ S_R14 /\ S_R15 /\ S_R16 /\ S_R17 /\ S_R18 /\ S_R19 /\ S_R20 /\ S_R21 /\ S_R22 /\ S_R23 /\ S_R24 /\
  S_P01 /\ S_P02 /\ S_P03 /\ S_P04 /\ S_P05 /\ S_P06 /\ S_P07 /\ S_P08 /\ S_P09 /\
  S_F01 /\ S_F02 /\ S_F03 /\ S_F04 /\ S_F05 /\ S_F06 /\ S_F07 /\ S_F08 /\ S_F09 /\ S_F10 /\
  S_I01 /\ S_I02 /\ S_G01 /\ S_G02 /\ S_G03 /\ S_G04 /\ S_G05 /\ S_G06 /\
  S_E01 /\ S_E02 /\ S_E03 /\ S_E04 /\ S_Q01 /\ S_Q02 /\ S_Q03 /\ S_Q04 /\ S_Q05 /\ S_Q06 /\
  S_C01 /\ S_C02 /\ S_C03 /\ S_W01 /\ S_W02 /\ S_W03 /\ S_W04 /\ S_C04 /\ S_C05 /\ S_C06 /\
  S_X01 /\ S_X02.

End Stmts.

(* ---- n >= 2^26: [0x131f8, 0x13234] then the branch to 0x13dd0 and the epilogue [0x13dd0, 0x13e0c] ---- *)
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
          F (Z_to_bv 64 0x131f8) fc None m (seg_rom rsegs)).
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

Lemma slot_ff_libk : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma slot_ff_delta : forall n b, @lib_delta LS n b = b.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma slot_ff_room : forall b n, @lib_room LS b n -> slot_room b.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  SR (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post B APIf ra g).
Proof.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (proj1 (proj2 FF)) as HRA.
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
        split; [exact (slot_ff_room b n Hroom)|]. split; [exact Hsp|]. exact Htp. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|]. exact Hres. }
    exact (SR_realizes (ms_segs B) _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes (ms_segs B) _ _ _ (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
             ltac:(rewrite Egn; exact HP0) HSink HRO Hres) HKg).
Qed.

End Bridge.

(* ---- The composition (slot-plan.md section 5) ---- *)
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
Hypothesis seg_G01 : S_G01 B APIf ra empty.
Hypothesis seg_G02 : S_G02 B APIf ra empty.
Hypothesis seg_G03 : S_G03 B APIf ra empty.
Hypothesis seg_G04 : S_G04 B APIf ra empty.
Hypothesis seg_G05 : S_G05 B APIf ra empty.
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


(* Past the last turn the loop cuts hold no state: b <= 6 (RB), j <= 255 (LI), i <= 10 (WB). *)
Lemma vac_K1330c : forall b, (6 < b)%nat -> Hat B APIf ra (Inv_K1330c_at B APIf ra empty) b.
Proof. intros b Hb g c (L & A & regs & mem & md & _ & _ & _ & Hb' & _). lia. Qed.

Lemma vac_K13694 : forall j, (255 < j)%nat -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof. intros j Hj g c (L & A & regs & mem & md & _ & _ & _ & Hj' & _). lia. Qed.

Lemma vac_K13d4c : forall j i, (10 < i)%nat -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof. intros j i Hi g c (phi & L & A & regs & mem & md & _ & _ & _ & _ & Hi' & _). lia. Qed.

(* W00: row i of row_of_block. *)
Lemma turn_rows : forall j i, Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j ->
  Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j (S i) -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof.
  intros j i Hd80 Hd7c HS.
  destruct (seg_W04 j i Hd80 HS Hd7c) as [Hd6c Hd70].
  exact (seg_W02 j i (seg_W03 j i Hd6c Hd70)).
Qed.

Lemma loop_rows : forall j, Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j -> forall i, Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof.
  intros j Hd80 Hd7c.
  assert (IND : forall k i, (11 <= i + k)%nat -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i).
  { induction k as [|k IH]; intros i Hk.
    - exact (vac_K13d4c j i ltac:(lia)).
    - destruct (Nat.lt_ge_cases 10 i) as [Hi|Hi]; [exact (vac_K13d4c j i Hi)|].
      exact (turn_rows j i Hd80 Hd7c (IH (S i) ltac:(lia))). }
  intros i. exact (IND 11%nat i ltac:(lia)).
Qed.

(* F00: frame turn j (F01 .. C06, W00 inside). *)
Lemma turn_frames : forall j, Hcut B APIf ra (Inv_K13db4 B APIf ra empty) -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) (S j) -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof.
  intros j Hdb4 HS.
  pose proof (seg_C06 j HS Hdb4) as Hd98.
  pose proof (seg_C05 j Hd98) as Hd8c.
  destruct (seg_C04 j Hd8c) as [Hd7c Hd80].
  pose proof (loop_rows j Hd80 Hd7c 0%nat) as Hd4c.
  pose proof (seg_W01 j Hd4c Hd80) as Hd38.
  destruct (seg_C03 j Hd38 Hd7c) as [Hcf4 Hd0c].
  pose proof (seg_C02 j Hcf4 Hd0c) as Hcc0.
  pose proof (seg_C01 j Hcc0) as Hca0.
  pose proof (seg_Q06 j Hca0) as Hc40.
  pose proof (seg_Q05 j Hc40) as Hbd8.
  pose proof (seg_Q04 j Hbd8 Hca0) as Hba8.
  pose proof (seg_Q03 j Hba8) as Hb98.
  pose proof (seg_Q02 j Hb98) as Hb80.
  pose proof (seg_Q01 j Hb80) as Hb64.
  pose proof (seg_E04 j Hb64) as Haf0.
  pose proof (seg_E03 j Haf0) as Haa8.
  pose proof (seg_E02 j Haa8) as Ha94.
  pose proof (seg_E01 j Ha94 Hca0) as Ha80.
  destruct (seg_G06 j Ha80) as [H9e4 H9e8].
  pose proof (seg_G05 j H9e4) as H950.
  destruct (seg_G04 j H950 H9e8) as [H910 H914].
  pose proof (seg_G03 j H910 H914) as H8f4.
  pose proof (seg_G02 j H8f4) as H8d8.
  destruct (seg_G01 j H8d8) as [H8c4 H8c8].
  pose proof (seg_I02 j H8c4) as H874.
  pose proof (seg_I01 j H874 H8c8) as H830.
  pose proof (seg_F10 j H830) as H7f8.
  pose proof (seg_F09 j H7f8) as H7ec.
  pose proof (seg_F08 j H7ec) as H7d8.
  pose proof (seg_F07 j H7d8) as H7c8.
  destruct (seg_F06 j H7c8) as [H748 H74c].
  pose proof (seg_F04 j H748) as H734.
  pose proof (seg_F05 j H74c H7c8) as H70c.
  pose proof (seg_F03 j H70c) as H6f8.
  pose proof (seg_F02 j H6f8 H734) as H6d4.
  exact (seg_F01 j H6d4).
Qed.

Lemma loop_frames : Hcut B APIf ra (Inv_K13db4 B APIf ra empty) -> forall j, Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof.
  intros Hdb4.
  assert (IND : forall k j, (256 <= j + k)%nat -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j).
  { induction k as [|k IH]; intros j Hk.
    - exact (vac_K13694 j ltac:(lia)).
    - destruct (Nat.lt_ge_cases 255 j) as [Hj|Hj]; [exact (vac_K13694 j Hj)|].
      exact (turn_frames j Hdb4 (IH (S j) ltac:(lia))). }
  intros j. exact (IND 256%nat j ltac:(lia)).
Qed.

(* R00: round-trip turn b (R05 .. R22). H(K13408) is the b = 6 arm and needs only turn 7, which holds no
   state; H(K134bc) (b = 5) needs turn 6 and H(K13464) (b = 0) needs turn 1: both are H(K1330c)[b + 1]. *)
Lemma rt_K13408 : Hcut B APIf ra (Inv_K13524 B APIf ra empty) -> Hcut B APIf ra (Inv_K13408 B APIf ra empty).
Proof.
  intros H524. pose proof seg_R10 as [_ R10b].
  exact (R10b (seg_R12 6%nat (seg_R21 6%nat (seg_R22 6%nat (vac_K1330c 7%nat ltac:(lia)) H524)))).
Qed.

Lemma turn_rt : forall b, Hcut B APIf ra (Inv_K13524 B APIf ra empty) -> Hat B APIf ra (Inv_K1330c_at B APIf ra empty) (S b) -> Hat B APIf ra (Inv_K1330c_at B APIf ra empty) b.
Proof.
  intros b H524 HS.
  pose proof seg_R10 as [R10a _].
  pose proof (seg_R22 b HS H524) as H51c.
  pose proof (seg_R21 b H51c) as H514.
  pose proof (seg_R12 b H514) as H420.
  pose proof (seg_R20 b H514) as H4e8.
  pose proof (R10a b H420) as H3cc.
  pose proof (rt_K13408 H524) as H408.
  assert (H4bc : b = 5%nat -> Hcut B APIf ra (Inv_K134bc B APIf ra empty)).
  { intros ->. exact (seg_R18 (seg_R19 H514)). }
  assert (H464 : b = 0%nat -> Hcut B APIf ra (Inv_K13464 B APIf ra empty)).
  { intros ->. exact (seg_R14 (seg_R15 (seg_R16 (seg_R17 H514)))). }
  pose proof (seg_R11 b (fun _ => H408) H4bc H4e8) as H3d4.
  pose proof (seg_R13 b H464 H4e8) as H428.
  pose proof (seg_R09 b H3cc H3d4 H428) as H398.
  pose proof (seg_R08 b H398) as H388.
  pose proof (seg_R07 b H388) as H374.
  pose proof (seg_R06 b H374 H51c) as H330.
  exact (seg_R05 b H330).
Qed.

Lemma loop_rt : Hcut B APIf ra (Inv_K13524 B APIf ra empty) -> forall b, Hat B APIf ra (Inv_K1330c_at B APIf ra empty) b.
Proof.
  intros H524.
  assert (IND : forall k b, (7 <= b + k)%nat -> Hat B APIf ra (Inv_K1330c_at B APIf ra empty) b).
  { induction k as [|k IH]; intros b Hk.
    - exact (vac_K1330c b ltac:(lia)).
    - destruct (Nat.lt_ge_cases 6 b) as [Hb|Hb]; [exact (vac_K1330c b Hb)|].
      exact (turn_rt b H524 (IH (S b) ltac:(lia))). }
  intros b. exact (IND 7%nat b ltac:(lia)).
Qed.

(* Plan section 5, steps 1-5. *)
Lemma slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  pose proof seg_X02 as [Hdcc Hdd0].
  pose proof (seg_X01 Hdcc Hdd0) as Hdb4.
  pose proof (loop_frames Hdb4 0%nat) as H694.
  pose proof (seg_P09 H694 Hdb4) as H660.
  pose proof (seg_P08 H660) as H648.
  pose proof (seg_P07 H648) as H638.
  pose proof (seg_P06 H638) as H624.
  pose proof (seg_P05 H624) as H614.
  pose proof (seg_P04 H614) as H5f0.
  pose proof (seg_P03 H5f0) as H5c0.
  pose proof (seg_P02 H5c0) as H5b0.
  pose proof (seg_P01 H5b0) as H598.
  pose proof (seg_R24 H598) as H58c.
  pose proof (seg_R23 H58c H598) as H524.
  pose proof (loop_rt H524 0%nat) as H30c.
  pose proof (seg_R04 H30c) as H2e4.
  pose proof (seg_R03 H2e4) as H2d4.
  pose proof (seg_R02 H2d4) as H2ac.
  pose proof (seg_R01 H2ac) as H2a0.
  pose proof (seg_A03 H2a0 H598) as H288.
  pose proof (seg_A02 0 H288 H598) as H24c.
  exact (seg_A01 B APIf ra empty FF H24c Hdd0).
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
