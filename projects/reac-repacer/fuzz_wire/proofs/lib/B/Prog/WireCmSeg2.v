(* WireCmSeg2: two straight-line pieces of the image-B walk of check_meter (fuzz_wire.asan-ubsan 0x8016c), the
   footprint runs (lib/Lib/ExecF.v evtF) of lib/B/Prog/WireCmIface.v cm_seg2a_stmt and cm_seg2c_stmt, stepped by
   lib/Lib/StepF.v. The form, and the register and literal helpers, are those of reac-repacer/fuzz_uci's
   lib/B/Prog/UciCvBSegs.v (recipes commit 0295462466b2):
     cm_seg2a  CM_RET_SM (0x801dc) -> CM_PRE (0x8026c): `mv s2, a0`, `j`, `mv s6, s2`, `bnez s2` at 0x801ec taken
               (Fa >= 4096); the frame header (0x41b58ab3, 0x18cc3, 0x8016c) by the three `sd` at 0x8022c .. 0x80234;
               s7 := (Fa >> 3) + s8 (`srli` at 0x80218, `add` at 0x8023c), which is shadow_addr Fa; the frame's 8
               shadow bytes by the `sb` at 0x80240 .. 0x80260; a0 := 14 and `sd s6, 24(s1)` at 0x80268.
     cm_seg2c  CM_CTR (0x80328) -> the `jal rp_meter_counter` at 0x8034c: s5 := Fa + 32, `sb` 2 at 0x80330 into
               shadow_addr Fa + 4, `sh` 0xa5c3 at 0x8033c into Fa + 32, the three argument moves, `jal`.
   Each store is turned into a cell update by StepF's solve_store, which needs the store address and the base of a
   rw_cells premise to be the same expression: shadow_addr Fa is named SA before the walk, and the s7 that the
   `srli` / `add` pair computes is set to Z_to_bv 64 SA once the `add` has run. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The bytes of a one-cell rw_cells fact. *)
Lemma cm_rw1_bytes : forall m A c, rw_cells rsegs m A [c] -> bytes_at rsegs m A (cbytes c).
Proof. intros m A c [[_ H] _]. cbn [cells_bytes] in H. rewrite app_nil_r in H. exact H. Qed.

(* UciCvBSegs.v cv_regs, cv_usub, cv_shift, cv_w, cv_memF, cv_lit, cv_lits, with this file's names. *)
Ltac cm_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cm_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cm_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cm_w := cm_shift; cm_usub; cm_shift; cm_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cm_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: each proof first computes every closed WireCmIface name of its goal. *)
Ltac cm_lit X := let v := eval vm_compute in X in change X with v.
Ltac cm_lits :=
  repeat match goal with
  | |- context [CM_RET_SM] => cm_lit CM_RET_SM
  | |- context [CM_PRE] => cm_lit CM_PRE
  | |- context [CM_CTR] => cm_lit CM_CTR
  | |- context [CM_RET_LEAF] => cm_lit CM_RET_LEAF
  | |- context [CM_LEAF] => cm_lit CM_LEAF
  | |- context [CM_AT ?o] => cm_lit (CM_AT o)
  | |- context [CM_ENTRY] => cm_lit CM_ENTRY
  end.

(* ---- cm_seg2a: CM_RET_SM -> CM_PRE ---- *)
Lemma cm_seg2a : cm_seg2a_stmt.
Proof.
  unfold cm_seg2a_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m Fa
    hj sj xj HF HFs HS1 HSD HSs RH RS RX RGH RGS RGX.
  cm_lits.
  pose proof (bv_unsigned_in_range 64 s1) as Rs1. unfold bv_modulus in Rs1. change (2 ^ Z.of_N 64) with (2^64) in Rs1.
  pose proof (munch_refl [(Fa, Fa + 24); (shadow_addr Fa, shadow_addr Fa + 8); (bv_unsigned s1 + 24, bv_unsigned s1 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UF : bv_unsigned (Z_to_bv 64 Fa) = Fa) by (apply unsigned_lit; lia).
  assert (SAr : shadow_addr Fa = Fa / 8 + 2147450880) by reflexivity.
  remember (shadow_addr Fa) as SA eqn:ESA.
  (* 0x801dc `mv s2, a0`; `j 0x801e8`; `mv s6, s2`; 0x801ec `bnez s2` (taken: Fa >= 4096) *)
  do 3 step. step. if_true.
  (* 0x8020c .. 0x80228: `lui a0`, `auipc a1`, `auipc a2`, `srli s7, s6, 3`, `li a3, -13`, `addiw a0`, `addi a1`,
     `addi a2` *)
  do 8 step.
  (* 0x8022c .. 0x80234: the frame header into [Fa, Fa + 24) *)
  do 3 step.
  (* 0x80238 `li a0, -8`; 0x8023c `add s7, s7, s8`: s7 = (Fa >> 3) + ASAN_K = SA *)
  do 2 step.
  setreg 23 (Z_to_bv 64 SA)
    ltac:(f_equal; rewrite ?(unsigned_lit Fa) by lia; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8;
          try unfold ASAN_K; lia).
  (* 0x80240 .. 0x8024c: 0xf8, 0xf3 x3 into SA + 4 .. SA + 7; 0x80250 `li a0, -15`; 0x80254 .. 0x80260: 0xf1 into
     SA .. SA + 3 *)
  do 4 step. step. do 4 step.
  (* 0x80264 `li a0, 14`; 0x80268 `sd s6, 24(s1)` *)
  do 2 step.
  cm_memF ltac:(fun mm => apply evtF_done; exists mm).
  split; [|split; assumption].
  f_equal; cm_regs; try cm_w.
Qed.

(* ---- cm_seg2c: CM_CTR -> the `jal rp_meter_counter` at 0x8034c ---- *)
Lemma cm_seg2c : cm_seg2c_stmt.
Proof.
  unfold cm_seg2c_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fa
    kj cj HF HF64 HSD RK RC RGK RGC.
  cm_lits.
  pose proof (munch_refl [(shadow_addr Fa + 4, shadow_addr Fa + 5); (Fa + 32, Fa + 34)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SAr : shadow_addr Fa = Fa / 8 + 2147450880) by reflexivity.
  remember (shadow_addr Fa) as SA eqn:ESA.
  (* 0x80328 `addi s5, s6, 32`; `li a0, 2`; 0x80330 `sb a0, 4(s7)` *)
  do 3 step.
  (* 0x80334 `lui a0, 0xa`; `addi a0, a0, 1475`; 0x8033c `sh a0, 0(s5)` *)
  do 3 step.
  (* 0x80340 .. 0x80348 `mv a0, s3`, `mv a1, s4`, `mv a2, s5`; 0x8034c `jal rp_meter_counter` *)
  do 4 step.
  cm_memF ltac:(fun mm => apply evtF_done; exists mm).
  match goal with
  | H1 : rw_cells rsegs ?mm (SA + 4) _, H2 : rw_cells rsegs ?mm (Fa + 32) _ |- _ =>
      apply cm_rw1_bytes in H1; apply cm_rw1_bytes in H2
  end.
  split; [|split; [exact MU|split; [exact WM|split]]].
  - f_equal; cm_regs; try cm_w.
  - assumption.
  - assumption.
Qed.
