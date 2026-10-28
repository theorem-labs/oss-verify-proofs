(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition m2sb_entry := 0x3f4d8%Z.

End CANSEC1.
Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  end.

Section CANSEC2. Context {rc : runConstT}.
Definition m2sb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t1 t2 t3 t4 t5 t6 : word) (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (shad (bv_unsigned a0))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Lemma m2sb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv bsegs m ->
  rt_got m -> rt_shbase m -> rt_layout m ->
  ((bv_unsigned a0 + 1 <= KLOW) \/ (KHIGH <= bv_unsigned a0 /\ bv_unsigned a0 + 1 <= KEND))%Z ->
  rng_aimg RNG ->
  evtF bsegs RNG (m2sb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t1 t2 t3 t4 t5 t6 a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f4d8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI GOT SHB LAY APP RI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold KLOW, KHIGH, KEND in APP.
  do 5 zstep. fold_lits. zsimp. do 3 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep. finish.
  - do 7 zstep. fold_lits. zsimp. zstep.
    if_cases K2; zify_cond K2. 2: { exfalso; lia. }
    do 6 zstep.
    if_cases K3; zify_cond K3. { exfalso; lia. }
    zstep.
    if_cases K4; zify_cond K4. { exfalso; lia. }
    do 3 zstep.
    finish.
Qed.
End CANSEC2.
