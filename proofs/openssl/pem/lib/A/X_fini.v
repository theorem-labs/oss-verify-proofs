(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small D_kit X_atexit X_gdefs X_unreg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (bi : byte),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SHW_HI <= lo ->
  rw_cells asegs m 0xb9f1c0 [C1 bi] ->
  rw_cells asegs m 0xb9f1e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f34fc) fc None m (seg_rom asegs)).
Proof.
  intros until bi. intros ST LO LOLO BI CL MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x1f3520%Z. cbn beta. lstep.
  if_cases Hb.
  - steps_to 0x1f35fc%Z. release_frame FR ST (bv_unsigned sp). astep. unfold dtor_post. sys_finish.
  - steps_to 0x1f35fc%Z. release_frame FR ST (bv_unsigned sp). astep. unfold dtor_post. sys_finish.
Qed.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x6694d0, 0x6694d1); (0x669480, 0x669488); (0x66a3f0, 0x66a3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (flag dso : word) (bi : byte),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> SHW_HI <= lo ->
  ro_cells asegs m 0x52e860 [C8 (Z_to_bv 64 0x1f34cc); C8 (Z_to_bv 64 0x199adc); C8 (Z_to_bv 64 0x1f34fc)] ->
  rw_cells asegs m 0xb9f1c0 [C1 bi] ->                           (* [comment removed for export] *)
  rw_cells asegs m 0xb9f1e0 [C1 (Z_to_bv 8 0)] ->               (* [comment removed for export] *)
  ro_cells asegs m 0x5a6548 [C8 (Z_to_bv 64 0x52e878); C8 (Z_to_bv 64 0x52e860)] ->
  ro_cells asegs m 0x5a4588 [C8 (Z_to_bv 64 0x51af44); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x5a75c0 [C8 dso] ->
  ro_cells asegs m 0x5a6500 [C8 (Z_to_bv 64 0x5aaa60); C8 (Z_to_bv 64 0x669460)] ->
  rw_cells asegs m 0x6694d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x669480 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x66a3f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)] ->
  stk asegs m SHW_LO SHW_HI -> stk asegs m ODR_LO ODR_HI ->
  gtab_at m ->
  mem_inv asegs m ->
  evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51b014) fc None m (seg_rom asegs)).
Proof.
  intros until bi. intros ST LO LOLO FA BI CL GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SCW OW GDS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x6694d0, 0x6694d1); (0x669480, 0x669488); (0x66a3f0, 0x66a3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  steps_to 0x1f34fc%Z.
  call dtor_spec; [rewrite EU32; exact ST| lia| lia| exact BI| exact CL| assumption|].
  rewrite EU32 in POST. rename POST into ST.
  steps_to 0x199adc%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x199b70%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0x1f34cc%Z.
  carve_frame 16%nat ST.
  steps_to 0x1aa510%Z.
  carve_frame 16%nat ST.
  steps_to 0x1a9ed8%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SCW| exact OW| exact GDS1| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x1aa558%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x1f34f8%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x51b05c%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
