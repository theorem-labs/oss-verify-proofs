(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout R_small D_kit X_atexit X_gdefs X_unreg.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (bi : byte),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SHW_HI <= lo ->
  rw_cells bsegs m 0xbd19c0 [C1 bi] ->
  rw_cells bsegs m 0xbd19e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ee498) fc None m (seg_rom bsegs)).
Proof.
  intros until bi. intros ST LO LOLO BI CL MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x1ee4bc%Z. cbn beta. lstep.
  if_cases Hb.
  - steps_to 0x1ee598%Z. release_frame FR ST (bv_unsigned sp). astep. unfold dtor_post. sys_finish.
  - steps_to 0x1ee598%Z. release_frame FR ST (bv_unsigned sp). astep. unfold dtor_post. sys_finish.
Qed.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x69bcd0, 0x69bcd1); (0x69bc80, 0x69bc88); (0x69cbf0, 0x69cbf8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (flag dso : word) (bi : byte),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> SHW_HI <= lo ->
  ro_cells bsegs m 0x566f58 [C8 (Z_to_bv 64 0x1eef1c); C8 (Z_to_bv 64 0x194a94); C8 (Z_to_bv 64 0x1ee498)] ->
  rw_cells bsegs m 0xbd19c0 [C1 bi] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0xbd19e0 [C1 (Z_to_bv 8 0)] ->               (* [comment removed for export] *)
  ro_cells bsegs m 0x5de7d0 [C8 (Z_to_bv 64 0x566f70); C8 (Z_to_bv 64 0x566f58)] ->
  ro_cells bsegs m 0x5dc808 [C8 (Z_to_bv 64 0x553640); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x5df840 [C8 dso] ->
  ro_cells bsegs m 0x5de788 [C8 (Z_to_bv 64 0x5e2fa0); C8 (Z_to_bv 64 0x69bc60)] ->
  rw_cells bsegs m 0x69bcd0 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x69bc80 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x69cb50 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x69cbf0 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x69f338 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x6a0018 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x69eb9c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x730ee0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x5dfa70 [C8 (Z_to_bv 64 0x55f010)] ->
  stk bsegs m SHW_LO SHW_HI -> stk bsegs m ODR_LO ODR_HI ->
  gtab_at m ->
  mem_inv bsegs m ->
  evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x553710) fc None m (seg_rom bsegs)).
Proof.
  intros until bi. intros ST LO LOLO FA BI CL GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SCW OW GDS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x69bcd0, 0x69bcd1); (0x69bc80, 0x69bc88); (0x69cbf0, 0x69cbf8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  steps_to 0x1ee498%Z.
  call dtor_spec; [rewrite EU32; exact ST| lia| lia| exact BI| exact CL| assumption|].
  rewrite EU32 in POST. rename POST into ST.
  steps_to 0x194a94%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x194b28%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0x1eef1c%Z.
  carve_frame 16%nat ST.
  steps_to 0x1a54c8%Z.
  carve_frame 16%nat ST.
  steps_to 0x1a4e90%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SCW| exact OW| exact GDS1| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x1a5510%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x1eef54%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x553758%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
