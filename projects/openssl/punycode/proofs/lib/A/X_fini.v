(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small D_kit X_atexit X_gdefs X_unreg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x66d4d0, 0x66d4d1); (0x66d480, 0x66d488); (0x66e3f0, 0x66e3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (flag dso : word),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> SHW_HI <= lo ->
  ro_cells asegs m 0x532838 [C8 (Z_to_bv 64 0x1f3428); C8 (Z_to_bv 64 0x199b38); C8 (Z_to_bv 64 0x20b954)] ->
  rw_cells asegs m 0xba3660 [C1 (Z_to_bv 8 0)] ->                          (* [comment removed for export] *)
  ro_cells asegs m 0x5aa530 [C8 (Z_to_bv 64 0x532850); C8 (Z_to_bv 64 0x532838)] ->
  ro_cells asegs m 0x5a8568 [C8 (Z_to_bv 64 0x51ef1c); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x5ab5a0 [C8 dso] ->
  ro_cells asegs m 0x5aa4e8 [C8 (Z_to_bv 64 0x5aea40); C8 (Z_to_bv 64 0x66d480)] ->
  rw_cells asegs m 0x66d4d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x66d480 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0x66e350 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x66e3f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x670b38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x671818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x67039c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x7026e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x5ab7d0 [C8 (Z_to_bv 64 0x52a8ec)] ->
  stk asegs m SHW_LO SHW_HI -> stk asegs m ODR_LO ODR_HI ->
  gtab_at m ->
  mem_inv asegs m ->
  evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51efec) fc None m (seg_rom asegs)).
Proof.
  intros until dso. intros ST LO LOLO FA BI GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SCW OW GDS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x66d4d0, 0x66d4d1); (0x66d480, 0x66d488); (0x66e3f0, 0x66e3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  steps_to 0x20b954%Z.
  carve_frame 48%nat ST.
  steps_to 0x20ba48%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x199b38%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x199bcc%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0x1f3428%Z.
  carve_frame 16%nat ST.
  steps_to 0x1aa56c%Z.
  carve_frame 16%nat ST.
  steps_to 0x1a9f34%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SCW| exact OW| exact GDS1| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x1aa5b4%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x1f3454%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x51f034%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
