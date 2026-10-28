(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small F_memset D_kit X_atexit X_gdefs X_unregi X_unregl X_psglob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition unreg_got (m : mem) : Prop :=
  ro_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)]
  /\ ro_cells asegs m 0x5a45a8 [C8 (Z_to_bv 64 0x6fe668); C8 (Z_to_bv 64 0x66a338); C8 (Z_to_bv 64 0x66cb38);
                               C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820);
                               C8 (Z_to_bv 64 0x5a77f0)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x66a3f0, 0x66a3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0x5aaa60 -> a1 = Z_to_bv 64 GT_N ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> SHW_HI <= lo ->
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
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a9ed8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SCW OW GDS MI. unfold GT_N.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x66a3f0, 0x66a3f8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x1a9f80%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x1aa094%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop 12200%nat 12200); [reflexivity| unfold GT_N; lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SCW| exact OW| assumption|].
  xsteps_to 0x1c4550%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk asegs ?mm SHW_LO SHW_HI |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x1aa2f0%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x1aa3a4%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
