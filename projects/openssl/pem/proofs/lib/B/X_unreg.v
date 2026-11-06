(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout R_small F_memset D_kit X_atexit X_gdefs X_unregi X_unregl X_psglob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition unreg_got (m : mem) : Prop :=
  ro_cells bsegs m 0x5dc818 [C8 (Z_to_bv 64 0x72ede0)]
  /\ ro_cells bsegs m 0x5dc828 [C8 (Z_to_bv 64 0x730e68); C8 (Z_to_bv 64 0x69cb38); C8 (Z_to_bv 64 0x69f338);
                               C8 (Z_to_bv 64 0x6a0028); C8 (Z_to_bv 64 0x6a0030); C8 (Z_to_bv 64 0x6a0020);
                               C8 (Z_to_bv 64 0x5dfa70)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x69cbf0, 0x69cbf8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0x5e2fa0 -> a1 = Z_to_bv 64 GT_N ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> SHW_HI <= lo ->
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
  evt bsegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a4e90) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SCW OW GDS MI. unfold GT_N.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x69cbf0, 0x69cbf8);
              (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x1a4f38%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x1a504c%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop 11827%nat 11827); [reflexivity| unfold GT_N; lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SCW| exact OW| assumption|].
  xsteps_to 0x1bf508%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk bsegs ?mm SHW_LO SHW_HI |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x1a52a8%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x1a535c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
