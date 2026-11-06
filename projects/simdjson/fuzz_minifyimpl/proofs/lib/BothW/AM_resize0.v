(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes ARep AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_annotw AM_resize.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxr P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Lemma aresize_null0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp + 16 <= 2^47 ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 0 ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (aresize_nop_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVRESIZE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH GOT SHB -> -> VEC VSH V8 VBLK RIMG RSTK RV RVS.
  unfold AVRESIZE. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  unfold aresize_nop_post.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells bsegs mm (shad V) _ |- _ =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as HR0; rewrite Z.add_0_r in HR0; unfold bxr in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSHx) as HR1; unfold bxr in SHV8; rewrite <- SHV8 in HR1; box SHV8 end
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  try replace (0 - 0) with 0 by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                      (* [comment removed for export] *)
  finish.
Qed.
End CANSEC1.
