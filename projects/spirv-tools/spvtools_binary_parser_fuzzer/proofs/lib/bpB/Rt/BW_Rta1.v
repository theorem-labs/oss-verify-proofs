(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BllocWalkKit BW_DepotFrame BW_Leaves BW_Efs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocPerfKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.

Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition rta_head_post (ra sp gp tp s0 s1 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R rbeg FAB c CH nf n : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 : word) m' (j16 : list byte),
    ms' = MS (mkR (wz 0x9524c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz AINST) (wz R) (wz rbeg) (wz (nf + n)) a4 a5 a6 a7
                  (wz c) a1 (wz AINST) (wz n) (wz CH) (wz (nf + n)) (wz (2^61)) (wz FAB) (wz (2^60 + 2^20 - 1)) (wz (2^60)) t3 t4 t5 t6)
             F (Z_to_bv 64 0x95410) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (R, R + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 16 j16; C8 (wz (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' R [C8 (wz kWriterLock)].

Section Head.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo SB ARI c CH nf n : Z).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 128 <= bv_unsigned sp.
  Hypothesis Ha3 : a3 = wz c. Hypothesis Ha4 : a4 = wz CH. Hypothesis Ha5 : a5 = wz n.
  Hypothesis CR : 1 <= c < kNumClasses. Hypothesis NFR : 0 <= nf /\ nf + n < 2^32. Hypothesis NNR : 0 <= n. Hypothesis CHR : 0 <= CH < 2^64.
  Hypothesis ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0.
  Hypothesis SBR : AHI_LO <= SB /\ SB + 2^37 <= aceil /\ SB mod 4096 = 0.
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0)].
  Hypothesis IRI : rw_cells asegs m (AINST + 48) [C8 (wz ARI)].
  Hypothesis RI0 : rw_cells asegs m R [C8 (wz 0)].
  Hypothesis RNF : rw_cells asegs m (R + 16) [C8 (wz nf)].

  Theorem rta_head :
    evt asegs (rta_head_post ra sp gp tp s0 s1 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R (SB + c * 2^32) (SB + c * 2^32 + kFreeArrayOffset) c CH nf n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz AINST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x950e8) fc None m (seg_rom asegs)).
Proof.
    unfold AHI_LO, kNumClasses, REGIONINFO_SIZE, AINST, kFreeArrayOffset in *. subst a3 a4 a5.
    change (1628632 + 32) with 1628664 in ISB. change (1628632 + 48) with 1628680 in IRI.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (ARI + 128 * c, ARI + 128 * c + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 128%nat ST. spill_frame ltac:(do 13 step).
    (* [comment removed for export] *)
    do 22 step.
    rewrite (unsigned_lit c) by (clear - CR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 7), (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    change (2^7) with 128. replace (ARI + c * 128) with R by (subst R; clear; lia).
    (* [comment removed for export] *)
    step. step. st1. do 6 step.
    if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    assert (AL8 : R mod 8 = 0) by (subst R; clear - ARIR; try acb; Z.div_mod_to_equations; lia).
    assert (ALR : 0 <= R < 2^64) by (subst R; clear - ARIR CR; try acb; lia).
    astep.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    astep. fix_lit_store.
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    apply evt_done. unfold rta_head_post. do 9 eexists.
    split. { change (2^61) with 2305843009213693952. change (2^60 + 2^20 - 1) with 1152921504607895551. change (2^60) with 1152921504606846976. reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. unfold kWriterLock, wz. change (2^60) with 1152921504606846976. eassumption.
  Qed.
End Head.

End HCW2.

