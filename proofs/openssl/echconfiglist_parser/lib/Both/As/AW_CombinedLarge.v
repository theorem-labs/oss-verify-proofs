(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase AW_LargeAlloc1 AllocTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition combined_large_seg1_post (sp gp tp t0 t1 t2 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size : Z) (s0 ra : word) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x19b704) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz 8) s1 (wz (AINST + 64)) (wz (AINST + 688)) (wz size) (wz 8) (wz (AINST + 64)) (wz 0x10000) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b934) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section CSeg1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 8.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41.

  Theorem combined_large_seg1 :
    evt asegs (combined_large_seg1_post sp gp tp t0 t1 t2 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size s0 ra)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b65c) fc None m (seg_rom asegs)).
  Proof.
    unfold AINST in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a0 a2 a3. unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. do 6 step.
    step. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
    replace (Z.b2z (size <? 1)) with 0 by (rewrite zb_b2z_if; destruct (Z.ltb_spec size 1); lia).
    step. rewrite ?(unsigned_lit 0), ?Z.add_0_r by lia.
    step. rewrite (unsigned_lit size), zb_lxor_ones by lia.
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step.
    apply evt_done. unfold combined_large_seg1_post, AINST. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
  Qed.
End CSeg1.

Definition combined_large_seg2_post (sp gp tp t0 t1 t2 a0 a2 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) (s0 s1 s2 s3 s4 ra : word) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 9) a2 (wz 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section CSeg2.
  Variables (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0v s1v s2v s3v s4v rav : word) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -48).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp. Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

  Theorem combined_large_seg2 :
    evt asegs (combined_large_seg2_post sp gp tp t0 t1 t2 a0 a2 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s0v s1v s2v s3v s4v rav)
      (MS (mkR (wz 0x19b704) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b704) fc None m (seg_rom asegs)).
  Proof.
    acb.
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia).
    destruct SPQ as [spq SPQ].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. do 6 step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End CSeg2.

End HCW.

