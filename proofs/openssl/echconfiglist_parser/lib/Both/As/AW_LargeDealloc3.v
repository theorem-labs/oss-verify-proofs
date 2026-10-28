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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_LargeAlloc1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition dealloc3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Dealloc3.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (t0 t1 t2 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j16 : list byte).
  Variables (lo a msz TSD CTX TH : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -48).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 80 <= bv_unsigned sp.
  Hypothesis MSZ : 0 <= msz < 2^47.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra].

  Theorem dealloc3 :
    evt asegs (dealloc3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR (wz 0x1d3194) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz msz) (wz 0) (wz 0) (wz msz) a2 a3 a4 a5 a6 (wz 215)
               (wz a) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1914) fc None m (seg_rom asegs)).
  Proof.
    pose proof ENV as ENV0. open_senv ENV. pose proof TPR as R; destruct R as [TPR']. unfold AIMG_TOP in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. step. step.
    apply (rw_cells_split_CB asegs _ _ [] 16 j16 [C8 s2; C8 s1; C8 s0; C8 ra] [12;4]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?k (take ?i ?l)] => let X := fresh "jk" in remember (take i l) as X in FR end.
    repeat match type of FR with context [CB ?k (drop ?i ?l)] => let X := fresh "jk" in remember (drop i l) as X in FR end.
    repeat match goal with H' : _ = take _ _ |- _ => clear H' | H' : _ = drop _ _ |- _ => clear H' end.
    st1. step. step.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. clear - K; try acb. lia. } clear K.
    step. replace (v_sltu (Z_to_bv 64 (-4096)) (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step.
    (* [comment removed for export] *)
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold dealloc3_post. do 16 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End Dealloc3.

End HCW.

