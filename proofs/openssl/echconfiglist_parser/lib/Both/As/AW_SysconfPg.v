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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition ALIBCPGSZ : Z := 0xc01f50.   (* [comment removed for export] *)
Definition AGOT_SSP  : Z := 0x5e9798.   (* [comment removed for export] *)
Definition ASSPGUARD : Z := 0xc01cd0.   (* [comment removed for export] *)

Definition sysconf30_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) (g : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 4096) g g a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).
End HCW.

Section Sysconf.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (g : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 544 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz 30.
  Hypothesis CPG : rw_cells asegs m ALIBCPGSZ [C8 (wz 4096)].
  Hypothesis CGOT : rw_cells asegs m AGOT_SSP [C8 (wz ASSPGUARD)].
  Hypothesis CGRD : rw_cells asegs m ASSPGUARD [C8 g].

  Theorem sysconf30_spec :
    evt asegs (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo g)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x55d7ac) fc None m (seg_rom asegs)).
  Proof.
    subst a0. unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, wz in *. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. carve_frame 544%nat ST.
    match type of FR with context [CB 544 ?j] => remember j as J eqn:EJ in FR; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 544 J [] [512;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR end.
    repeat match type of FR with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in FR end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. clear - K; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End Sysconf.

