(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Z_dview Z_drep Z_dkit Z_trees_iface Z_adler32 F_memset Z_dinit_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Definition Z_DRESETKEEP : Z := 0x16e4c.
Definition Z_DRESET : Z := 0x168c4.
Definition Z_DRESET_STACK : Z := 192.
Definition zs_raw (As ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) : list cell :=
  zs_pub ni ai ti no ao to p1 p2 ++ [C8 msg; C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 opq; C4 dt; CB 4 p3; C8 adl; C8 resv].
Ltac merge44 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C4 ?a :: C4 ?b :: ?post =>
      let H' := fresh in pose proof (cells_merge44 m A pre a b post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.
Ltac split8 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C8 (Z_to_bv 64 0) :: ?post =>
      let H' := fresh in pose proof (cells_split8_0 m A pre post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.
Lemma land7_of_mod8 : forall a, a mod 8 = 0 -> Z.land a 7 = 0.
Proof. intros a H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.
Ltac al8m X := rewrite (land7_of_mod8 X) by (Z.div_mod_to_equations; lia).
Definition rk1_fields (x : deflate_state) : deflate_state :=
  set_prev_length (set_lookahead (set_match_available (set_match_length (set_block_start x (ds_strstart x mod 2 ^ 32)) 2) 0) 0) 2.
Definition RK1 (s : deflate_state) : deflate_state := rk1_fields (tr_init (RK0 s)).
Lemma LM_rk1_fields : forall x, LM (rk1_fields x) = LM x.
Proof. intros x. destruct x. reflexivity. Qed.
Lemma LM_RK1 : forall s, LM (RK1 s) = LM (tr_init (RK0 s)).
Proof. intros s. apply LM_rk1_fields. Qed.
Lemma tr_init_matches : forall x, ds_matches (tr_init x) = 0.
Proof. intros x. reflexivity. Qed.
Section RESET.
  Hypothesis HTRI : tr_init_stmt.
  Definition dresetkeep_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : dlay) (s : deflate_state) (ni ai no ao : Z) (p1 p2 : list byte) (opq : word) (p3 : list byte) (resv : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells usegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (RK1 s).
  Definition dreset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : dlay) (s : deflate_state) (ni ai no ao : Z) (p1 p2 : list byte) (opq : word) (p3 : list byte) (resv : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells usegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (LM (tr_init (RK0 s))).
End RESET.
