(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memset ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition CM_RA : Z := 0xe35fc.           (* [comment removed for export] *)
  Definition CM_A2 : Z := 0x3215a8.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cm_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
    [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cmalloc0_spec : cmalloc0_stmt.
  Proof.
    unfold cmalloc0_stmt, cmalloc0_stmt_at. intros until lo. intros ST CEIL LO MI IM GM. hcb.
    unfold P_CRYPTO_malloc, FR_CRYPTO_malloc in *. prep_statics IM GM.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. if_true. step. if_true. do 8 step.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma cmalloc_array0_spec : cmalloc_array0_stmt.
  Proof.
    unfold cmalloc_array0_stmt, cmalloc0_stmt_at. intros until lo. intros ST CEIL LO MI IM GM. hcb.
    unfold P_CRYPTO_malloc_array, FR_CRYPTO_array, FR_CRYPTO_malloc in *. prep_statics IM GM.
    pose proof (word_range sp) as SPR. pose proof (word_range a1) as A1R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    do 7 step. zstep. rewrite Z.mul_0_l. change (Z.shiftr 0 64) with 0.
    step. step. if_true.
    zstep. rewrite Z.mul_0_l. do 8 step.
    release_frame FR ST (bv_unsigned sp).
    pose proof cmalloc0_spec as C0. unfold cmalloc0_stmt, cmalloc0_stmt_at, P_CRYPTO_malloc, FR_CRYPTO_malloc in C0.
    eapply evt_mono.
    { eapply C0; [exact ST| exact CEIL| lia| exact MI| exact IM| exact GM]. }
    intros ms' PO. unfold cmalloc0_post in *. destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU' & WM' & MI' & ST').
    do 15 eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU']|].
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    split; [exact MI'| exact ST'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cm1_post (sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 CM_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2
                   (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 CM_A2) (Z_to_bv 64 P_CRYPTO_malloc) a4 a5 a6 a7
                   a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 RMALLOC_SYM) fc None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (A_mem_inited, A_mem_inited + 1)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
      /\ MEMFLAG m1 1 /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma cm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n v lo : Z),
      1 <= n < 2^32 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      evt usegs (cm1_post sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros HN ST CEIL LO MI MF IM GM. hcb.
    unfold P_CRYPTO_malloc in *. prep_statics IM GM.
    destruct MF as (fb & MF & FBV & V01). unfold A_mem_inited in MF.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (0x333550, 0x333550 + 1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. if_true. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step.
    assert (FIN : forall m1,
      munch [(bv_unsigned sp + -48, bv_unsigned sp); (0x333550, 0x333550 + 1)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
      stk usegs m1 lo (bv_unsigned sp + -48) ->
      rw_cells usegs m1 (bv_unsigned sp + -48) (cm_frame (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) s3 s2 s1 s0 ra) ->
      rw_cells usegs m1 0x333550 [C1 (Z_to_bv 8 1)] ->
      rw_cells usegs m1 3288064 [C8 (Z_to_bv 64 931200); C8 (Z_to_bv 64 931856); C8 (Z_to_bv 64 932136)] ->
      rw_cells usegs m1 3282856 [C8 (Z_to_bv 64 931200); C8 (Z_to_bv 64 931856); C8 (Z_to_bv 64 932136)] ->
      evt usegs (cm1_post sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc n lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2 (Z_to_bv 64 0x3335dc) (Z_to_bv 64 1)
                 (Z_to_bv 64 3282344) (Z_to_bv 64 931200) a4 a5 a6 a7 a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe35f0) fc None m1 (seg_rom usegs))).
    { intros m1 MU1 WM1 MI1 ST1 FR1 MF1 IM1 GM1. clear MU WM MI ST FR MF IM GM.
      step. step. step. finish; [exact FR1|]. exists (Z_to_bv 8 1). split; [exact MF1| split; [reflexivity| lia]]. }
    cbv delta [mkR] in FIN.
    destruct V01 as [-> | ->].
    - replace fb with (b8 0) in MF by (symmetry; exact (byte_eq_of_unsigned fb 0 FBV)).
      st1. unfold wz. step. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1.
      step. st1.
      eapply FIN; eassumption.
    - replace fb with (b8 1) in MF by (symmetry; exact (byte_eq_of_unsigned fb 1 FBV)).
      st1. unfold wz. step. (* [comment removed for export] *)
      try (if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia]; clear K1).
      eapply FIN; first [eassumption| exact MF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cm_seg2 :
    forall (sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 CM_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 CM_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HA FR MI. unfold CM_RA.
    replace (ret_pc (Z_to_bv 64 0xe35fc)) with (Z_to_bv 64 0xe35fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold cm_frame in FR.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 7 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition arr_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (target v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a2 a3 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 target) fc None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp).

  Local Ltac arr_prefix_tac sp m lo ST :=
    hcb;
    pose proof (word_range sp) as SPR;
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU; pose proof (wmono_refl usegs m) as WM;
    carve_frame 32%nat ST;
    do 7 step; zstep; rewrite (Z.shiftr_div_pow2 _ 64), Z.div_small by lia;
    step; step; if_true; zstep; do 8 step;
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FR ST (bv_unsigned sp) end; finish.

  Lemma arr_malloc_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size < 2^32 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (arr_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P_CRYPTO_malloc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m (seg_rom usegs)).
  Proof. unfold P_CRYPTO_malloc_array, P_CRYPTO_malloc. intros until lo; intros HN HS HP ST CEIL LO MI. arr_prefix_tac sp m lo ST. Qed.

  Lemma arr_calloc_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size < 2^32 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (arr_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P_CRYPTO_zalloc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_calloc) fc None m (seg_rom usegs)).
  Proof. unfold P_CRYPTO_calloc, P_CRYPTO_zalloc. intros until lo; intros HN HS HP ST CEIL LO MI. arr_prefix_tac sp m lo ST. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CZ_RA : Z := 0xe366c.
  Definition CZ_T1 : Z := 0x2c0688.          (* [comment removed for export] *)
  Definition cz_frame (j : list byte) (s1 s0 ra : word) : list cell := [CB 8 j; C8 s1; C8 s0; C8 ra].

  Definition cz1_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
      (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 CZ_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                   (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells usegs m1 (bv_unsigned sp + -32) (cz_frame j s1 s0 ra).

  Lemma cz_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (cz1_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 F fc n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. hcb. unfold P_CRYPTO_zalloc, P_CRYPTO_malloc.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    do 7 step. finish. exact FR.
  Qed.

  Lemma cz_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -32) (cz_frame j s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 CZ_T1) t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_memset) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 CZ_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 n) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 CZ_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HA FR MI. unfold CZ_RA, CZ_T1, P_memset.
    replace (ret_pc (Z_to_bv 64 0xe366c)) with (Z_to_bv 64 0xe366c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold cz_frame in FR.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 8 step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma cmalloc_spec : cmalloc_stmt H.
  Proof.
    unfold cmalloc_stmt, cmalloc_stmt_at. intros until errv.
    intros A0 HN HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK in LO. hcb. subst a0. subst tp. rewrite errno_RATP in ERR.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply cm_seg1; try eassumption; lia|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MF1 & IM1 & GM1).
    unfold A_mem_inited in MU1.
    (* [comment removed for export] *)
    pose proof (HH_malloc H HH) as MA. unfold malloc_sr_stmt, malloc_sr_stmt_at in MA.
    eapply (sr_seq H HH).
    { eapply MA with (lo := lo) (B := B) (LB := LB) (s := s) (n := n); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold RMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ =>
               eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|];
               constructor; [left; cbn; lia|]; constructor; [right; left; cbn; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia| constructor]
           | |- hs_KREL _ _ _ => exact KREL
           | |- hs_alloc_ok _ _ _ _ => eapply (HH_alloc_ok H HH); [exact HP| lia| lia| lia| lia]
           | |- hs_rauxv_ok _ _ _ =>
               eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL;
               constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; eapply (rw_cells_transport usegs _ m m1); [exact ERR| exact MU1| exact WM1| unfold RERRNO; cbn; lia]
           | |- mem_inv _ _ => exact MI1
           end. }
    intros [ms2 mo2] PO. unfold malloc_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HEAP2 & BLK).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, HPRES by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    apply (rheap_pres_rw_cells _ _ _ _ _ _ HPRES) in FR1; [| left; cbn; lia].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply cm_seg2; [lia| exact FR1| exact MI2]|].
    intros ms3 ->.
    apply (sr_done H HH). unfold cmalloc_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|].
    split. { unfold cm_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp). exact ST2. }
    split; [rewrite errno_RATP; exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans.
      - eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB].
        constructor; [left; cbn; lia|]. constructor; [right; cbn; intros a Ha; unfold memflag_foot, A_mem_inited; cbn; lia| constructor].
      - eapply (xpres_weaken LB LB _ _ memflag_foot); [apply xpres_of_heap_pres; exact HPRES| lia| auto| auto]. }
    split; [exact BR|]. split; [exact HEAP2|]. split; [exact BLK|].
    split.
    { destruct MF1 as (fb1 & MF1 & FB1 & _). exists fb1. split; [| split; [exact FB1| lia]].
      eapply rheap_pres_rw_cells; [exact HPRES| exact MF1|]. right; left. unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia. }
    split.
    { eapply rheap_pres_rw_cells; [exact HPRES| exact IM1|]. right; left. unfold A_malloc_impl, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia. }
    eapply rheap_pres_rw_cells; [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cmalloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB n lo B m m1 mo c,
    xpres LB (bv_unsigned sp) memflag_foot m m1 ->
    cmalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m1 mo c ->
    cmalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold cmalloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p, s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  Lemma czalloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB n lo B m m1 mo c,
    xpres LB (bv_unsigned sp) memflag_foot m m1 ->
    czalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m1 mo c ->
    czalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold czalloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, p, s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  (* [comment removed for export] *)
  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma MEMFLAG_across : forall W m m1 v,
    munch W m m1 -> wmono usegs m m1 -> disjoint_from W A_mem_inited 1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros W m m1 v MU WM DJ (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply rw_cells_transport; [exact MF| exact MU| exact WM| exact DJ].
  Qed.
  Lemma IMPL_across : forall W m m1,
    munch W m m1 -> wmono usegs m m1 -> disjoint_from W A_malloc_impl 24 -> IMPL_mem m -> IMPL_mem m1.
  Proof. intros W m m1 MU WM DJ IM. eapply rw_cells_transport; [exact IM| exact MU| exact WM| exact DJ]. Qed.
  Lemma GOT_across : forall W m m1,
    munch W m m1 -> wmono usegs m m1 -> disjoint_from W A_got_CRYPTO_malloc 24 -> GOT_mem m -> GOT_mem m1.
  Proof. intros W m m1 MU WM DJ GM. eapply rw_cells_transport; [exact GM| exact MU| exact WM| exact DJ]. Qed.
  (* [comment removed for export] *)
  Lemma MEMFLAG_heap : forall LB SP m m1 v, rheap_pres LB SP m m1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros LB SP m m1 v HPRES (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply rheap_pres_rw_cells; [exact HPRES| exact MF|]. right; left. unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.
  Lemma IMPL_heap : forall LB SP m m1, rheap_pres LB SP m m1 -> IMPL_mem m -> IMPL_mem m1.
  Proof.
    intros LB SP m m1 HPRES IM. eapply rheap_pres_rw_cells; [exact HPRES| exact IM|].
    right; left. unfold A_malloc_impl, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.
  Lemma GOT_heap : forall LB SP m m1, rheap_pres LB SP m m1 -> GOT_mem m -> GOT_mem m1.
  Proof.
    intros LB SP m m1 HPRES GM. eapply rheap_pres_rw_cells; [exact HPRES| exact GM|].
    right; left. unfold A_got_CRYPTO_malloc, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma IMPL_xpres : forall LB SP m m1, xpres LB SP memflag_foot m m1 -> IMPL_mem m -> IMPL_mem m1.
  Proof.
    intros LB SP m m1 XP IM. eapply xpres_rw_cells'; [exact XP| exact IM| |].
    - right; left. unfold A_malloc_impl, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
    - unfold memflag_foot, A_malloc_impl, A_mem_inited. constructor; [cbn; lia| constructor].
  Qed.
  Lemma GOT_xpres : forall LB SP m m1, xpres LB SP memflag_foot m m1 -> GOT_mem m -> GOT_mem m1.
  Proof.
    intros LB SP m m1 XP GM. eapply xpres_rw_cells'; [exact XP| exact GM| |].
    - right; left. unfold A_got_CRYPTO_malloc, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
    - unfold memflag_foot, A_got_CRYPTO_malloc, A_mem_inited. constructor; [cbn; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma cmalloc_array_spec : cmalloc_array_stmt H.
  Proof.
    unfold cmalloc_array_stmt. intros until errv.
    intros A0 A1 HN HS HNS HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    hcb. subst a0 a1. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply arr_malloc_prefix; [exact HN| exact HS| exact HNS| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof cmalloc_spec as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (sr_mono H HH); [| intros c PO; eapply cmalloc_post_back; [exact XP1| exact PO]].
    eapply CM with (v := v); try reflexivity; try eassumption.
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor].
    - unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK. lia.
    - subst tp. rewrite errno_RATP in *. errno_across ERR MU1 WM1.
    - eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF].
    - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
    - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM].
  Qed.

  (* [comment removed for export] *)
  Lemma czalloc_spec : czalloc_stmt H.
  Proof.
    unfold czalloc_stmt, czalloc_stmt_gen. intros until errv.
    intros A0 SZ HN HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    subst size. rewrite Z.mul_1_r in *.
    unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    hcb. subst a0. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply cz_seg1; [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    pose proof cmalloc_spec as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (sr_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := num); rewrite ?unsigned_lit by lia; try reflexivity; try eassumption.
      - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
      - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor].
      - lia.
      - unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK. lia.
      - subst tp. rewrite errno_RATP in *. errno_across ERR MU1 WM1.
      - eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF].
      - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
      - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]. }
    intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply cz_seg2; [lia| exact FR1| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply memset_spec; [| exact MI2]|].
    { rewrite !unsigned_lit by lia. exact BLK. }
    intros ms4 PO. unfold memset_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3).
    rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in BLK3 by lia. change (0 mod 256) with 0 in BLK3.
    apply (sr_done H HH). unfold czalloc_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m3, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { unfold cz_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp).
             eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. subst tp. rewrite errno_RATP. unfold RERRNO. cbn. lia. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (p, A, num). split; [left; reflexivity| cbn; lia]. }
    split; [exact BLK3|].
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.

  Lemma ccalloc_spec : ccalloc_stmt H.
  Proof.
    unfold ccalloc_stmt, czalloc_stmt_gen. intros until errv.
    intros A0 (A1 & HN & HS) HNS HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    hcb. subst a0 a1. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply arr_calloc_prefix; [exact HN| exact HS| exact HNS| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof czalloc_spec as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_mono H HH); [| intros c PO; eapply czalloc_post_back; [exact XP1|]; rewrite <- (Z.mul_1_r (num * size)); exact PO].
    eapply CZ with (v := v); try reflexivity; try eassumption; rewrite ?Z.mul_1_r; try eassumption.
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor].
    - unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK. lia.
    - subst tp. rewrite errno_RATP in *. errno_across ERR MU1 WM1.
    - eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF].
    - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
    - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM].
  Qed.
End W.
