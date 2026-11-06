(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4 ECH_C14_stmt ECH_KitSeg ECH_LibMid ECH_C14_bio2buf.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_ECHS_FUNC_RP : Z := 0x2118c.   (* [comment removed for export] *)
Definition S_echs_file : list byte := Eval vm_compute in img_cstr A_ECHS_FILE_RP 64.
Definition K_echs_file : list byte := Eval vm_compute in img_slack A_ECHS_FILE_RP (length S_echs_file).
Definition S_echs_func : list byte := Eval vm_compute in img_cstr A_ECHS_FUNC_RP 64.
Definition K_echs_func : list byte := Eval vm_compute in img_slack A_ECHS_FUNC_RP (length S_echs_func).
Definition ERR_LIB_SSL : Z := 20.
Definition R_INTERNAL_ERROR : Z := 0xc0103.            (* [comment removed for export] *)
Definition R_PASSED_INVALID_ARGUMENT : Z := 0x80106.
Definition R_PASSED_NULL_PARAMETER : Z := 0xc0102.
(* [comment removed for export] *)
Definition RP_EPI : Z := 0x26c6a4.        (* [comment removed for export] *)
Definition RP_EPI0 : Z := 0x26c6a0.       (* [comment removed for export] *)
Definition RP_ERRL : Z := 0x26c92c.       (* [comment removed for export] *)
Definition RP_ERRL0 : Z := 0x26c920.      (* [comment removed for export] *)
Definition RP_ERRL_R1 : Z := 0x26c938.    (* [comment removed for export] *)
Definition RP_ERRL_R2 : Z := 0x26c954.    (* [comment removed for export] *)
Definition RP_ERRL_R3 : Z := 0x26c968.    (* [comment removed for export] *)
Definition RP_595_R1 : Z := 0x26c63c. Definition RP_595_R2 : Z := 0x26c658.   (* [comment removed for export] *)
Definition RP_599_R1 : Z := 0x26c7e8. Definition RP_599_R2 : Z := 0x26c804.   (* [comment removed for export] *)

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma R_echs_file : ROSTR A_ECHS_FILE_RP S_echs_file K_echs_file.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_echs_func : ROSTR A_ECHS_FUNC_RP S_echs_func K_echs_func.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition rp_glue (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      mem_inv rsegs m1 ->
      evt rsegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom rsegs)).

  Local Tactic Notation "glue_tac" constr(raA) integer(n) :=
    unfold rp_glue; intros;
    let v := eval cbv in raA in
    replace (ret_pc (Z_to_bv 64 raA)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
    do n step; apply evt_done; do 12 eexists; reflexivity.

  Lemma rp_g595a : rp_glue RP_595_R1 RP_595_R2 P_ERR_set_debug A_ECHS_FILE_RP 595 A_ECHS_FUNC_RP.
  Proof. unfold RP_595_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_RP. glue_tac RP_595_R1 7. Qed.
  Lemma rp_g595b : rp_glue RP_595_R2 RP_EPI0 P_ERR_set_error ERR_LIB_SSL R_INTERNAL_ERROR 0.
  Proof. unfold RP_EPI0, P_ERR_set_error, ERR_LIB_SSL, R_INTERNAL_ERROR. glue_tac RP_595_R2 7. Qed.
  Lemma rp_g599a : rp_glue RP_599_R1 RP_599_R2 P_ERR_set_debug A_ECHS_FILE_RP 599 A_ECHS_FUNC_RP.
  Proof. unfold RP_599_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_RP. glue_tac RP_599_R1 7. Qed.
  Lemma rp_g599b : rp_glue RP_599_R2 RP_ERRL0 P_ERR_set_error ERR_LIB_SSL R_INTERNAL_ERROR 0.
  Proof. unfold RP_ERRL0, P_ERR_set_error, ERR_LIB_SSL, R_INTERNAL_ERROR. glue_tac RP_599_R2 7. Qed.

  (* [comment removed for export] *)
  Definition rp_epi_stmt (pc0 : Z) (rv : word -> word) : Prop :=
    forall (rax gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA : word),
      2352 <= bv_unsigned sp ->
      rw_cells rsegs m (bv_unsigned sp + -104) (rp_saves S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR RA sp gp tp t0 t1 t2 S0 S1 (rv s4) a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (ret_pc RA) fc None m (seg_rom rsegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
  (* [comment removed for export] *)
  Lemma rp_epi : rp_epi_stmt RP_EPI (fun s4 => s4).
  Proof.
    unfold rp_epi_stmt. intros until RA. intros SPL SV MI. unfold RP_EPI. pose proof (word_range sp) as SPR. unfold rp_saves in SV.
    step. step. do 13 step. step. step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma rp_epi0 : rp_epi_stmt RP_EPI0 (fun _ => Z_to_bv 64 0).
  Proof.
    unfold rp_epi_stmt. intros until RA. intros SPL SV MI. unfold RP_EPI0. pose proof (word_range sp) as SPR. unfold rp_saves in SV.
    step. step. step. do 13 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_errl1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 RP_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom rsegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RP_ERRL) fc None m (seg_rom rsegs)).
  Proof. intros until m. intros MI. unfold RP_ERRL, RP_ERRL_R1, P_BIO_free_all. do 3 step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma rp_errl0 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 RP_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 RP_ERRL0) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 RP_ERRL0)) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI.
    replace (ret_pc (Z_to_bv 64 RP_ERRL0)) with (Z_to_bv 64 RP_ERRL0) by (symmetry; apply ret_pc_even; [unfold RP_ERRL0; lia| reflexivity]).
    unfold RP_ERRL0, RP_ERRL_R1, P_BIO_free_all. do 6 step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma rp_errl2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 RP_ERRL_R2) sp gp tp t0 t1 t2 s0 s1 s3 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 645) a3 a4 a5 a6 a7
                                          (Z_to_bv 64 A_ECHS_FILE_RP) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 RP_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 RP_ERRL_R1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI.
    replace (ret_pc (Z_to_bv 64 RP_ERRL_R1)) with (Z_to_bv 64 RP_ERRL_R1) by (symmetry; apply ret_pc_even; [unfold RP_ERRL_R1; lia| reflexivity]).
    unfold RP_ERRL_R1, RP_ERRL_R2, P_CRYPTO_free, A_ECHS_FILE_RP. do 7 step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma rp_errl3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 RP_ERRL_R3) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 646) a3 a4 a5 a6 a7
                                          (Z_to_bv 64 A_ECHS_FILE_RP) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 RP_ERRL_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A_ECHS_FILE_RP) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 RP_ERRL_R2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI.
    replace (ret_pc (Z_to_bv 64 RP_ERRL_R2)) with (Z_to_bv 64 RP_ERRL_R2) by (symmetry; apply ret_pc_even; [unfold RP_ERRL_R2; lia| reflexivity]).
    unfold RP_ERRL_R2, RP_ERRL_R3, P_CRYPTO_free, A_ECHS_FILE_RP. do 5 step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma rp_errl4 :
    forall (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA : word),
      2352 <= bv_unsigned sp ->
      rw_cells rsegs m (bv_unsigned sp + -104) (rp_saves S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR RA sp gp tp t0 t1 t2 S0 S1 s4 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (ret_pc RA) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 RP_ERRL_R3) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 RP_ERRL_R3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until RA. intros SPL SV MI. pose proof (word_range sp) as SPR. unfold rp_saves in SV.
    replace (ret_pc (Z_to_bv 64 RP_ERRL_R3)) with (Z_to_bv 64 RP_ERRL_R3) by (symmetry; apply ret_pc_even; [unfold RP_ERRL_R3; lia| reflexivity]).
    unfold RP_ERRL_R3. step. step. step. do 13 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bio_free_all_null :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom rsegs)).
  Proof. intros until m. intros MI. unfold P_BIO_free_all. step. if_lit. step. apply evt_done. reflexivity. Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let EGS : egs_stmt H := proj1 (proj2 (C4_spec H HX CERTO3)).

  (* [comment removed for export] *)
  Lemma rp_raise :
    forall (sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIBc Lc : list block) (M : libmid) (x : ctxinfo)
           (lo B : Z) (errv : word) (ra1 ra2 ra3 line reason : Z) (Q : config -> Prop),
      hs_RHEAP H s (mid_errblocks M ++ Lc) m -> hs_KREL H s mo ->
      LIBMID LIBc m M -> (forall b, In b LIBc -> In b Lc) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      lb_bytes (mid_errblocks M ++ Lc) + errph_bytes (mid_err M) + ERRDEBUG_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ Lc)) + errph_cnt (mid_err M) + 2 <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ Lc) + errph_big (mid_err M) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RAISE_STACK (mid_err M) ->
      rw_cells rsegs m RERRNO [C4 errv] -> mem_inv rsegs m ->
      0 <= line < 2^31 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      rp_glue ra1 ra2 P_ERR_set_debug A_ECHS_FILE_RP line A_ECHS_FUNC_RP ->
      rp_glue ra2 ra3 P_ERR_set_error ERR_LIB_SSL reason 0 ->
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (LE : list block) (M' : libmid) (c : errchain),
         hs_KREL H s' mo' -> hs_MPRES H mo mo' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> hs_rauxv_ok H m' B ->
         hs_RHEAP H s' (mid_errblocks M' ++ LE ++ Lc) m' ->
         LIBMID (LE ++ LIBc) m' M' -> mid_step M M' -> mid_newlib_ok M M' LE ->
         mid_flag M' = 1 -> mid_ctx M' = CtxReady x -> mid_err M' = ErrReady c -> mid_vdso M' = mid_vdso M -> errph_delta (mid_err M) LE c ->
         Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES -> lb_big (mid_errblocks M') = 0 ->
         rw_cells rsegs m' RERRNO [C4 errv'] ->
         xpres Lc (bv_unsigned sp) (ERR_X ++ memflag_foot ++ errph_foot (mid_err M)) m m' ->
         hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra3) sp gp (Z_to_bv 64 RATP) u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                              F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom rsegs)) mo')) ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra1) sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)) mo).
  Proof using HH EGS CERTO3 HX.
    intros until Q. intros HP KREL LM SUB CX F1 BY CN BG AUX SPB SPA ST CEIL LO ERR MI LNR REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & GM & GE & GX & MM & MB & HT & RL).
    destruct M as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph f.
    unfold mid_errblocks in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. cbn [ERRPH_mid] in EPm.
    assert (EP : ERRPH Lc m eph) by (eapply ERRPH_mono; [exact EPm| exact SUB]).
    assert (CPc : CTXPH Lc m (CtxReady x)) by (eapply CTXPH_mono; [exact CP| exact SUB]).
    assert (EB : errph_below eph lo).
    { destruct eph as [|c0]; [exact I|]. cbn [errph_below]. cbn [ERRPH] in EPm. destruct EPm as [_ CH].
      eapply (chain_below_of_RHEAP H HH); [exact HP| intros b Hb; apply in_or_app; right; exact (SUB _ Hb)| exact CH| exact CEIL]. }
    unfold rp_glue in G1, G2.
    eapply (raise_spec H HX EGS) with (lo := lo) (B := B) (LB := Lc) (s := s) (ph := eph) (E := E) (x := x) (errv := errv)
      (file := A_ECHS_FILE_RP) (fs := S_echs_file) (fsl := K_echs_file) (func := A_ECHS_FUNC_RP) (gs := S_echs_func) (gsl := K_echs_func)
      (line := line) (lib := ERR_LIB_SSL) (reason := reason) (ra2 := ra2) (ra3 := ra3).
    all: try first [exact HP| exact KREL| exact AUX| exact SPB| exact SPA| exact ST| exact CEIL| exact LO| exact MI| exact MF| exact IM| exact GM| exact RL| exact EP| exact EX| exact EB| exact CPc
                    | exact R_echs_file| exact R_echs_func| exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E].
    all: lazymatch goal with
         | |- lb_bytes _ + raise_bytes _ <= _ => unfold raise_bytes; clear - BY; lia
         | |- Z.of_nat _ + raise_cnt _ <= _ => unfold raise_cnt; clear - CN; lia
         | |- lb_big _ + _ <= _ => exact BG
         | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR
         | |- Z_to_bv 64 RATP = _ => reflexivity
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length _) < _ => vm_compute; reflexivity
         | |- 0 < A_ECHS_FILE_RP => unfold A_ECHS_FILE_RP; lia
         | |- 0 < A_ECHS_FUNC_RP => unfold A_ECHS_FUNC_RP; lia
         | |- 0 < ERR_LIB_SSL < 256 => unfold ERR_LIB_SSL; lia
         | |- ERR_LIB_SSL <> 2 => unfold ERR_LIB_SSL; lia
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply G1; assumption
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply G2; assumption
         | _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' mo' s' errv' LBN c p1 p2 A1 A2 n1 n2 E'
           KREL' MP' MI' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' XP'.
    pose proof (errst_fits_raise E A1 p1 n1 line A2 p2 n2 ERR_LIB_SSL reason FIT RSZ) as FIT'. change (errst_fits E') in FIT'.
    pose proof (LIBMID_errcall_mf LIBc Lc (LBN ++ Lc) LBN (bv_unsigned sp) m m' (mkMID 1 (CtxReady x) eph E v) x c E' LM eq_refl XP' SUB CP' EP' DL EST' FIT' MF') as LM'.
    cbn [mid_vdso] in LM'.
    pose proof EST' as (LEN' & _).
    pose proof (errst_fits_bounds E' LEN' FIT') as (EC' & EB' & EG').
    rewrite errno_RATP in ERR'.
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' mo' s' errv' LBN (mkMID 1 (CtxReady x) (ErrReady c) E' v) c);
      cbn [mid_flag mid_ctx mid_err mid_E mid_vdso mid_errblocks]; try reflexivity.
    all: try first [exact KREL'| exact MP'| exact MI'| exact ST'| exact AUX'| exact HP'| exact LM'| exact DL| exact EC'| exact EB'| exact EG'| exact ERR'| exact XP'].
    - (* [comment removed for export] *) unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 ->. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity.
    - (* [comment removed for export] *) unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LBN. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct eph as [|c0]; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity.
  Qed.
End W.
