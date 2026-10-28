(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsCall AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitSeg ECH_ALibMF ECH_ALibOK ECH_ALibMid ECH_ALibMidA ECH_ATraces
  ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C11 ECH_AStmt_C13 ECH_AStmt_C14 ECH_AStmt_C15
  ECH_AC1_dup ECH_AC1_free ECH_AC1_freeopt ECH_AC7_newmembuf ECH_AC15_parse.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FZ_R1 : Z := R_fuzz_parse_one.          (* [comment removed for export] *)
Definition FZ_R2 : Z := R_fuzz_CRYPTO_memdup.      (* [comment removed for export] *)
Definition FZ_R3 : Z := R_fuzz_parse_one_2.        (* [comment removed for export] *)
Definition FZ_R4 : Z := R_fuzz_CRYPTO_free.        (* [comment removed for export] *)
Definition FZ_R5 : Z := R_fuzz_ERR_clear_error.    (* [comment removed for export] *)
Definition A_FZ_FILE : Z := 0x40b4d.
Definition ASHB15 : Z := 2147450880.               (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac killu K := exfalso; revert K; change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; intros K; Z.div_mod_to_equations; lia.

  Lemma rw_cells_as_CB1 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    clear. intros m A cs [[WF BA] W]. unfold rw_cells, cells_at. cbn [cells_bytes cbytes cells_wf cell_wf cells_size csize].
    rewrite app_nil_r, Nat.add_0_r. split; [split; [split; [apply cells_bytes_length; exact WF| exact I]| exact BA]| exact W].
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D N lo : Z),
      a1 = Z_to_bv 64 N -> 0 <= N < 2^31 -> 0 <= D < 2^64 ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 FZ_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 D) (Z_to_bv 64 N) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB15) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_parse_one) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_LLVMFuzzerTestOneInput) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros A1 NR DR GSB SHB0 ST CEIL LO MI. subst a1.
    unfold P_LLVMFuzzerTestOneInput, P_parse_one, FZ_R1, R_fuzz_parse_one, ASHB15.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. carve_frame 32%nat ST.
    do 4 st1. step. zstep. rewrite (Z.shiftr_div_pow2 N 31), (Z.div_small N (2^31)) by lia.
    step. if_lit. step. step. step. step. step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg2a :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N : Z),
      32 <= N < 1500 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FZ_R2) sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 s1 (Z_to_bv 64 N) (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 68) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 FZ_R1) sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until N. intros NR MI. unfold FZ_R1, FZ_R2, R_fuzz_parse_one, R_fuzz_CRYPTO_memdup, P_CRYPTO_memdup, A_FZ_FILE.
    replace (ret_pc (Z_to_bv 64 0x1ef250)) with (Z_to_bv 64 0x1ef250) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. if_cases K0; zify_cond K0; [killu K0|]. clear K0.
    do 5 step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg2b :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N : Z),
      0 <= N < 2^31 -> (N < 32 \/ 1500 <= N) -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FZ_R4) sp gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 FZ_R1) sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until N. intros NR NC MI. unfold FZ_R1, FZ_R4, R_fuzz_parse_one, R_fuzz_CRYPTO_free, P_CRYPTO_free, A_FZ_FILE.
    replace (ret_pc (Z_to_bv 64 0x1ef250)) with (Z_to_bv 64 0x1ef250) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. if_cases K0; zify_cond K0; [| killu K0]. clear K0.
    do 5 step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg3 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N A : Z) (bs : list byte),
      32 <= N < 1500 -> 0 < A -> A + N <= aceil -> aapp A N -> zlength bs = N -> rw_cells asegs m A [CB (length bs) bs] ->
      accessible m A N -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (c2 c3 c4 : word) m1 bs',
          ms' = MS (mkR (Z_to_bv 64 FZ_R3) sp gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 N) c2 c3 c4 a5 a6 a7
                       (Z_to_bv 64 ASHB15) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_parse_one) fc None m1 (seg_rom asegs)
          /\ munch [(A, A + 6)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 A [CB (length bs') bs'] /\ zlength bs' = N)
        (MS (mkR (Z_to_bv 64 FZ_R2) sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ASHB15) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until bs. intros NR AP AH AAP LEN BLK ACC0 MI. unfold FZ_R2, FZ_R3, R_fuzz_CRYPTO_memdup, R_fuzz_parse_one_2, P_parse_one, ASHB15. unfold zlength in LEN.
    replace (ret_pc (Z_to_bv 64 0x1ef274)) with (Z_to_bv 64 0x1ef274) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    acb. pose proof aceil_range as ACR.
    pose proof (munch_refl [(A, A + 6)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(A, A + 6)]).
    { constructor; [| constructor]. cbn [fst snd]. destruct (aapp_not_shadowland A N AAP); lia. }
    change (id (accessible m A N)) in ACC0.
    (* [comment removed for export] *)
    destruct (rw_cells_CB_split _ _ _ _ 6 _ BLK ltac:(lia)) as [HD TL]. clear BLK.
    Local Ltac reacc ACC0 MU NSW A N :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (ACC : accessible mx A N) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. do 2 step. ub_dead. step. zstep. reacc ACC0 MU NSW A N. ck8_load ACC A. step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    zstep. zstep. step. step.
    step. st1. step. ub_dead. zstep. zstep. reacc ACC0 MU NSW A N. ck8_load ACC (A + 1). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    step. st1. step. ub_dead. do 3 step. ub_dead. zstep. zstep. reacc ACC0 MU NSW A N. ck8_load ACC (A + 2). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    zstep. step. step. st1. step. ub_dead. zstep. zstep. reacc ACC0 MU NSW A N. ck8_load ACC (A + 3). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    do 2 step. st1. step. ub_dead. do 3 step. ub_dead. zstep. zstep. reacc ACC0 MU NSW A N. ck8_load ACC (A + 4). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step. st1. step. ub_dead. zstep. zstep. reacc ACC0 MU NSW A N. ck8_load ACC (A + 5). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC.
    (* [comment removed for export] *)
    st1. step. step. step.
    (* [comment removed for export] *)
    pose proof (rw_cells_as_CB1 _ _ _ HD) as HD'. cbn [cells_size csize cells_bytes cbytes app Nat.add] in HD'.
    pose proof (rw_cells_CB_join _ _ _ _ _ _ _ HD' TL) as J. clear HD HD' TL.
    lazymatch type of J with rw_cells _ _ _ [CB ?n ?b] =>
      replace n with (length b) in J by (rewrite length_app, length_skipn; cbn [length]; lia) end.
    apply evt_done. eexists _, _, _, m1. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact J|].
    unfold zlength. rewrite length_app, length_skipn. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FZ_R4) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 FZ_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold FZ_R3, FZ_R4, R_fuzz_parse_one_2, R_fuzz_CRYPTO_free, P_CRYPTO_free, A_FZ_FILE.
    replace (ret_pc (Z_to_bv 64 0x1ef374)) with (Z_to_bv 64 0x1ef374) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FZ_R5) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 FZ_R4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold FZ_R4, FZ_R5, R_fuzz_CRYPTO_free, R_fuzz_ERR_clear_error, P_ERR_clear_error.
    replace (ret_pc (Z_to_bv 64 0x1ef390)) with (Z_to_bv 64 0x1ef390) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma af_seg6 :
    forall (gp tp t0 t1 t2 s0x s1x s2x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra sp s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -32) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 FZ_R5) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 FZ_R5)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI RAE. unfold FZ_R5, R_fuzz_ERR_clear_error. unfold ap_frame in FR.
    replace (ret_pc (Z_to_bv 64 0x1ef394)) with (Z_to_bv 64 0x1ef394) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. do 4 step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section G.
  Context {HCEIL : HeapCeil}.

  Local Ltac addrs := unfold A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret,
    A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_optsdone_lock, A_init_lock,
    A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main, A_destructor_key,
    A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
    A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret,
    A_defctx_exlock, A_defctx_exmeth_bio, A_malloc_impl, A_realloc_impl, A_free_impl, A_vdso_func, A_global_cleanup, A_mem_inited,
    A_got_CRYPTO_malloc, A_got_ossl_echext_free, A_got_ASN1_OBJECT_free, A_mem_buf_method, A_b64_method, O_METH_BREAD,
    A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW, LIBKEY0, AIMG_TOP in *.
  (* [comment removed for export] *)
  Local Ltac in_ivs_tac W a :=
    apply (proj1 (in_ivs_b_spec W a)); unfold W; addrs; cbn [in_ivs_b fst snd Z.add];
    repeat (rewrite Bool.orb_true_iff; first [left; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia | right]).

  (* [comment removed for export] *)
  Lemma rw_cells_of_none : forall m A cs,
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m (wa a) = None) ->
    cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
    rw_cells asegs m A cs.
  Proof.
    intros m A cs HN WF HB HA HL. pose proof (cells_bytes_length cs WF) as LEN.
    apply (rw_cells_recast asegs m A [CB (length (cells_bytes cs)) (cells_bytes cs)]).
    - apply none_on_rw_cells; [intros a Ha; apply HN; rewrite LEN in Ha; exact Ha| exact HB| exact HA| rewrite LEN; exact HL].
    - exact WF.
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
    - cbn [cells_size csize]. rewrite LEN. lia.
  Qed.
  Local Ltac img_chunk NONE :=
    apply rw_cells_of_none;
    [ intros a Ha; apply NONE; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in Ha; revert Ha; addrs; intros Ha;
      first [ in_ivs_tac LIBX0 a | lia | split; lia ]
    | cbn; repeat split; try reflexivity; try exact I
    | vm_compute; reflexivity
    | addrs; lia
    | addrs; cbn; lia ].

  (* [comment removed for export] *)
  Definition relro_grp (m : mem) : Prop :=
    GOT_mem m /\ GOT_echfree m /\ GOT_x509vpm m /\ METH_mem m /\ METH_b64 m /\ HPKE_tabs m /\ relro_lib m.
  Lemma relro_grp_of_image : forall m, arelro_lib m -> relro_grp m.
  Proof.
    intros m RL. assert (NONE : forall a, 0x571000 <= a < 0x5ea000 -> m (wa a) = None) by exact RL.
    unfold relro_grp, GOT_mem, GOT_echfree, GOT_x509vpm, METH_mem, METH_b64, HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS.
    repeat match goal with |- _ /\ _ => split end; try exact RL; try exact I; img_chunk NONE.
  Qed.

  Lemma errst_fits_cleared : errst_fits errst_cleared.
  Proof. unfold errst_fits, errst_cleared. cbn [es_slots]. repeat (apply Forall_cons; [cbn; unfold ERRDEBUG_BYTES; lia|]). apply Forall_nil. Qed.
  Lemma errst_fits_canonical : forall E, errst_canonical E -> errst_fits E.
  Proof. intros E [-> | ->]; [exact errst_fits_zero| exact errst_fits_cleared]. Qed.
  Lemma blocks_ERRST_canonical : forall E, errst_canonical E -> blocks_ERRST E = [].
  Proof. intros E [-> | ->]; reflexivity. Qed.
  Lemma estrs_ok_canonical : forall E, errst_canonical E -> estrs_ok E.
  Proof. intros E [-> | ->]; unfold estrs_ok; cbn [es_slots errst_zero errst_cleared repeat]; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. Qed.
  Lemma ERRST_canon_relist : forall L L' m a E, errst_canonical E -> ERRST L m a E -> ERRST L' m a E.
  Proof.
    intros L L' m a E CE ER. unfold ERRST in *.
    destruct ER as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & OWN).
    destruct K2 as [K2a K2b]. destruct K3 as [K3a K3b].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    clear OWN. destruct CE as [-> | ->]; cbn [es_slots errst_zero errst_cleared repeat];
      repeat (apply Forall_cons; [cbn [sl_file sl_file_o sl_func sl_func_o sl_flags sl_buffer sl_line slot_clear ofield]; repeat split; try reflexivity; lia|]); apply Forall_nil.
  Qed.

  Lemma LIBMID_fresh : forall LIB m, LIBST Fresh LIB m -> arelro_lib m -> LIB = [] /\ LIBMID [] m (mkMID 0 CtxFresh ErrFresh errst_zero false).
  Proof.
    intros LIB m [-> [PR M0]] RL. split; [reflexivity|]. unfold lib_pristine in PR.
    assert (NONE : forall a, rin_ivs LIBX0 a -> m (wa a) = None) by exact PR.
    assert (NON : forall A n, (forall a, A <= a < A + n -> rin_ivs LIBX0 a) -> none_on m A n) by (intros A n K a Ha; apply NONE; apply K; exact Ha).
    pose proof (relro_grp_of_image m RL) as (G1 & G2 & G3 & M1 & M2 & HT & _).
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRX errph_shad errph_below].
    split; [unfold IMPL_mem; repeat match goal with |- _ /\ _ => split end; img_chunk NONE|].
    split. { exists (b8 0). split; [img_chunk NONE| split; [reflexivity| left; reflexivity]]. }
    split. { unfold CTX_fresh. repeat match goal with |- _ /\ _ => split end; try exact M0; (apply NON; intros a Ha; revert Ha; addrs; intros Ha; in_ivs_tac LIBX0 a). }
    split. { unfold ERR_fresh_core. repeat match goal with |- _ /\ _ => split end; (apply NON; intros a Ha; revert Ha; addrs; intros Ha; in_ivs_tac LIBX0 a). }
    split; [reflexivity|].
    split; [img_chunk NONE|].
    split; [apply NONE; in_ivs_tac LIBX0 A_global_cleanup|].
    split; [exact errst_fits_zero|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact M1|]. split; [exact M2|]. split; [exact HT|]. split; [exact RL|].
    split; exact I.
  Qed.

  Lemma LIBMID_inited : forall LIB m i, LIBST (Inited i) LIB m -> arelro_lib m ->
    (forall b, In b LIB -> blk_addr b + blk_size b <= aceil /\ 0 <= blk_addr b) ->          (* [comment removed for export] *)
    exists E, errst_canonical E /\ lib_fits LIB /\ LIBMID LIB m (mkMID 1 (CtxReady (li_ctx i)) (ErrReady (li_chain i)) E (li_vdso_done i)).
  Proof.
    intros LIB m i ((IM & VD & MFb & CS & ES & CL) & (CB & CH & (E & ER & CE) & SH) & SZ) RL HB.
    exists E. split; [exact CE|]. split; [exact SZ|]. pose proof (relro_grp_of_image m RL) as (G1 & G2 & G3 & M1 & M2 & HT & _).
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRPH ERRX errph_shad errph_below].
    split; [exact IM|]. split; [exists (b8 1); split; [exact MFb| split; [reflexivity| right; reflexivity]]|].
    split; [split; [exact CS| exact CB]|]. split; [split; [exact ES| exact CH]|].
    split. { split; [eapply ERRST_canon_relist; [exact CE| exact ER]|]. split; [exact (estrs_ok_canonical E CE)|].
             unfold lib_shad, estrs_cells. rewrite (blocks_ERRST_canonical E CE). split; [apply Forall_nil| apply Forall_nil]. }
    split; [exact VD|]. split; [exact CL|]. split; [exact (errst_fits_canonical E CE)|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact M1|]. split; [exact M2|]. split; [exact HT|]. split; [exact RL|].
    split; [exact SH|].
    pose proof CH as (I1 & Z1 & _ & I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _).
    pose proof (HB _ I1) as [B1 P1]. pose proof (HB _ I2) as [B2 P2]. pose proof (HB _ I3) as [B3 P3]. pose proof (HB _ I4) as [B4 P4].
    rewrite Z1 in B1. rewrite Z2 in B2. rewrite Z3 in B3. rewrite Z4 in B4. unfold chain_below. repeat split; lia.
  Qed.

  Lemma abyte_eq_of_unsigned1 : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
  Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.

  Lemma LIBST_of_mid : forall LIB m x c E v, LIBMID LIB m (mkMID 1 (CtxReady x) (ErrReady c) E v) -> errst_canonical E -> lib_fits LIB ->
    LIBST (Inited (mkLI x c v)) LIB m.
  Proof.
    intros LIB m x c E v LM CE SZ. destruct LM as (IM & MF & CP & EP & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & SH & BL).
    cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRPH ERRX errph_shad] in *.
    destruct CP as [CS CB]. destruct EP as [ES CH]. destruct MF as (fb & MFb & V1 & _).
    assert (FB : fb = b8 1) by (rewrite (abyte_eq_of_unsigned1 fb 1 V1); reflexivity). subst fb.
    split.
    - unfold lib_statics_inited. cbn [li_ctx li_chain li_vdso_done]. exact (conj IM (conj VD (conj MFb (conj CS (conj ES CL))))).
    - split; [| exact SZ]. unfold lib_blocks_inited. cbn [li_ctx li_chain li_vdso_done]. split; [exact CB|]. split; [exact CH|].
      split; [| exact SH]. exists E. split; [| exact CE]. destruct EX as (ER & _). eapply ERRST_canon_relist; [exact CE| exact ER].
  Qed.
End G.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma parse_stack_max {HCEIL : HeapCeil} : forall M, PARSE_STACK M <= 10800.
Proof. intros [f [|x] [|c] E v]; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma errclear_stack_max {HCEIL : HeapCeil} : forall eph, ERRCLEAR_STACK eph <= 9360.
Proof. intros [|c]; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma mid_step_trans : forall M0 M1 M2, mid_step M0 M1 -> mid_step M1 M2 -> mid_step M0 M2.
Proof.
  intros M0 M1 M2 (F1 & C1 & E1 & V1) (F2 & C2 & E2 & V2). unfold mid_step.
  split; [exact F2|]. split; [intros b Hb; exact (C2 b (C1 b Hb))|]. split; [intros c Hc; exact (E2 c (E1 c Hc))| intros Hv; exact (V2 (V1 Hv))].
Qed.
(* [comment removed for export] *)
Lemma newlib_bounds : forall M M' LBN, mid_step M M' -> mid_newlib_ok M M' LBN ->
  lb_bytes LBN + mid_bytes M' <= mid_bytes M /\ Z.of_nat (length LBN) + mid_cnt M' <= mid_cnt M
  /\ Z.of_nat (length LBN) <= CTXINIT_CNT + ERRINIT_CNT /\ lb_bytes LBN <= CTXINIT_BYTES + ERRINIT_BYTES.
Proof.
  intros [f cph eph E v] [f' cph' eph' E' v'] LBN ST NW. unfold mid_step, mid_newlib_ok, mid_bytes, mid_cnt in *.
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. destruct ST as (_ & SC & SE & _). destruct NW as (LA & LE & P & C & R).
  rewrite (lb_bytes_perm_s _ _ P), (Permutation_length P), lb_bytes_app_s, length_app, Nat2Z.inj_add.
  assert (KA : lb_bytes LA + ctxph_bytes cph' <= ctxph_bytes cph /\ Z.of_nat (length LA) + ctxph_cnt cph' <= ctxph_cnt cph
               /\ Z.of_nat (length LA) <= CTXINIT_CNT /\ lb_bytes LA <= CTXINIT_BYTES).
  { destruct cph as [|b].
    - destruct cph' as [|b']; cbn [ctxph_delta ctxph_bytes ctxph_cnt] in C |- *.
      + subst LA. cbn. unfold CTXINIT_BYTES, CTXINIT_CNT. lia.
      + lia.
    - cbn in C. subst LA. rewrite (SC b eq_refl). cbn. unfold CTXINIT_CNT, CTXINIT_BYTES. lia. }
  assert (KE : lb_bytes LE + errph_bytes eph' <= errph_bytes eph /\ Z.of_nat (length LE) + errph_cnt eph' <= errph_cnt eph
               /\ Z.of_nat (length LE) <= ERRINIT_CNT /\ lb_bytes LE <= ERRINIT_BYTES).
  { destruct eph as [|c].
    - destruct eph' as [|c']; cbn [errph_delta errph_bytes errph_cnt] in R |- *.
      + subst LE. cbn. unfold ERRINIT_BYTES, ERRINIT_CNT. lia.
      + lia.
    - cbn in R. subst LE. rewrite (SE c eq_refl). cbn. unfold ERRINIT_CNT, ERRINIT_BYTES. lia. }
  lia.
Qed.
Lemma newlib_nil : forall M M' LBN x c, mid_ctx M = CtxReady x -> mid_err M = ErrReady c -> mid_newlib_ok M M' LBN -> LBN = [].
Proof.
  intros [f cph eph E v] M' LBN x c HC HE NW. unfold mid_newlib_ok in NW. cbn [mid_ctx mid_err] in *. subst cph eph.
  destruct NW as (LA & LE & P & -> & ->). apply Permutation_nil. apply Permutation_sym. exact P.
Qed.
(* [comment removed for export] *)
Lemma XF_libx : forall a, rin_ivs (memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X) a -> rin_ivs (AERRNO_X ++ (LIBX ++ [(A_next_key + 4, A_key_lock)])) a.
Proof.
  intros a Ha. apply (proj1 (in_ivs_b_spec _ a)).
  unfold memflag_foot, CTX_X, ERR_XE, ERRNO_X, ERR_X, VDSO_X in Ha. cbn [rin_ivs fst snd app] in Ha.
  unfold AERRNO_X, LIBX, LIBX0, LIBXW, ARERRNO, ATP, A_mem_inited, A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret,
    A_defctx_once, A_defctx_once_ret, A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock,
    A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret,
    A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret,
    A_optsdone, A_td_tsd_used, A_tsd_main, A_vdso_func in *.
  cbn [in_ivs_b fst snd app Z.add Z.sub].
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
  (* [comment removed for export] *)
  (assert (K3 : a < 12595196 \/ 12595196 <= a < 12595200 \/ 12595200 <= a) by lia); destruct K3 as [K3|[K3|K3]];
    repeat (rewrite Bool.orb_true_iff; first [left; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia | right]).
Qed.


(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CNX : cnewex_stmt H.
  Hypothesis CFX : cfreeex_stmt H.
  (* [comment removed for export] *)
  Hypothesis ECL : errclear_stmt H.
  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Hypothesis RCFG : readcfg_stmt H PF9new PF9free.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Definition TOK (r : Z * list Z) : Prop := trace_ok (as_TR H) (fst r) (snd r).
  Definition fuzz_closed_ok : Prop :=
       (forall M, parse_closed_ok H PF9new PF9free M)
    /\ ctxph_closed_ok H CtxFresh /\ errph_closed_ok H ErrFresh
    /\ Forall TOK (pf_shift R_parse_one_OSSL_ECHSTORE_new PF_storenew)
    /\ Forall TOK (pf_shift R_fuzz_parse_one PF_biofree) /\ Forall TOK (pf_shift R_fuzz_parse_one_2 PF_biofree)
    /\ Forall TOK (pf_shift R_fuzz_CRYPTO_memdup PF_cmemdup) /\ Forall TOK (pf_shift R_fuzz_CRYPTO_free PF_cfree)
    /\ (forall eph, Forall TOK (pf_shift R_fuzz_ERR_clear_error (PF_errclear eph))).
  Hypothesis HFC : atr_ok H -> fuzz_closed_ok.

  (* [comment removed for export] *)
  Definition MIDCOST : Z := 2 * (as_Cm H (2^23 + 2^20) + as_Cf H (2^23 + 2^22)) + as_Cm H 1500.

  Lemma nodup_ids_cons_ne : forall (b0 : block) (l : list block) b, List.NoDup (map blk_id (b0 :: l)) -> In b l -> blk_id b0 <> blk_id b.
  Proof. intros b0 l b ND Hb. exact (proj1 (nd_app [b0] l ND) b0 b (or_introl eq_refl) Hb). Qed.

  (* [comment removed for export] *)
  Definition fz_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LB0 LBc : list block) (LF : list fframe) (M0 : libmid) (D N lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (M' : libmid) (LBN : list block) (P : Z) (o : oblk) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR (Z_to_bv 64 FZ_R4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 P)
                       (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7 (Z_to_bv 64 ASHB15) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_CRYPTO_free) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp + -32) /\ stack0 m' lo shi
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ match o with None => P = 0
                      | Some (id, n) => In (id, P, n) (mid_errblocks M' ++ blocks_of P o ++ LBN ++ LB0)
                                        /\ (exists bs, rw_cells asegs m' P [CB (Z.to_nat n) bs]) /\ addressable m' P n end
      /\ as_RHEAP H s' (mid_errblocks M' ++ blocks_of P o ++ LBN ++ LB0) m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M0 M' /\ mid_newlib_ok M0 M' LBN /\ (exists b, mid_ctx M' = CtxReady b)
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
      /\ lb_bytes (blocks_of P o) <= 1500
      /\ rw_cells asegs m' (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)
      /\ as_RFS H LF m' /\ Forall (fs_scratch H LF) XS
      /\ xpres H LBc (bv_unsigned sp) (AERRNO_X ++ (LIBX ++ [(A_next_key + 4, A_key_lock)]) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - MIDCOST.

  (* [comment removed for export] *)
  Lemma fs_scratch_stack0_ok : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> stack0_ok iv.
  Proof.
    intros LF m iv R SC. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4).
    destruct SC as [->|(k & ff & fp & FF & E)].
    - eapply stack0_ok_aapp; [exact F4| lia| unfold AFS_FLAGS, AFS_SIZE; lia].
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [-> |[-> | ->]].
      + eapply stack0_ok_aapp; [exact P9| lia| lia].
      + eapply stack0_ok_aapp; [exact P9| lia| lia].
      + rewrite fshn_nsh by lia. apply stack0_ok_sh; acb; unfold AIMG_TOP in *; lia.
  Qed.


  (* [comment removed for export] *)
  Lemma parse_cost_bound : forall M, PARSE_COST H M <= as_Cm H (2^23 + 2^20) + as_Cf H (2^23 + 2^22).
  Proof.
    intros M. pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    unfold PARSE_COST, NEWMEMBUF_COST, READCFG_COST, BIOFREE_COST, STORE_SIZE, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, DECODE_BYTES, DECODE_CUM_BYTES.
    pose proof (CM0 (2^16) ltac:(lia)) as P16. pose proof (CF0 (2^16) ltac:(lia)) as Q16.
    assert (CX : 0 <= ctxph_cost H (mid_ctx M) <= as_Cm H (2^16) + as_Cf H (2^16)).
    { destruct (mid_ctx M); cbn [ctxph_cost]; unfold CTXINIT_COST, CTXINIT_BYTES; lia. }
    assert (EX : 0 <= errph_cost H (mid_err M) <= as_Cm H (2^16) + as_Cf H (2^16)).
    { destruct (mid_err M); cbn [errph_cost]; unfold ERRINIT_COST, ERRINIT_BYTES; lia. }
    (* [comment removed for export] *)
    pose proof (CMM 24 (2^16) ltac:(lia)). pose proof (CMM 128 (2^16) ltac:(lia)). pose proof (CMM 16 (2^16) ltac:(lia)). pose proof (CMM 32 (2^16) ltac:(lia)).
    pose proof (CMS (2^16) (2^16) ltac:(lia) ltac:(lia)). pose proof (CMS (2^17) (2^17) ltac:(lia) ltac:(lia)). pose proof (CMS (2^18) (2^18) ltac:(lia) ltac:(lia)).
    change (2^16 + 2^16) with (2^17) in *. change (2^17 + 2^17) with (2^18) in *. change (2^18 + 2^18) with (2^19) in *.
    pose proof (CMM (2^19) (2^20) ltac:(lia)). pose proof (CMS (2^23) (2^20) ltac:(lia) ltac:(lia)). pose proof (CM0 (2^16) ltac:(lia)).
    (* [comment removed for export] *)
    pose proof (CFM 0 (2^18) ltac:(lia)). pose proof (CFM (2^16) (2^18) ltac:(lia)). pose proof (CFM (24 + 2^17) (2^18) ltac:(lia)). pose proof (CFM 32 (2^18) ltac:(lia)).
    pose proof (CFM 16 (2^18) ltac:(lia)). pose proof (CFM 128 (2^18) ltac:(lia)).
    pose proof (CFS (2^18) (2^18) ltac:(lia) ltac:(lia)). pose proof (CFS (2^19) (2^19) ltac:(lia) ltac:(lia)). pose proof (CFS (2^20) (2^20) ltac:(lia) ltac:(lia)). pose proof (CFS (2^21) (2^21) ltac:(lia) ltac:(lia)).
    change (2^18 + 2^18) with (2^19) in *. change (2^19 + 2^19) with (2^20) in *. change (2^20 + 2^20) with (2^21) in *. change (2^21 + 2^21) with (2^22) in *.
    pose proof (CFS (2^23) (2^22) ltac:(lia) ltac:(lia)). pose proof (CF0 (2^18) ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma estr_bytes_bound : forall E, estrs_ok E -> 0 <= estr_bytes E <= 56 * Z.of_nat (length (es_slots E)).
  Proof.
    intros E OK. unfold estr_bytes. unfold estrs_ok in OK. induction OK as [|sl ss Psl F IH]; [cbn; lia|].
    change (fold_right (fun sl0 acc => slot_bytes sl0 + acc) 0 (sl :: ss)) with (slot_bytes sl + fold_right (fun sl0 acc => slot_bytes sl0 + acc) 0 ss).
    cbn [length]. rewrite Nat2Z.inj_succ. set (R := fold_right (fun sl0 acc => slot_bytes sl0 + acc) 0 ss) in *. unfold slot_bytes. lia.
  Qed.

  Lemma fuzz_spec : fuzz_stmt H ECHL.
  Proof.
    unfold fuzz_stmt. intros until errv.
    intros VIS A0 A1 DS DSL NR D16 DIN DEMPTY HP KREL LST BUD BUDC AUX AUXA SPB BHI SPA ST CEIL LO ERR MI RL TP RAE AC ADDR RFS LFB STK0 SSH CHN PF CHS TROK HAL.
    cbn [al_LIBST al_fresh al_is_fresh al_LIBX al_frames al_cost al_tr_ok al_PF ECHL] in *.
    unfold afuzz_live, afuzz_cnt, fuzz_cost, AFUZZ_LIVE, ATRANS_CNT, ALIB_CNT_MAX, ALIB_BYTES_MAX, AFUZZ_STACK in *.
    cbn [al_is_fresh al_cost ECHL] in *. unfold acost in HAL.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp a0 a1. rewrite (unsigned_lit ATP) in ERR by (unfold ATP; lia).
    assert (CEIL' : aceil <= bv_unsigned sp) by lia.
    pose proof (bytes_at_bound _ _ _ _ DS) as [DSB1 DSB2]. rewrite DSL in DSB2.
    assert (N0 : 0 <= N) by lia.
    pose proof (HFC TROK) as (HPC & HCC & HEC & HR1 & HBF1 & HBF2 & HMD & HCF & HECL).
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS). pose proof aceil_range as ACR.
    set (LB0 := LIB ++ LBc) in *.
    assert (SUBL : forall b, In b LIB -> In b LB0) by (intros b Hb; unfold LB0; apply in_or_app; left; exact Hb).
    assert (SUBC : forall b, In b LBc -> In b LB0) by (intros b Hb; unfold LB0; apply in_or_app; right; exact Hb).
    assert (LBY0 : lb_bytes LB0 = lb_bytes LIB + lb_bytes LBc) by (unfold LB0; apply lb_bytes_app_s).
    assert (LBC0 : length LB0 = (length LIB + length LBc)%nat) by (unfold LB0; apply length_app).
    assert (HB : forall b, In b LB0 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (ND0 := ah_nodup H HH _ _ _ HP). pose proof (nd_app LIB LBc ND0) as [DJLC _].
    assert (DCASE : N = 0 \/ exists pD, In (pD, D, N) LBc).
    { destruct (Z.eq_dec N 0) as [N00|N00]; [left; exact N00| right]. destruct (DIN ltac:(lia)) as [pD PIN]. exists pD. exact PIN. }
    assert (DPH : 0 < D /\ D + N <= aceil).
    { destruct DCASE as [N00|(pD & PIN)]; [rewrite (DEMPTY N00), N00; unfold AFUZZ_EMPTY; pose proof aceil_facts; unfold AIMG_TOP in *; lia|].
      pose proof (HB _ (SUBC _ PIN)) as (R1 & R2 & R3 & R4 & _). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4. unfold AIMG_TOP in R1. lia. }
    destruct DPH as [DP DH].
    (* [comment removed for export] *)
    assert (INIT : exists M0, LIBMID LIB m M0 /\ errst_canonical (mid_E M0)
                   /\ mid_bytes M0 <= (if is_fresh st then 2^17 else 0) /\ mid_cnt M0 <= (if is_fresh st then 1800 else 0)
                   /\ (is_fresh st = false -> (exists x, mid_ctx M0 = CtxReady x) /\ (exists c, mid_err M0 = ErrReady c) /\ lib_fits LIB)
                   /\ (is_fresh st = true -> LIB = [] /\ mid_ctx M0 = CtxFresh /\ mid_err M0 = ErrFresh)).
    { destruct st as [|i].
      - destruct (LIBMID_fresh LIB m LST RL) as [-> LM]. exists (mkMID 0 CtxFresh ErrFresh errst_zero false).
        unfold mid_bytes, mid_cnt. cbn [mid_E mid_ctx mid_err is_fresh ctxph_bytes errph_bytes ctxph_cnt errph_cnt].
        unfold CTXINIT_BYTES, ERRINIT_BYTES, CTXINIT_CNT, ERRINIT_CNT.
        split; [exact LM|]. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [intros; discriminate| intros _; repeat split; reflexivity].
      - destruct (LIBMID_inited LIB m i LST RL ltac:(intros b Hb; pose proof (HB _ (SUBL _ Hb)) as (_ & K2 & _ & K4 & _); split; [exact K2| exact K4])) as (E & CE & SZ & LM).
        exists (mkMID 1 (CtxReady (li_ctx i)) (ErrReady (li_chain i)) E (li_vdso_done i)).
        unfold mid_bytes, mid_cnt. cbn [mid_E mid_ctx mid_err is_fresh ctxph_bytes errph_bytes ctxph_cnt errph_cnt].
        split; [exact LM|]. split; [exact CE|]. split; [lia|]. split; [lia|].
        split; [intros _; split; [eexists; reflexivity| split; [eexists; reflexivity| exact SZ]]| intros; discriminate]. }
    destruct INIT as (M0 & LM0 & CE0 & MB0 & MC0 & INITED & FRESH).
    assert (E00 : mid_errblocks M0 = []) by (unfold mid_errblocks; apply blocks_ERRST_canonical; exact CE0).
    pose proof (ctxph_nonneg H HH (mid_ctx M0)) as (NB0a & NB0b & _). pose proof (errph_nonneg (mid_err M0)) as (NB0c & NB0d). pose proof (parse_stack_max M0) as PS0.
    pose proof LM0 as (IM0 & MF0 & CP0 & EPm0 & _).
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    (* [comment removed for export] *)
    set (Bmiss := fun (X : list (Z * Z)) (A0 n0 : Z) => forall q, rin_ivs X q -> ~ (A0 <= q < A0 + n0) /\ ~ (sh A0 <= q < sh A0 + nsh n0)).
    assert (BM_nil : forall A0 n0, Bmiss [] A0 n0) by (intros A0 n0 q K; destruct K).
    assert (BM_app : forall X Y A0 n0, Bmiss X A0 n0 -> Bmiss Y A0 n0 -> Bmiss (X ++ Y) A0 n0).
    { intros X Y A0 n0 DX DY q K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (DX q K)| exact (DY q K)]. }
    assert (SHTOP : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (BM_img : forall X A0 n0, Forall in_aimg X -> AIMG_TOP <= A0 -> 0 <= n0 -> aapp A0 n0 -> Bmiss X A0 n0).
    { intros X A0 n0 FX P1 P2 P3 q K. pose proof (sh_aapp_range A0 n0 P3 P2) as (S1 & S2 & S3).
      destruct (rin_ivs_In _ _ K) as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as W. unfold in_aimg in W. unfold AIMG_TOP in *. lia. }
    assert (BM_blk : forall s' L' m' b b0 lo' hi', as_RHEAP H s' L' m' -> In b L' -> In b0 L' -> blk_id b <> blk_id b0 ->
              blk_addr b <= lo' -> hi' <= blk_addr b + blk_size b -> Bmiss [(lo', hi')] (blk_addr b0) (blk_size b0)).
    { intros s' L' m' b b0 lo' hi' HP' Hb Hb0 NE B1 B2 q K. cbn [rin_ivs fst snd] in K. destruct K as [K|[]].
      pose proof (ah_disj H HH _ _ _ _ _ HP' Hb Hb0 NE) as DJ.
      pose proof (ah_blocks H HH _ _ _ _ HP' Hb) as (_ & _ & Q3 & _ & _ & _ & Q7). pose proof (aapp_not_shadowland _ _ Q7).
      pose proof (ah_blocks H HH _ _ _ _ HP' Hb0) as (_ & _ & R3 & _ & _ & _ & R7). pose proof (sh_aapp_range _ _ R7 R3) as (S1 & S2 & S3).
      unfold ALOWSH_LO, AHI_LO in *. lia. }
    assert (BM_xs : forall s' L' m0 mm XS b0, as_RHEAP H s' L' m0 -> In b0 L' -> as_RFS H LF mm -> Forall (fs_scratch H LF) XS -> Bmiss XS (blk_addr b0) (blk_size b0)).
    { intros s' L' m0 mm XS b0 HP' Hb0 RF FXS q K. destruct (rin_ivs_In _ _ K) as (iv & Hiv & R).
      pose proof (fs_scratch_off_block H HH s' L' m0 [b0] LF mm iv q HP' ltac:(intros b [<-|[]]; exact Hb0) RF (proj1 (Forall_forall _ _) FXS iv Hiv) R) as [NBq NSq].
      split; intros Kq; [apply NBq| apply NSq]; exists b0; (split; [left; reflexivity| exact Kq]). }
    assert (BX_bytes : forall L SP X mm mm' A0 bs b0, xpres H L SP X mm mm' -> bytes_at asegs mm A0 bs -> In b0 L ->
              blk_addr b0 <= A0 -> A0 + Z.of_nat (length bs) <= blk_addr b0 + blk_size b0 -> Bmiss X (blk_addr b0) (blk_size b0) -> bytes_at asegs mm' A0 bs).
    { intros L SP X mm mm' A0 bs b0 XP BA Hb0 B1 B2 BM. eapply bytes_at_agree; [eapply (magree_of_xpres H); exact XP| exact BA|].
      intros q Hq. unfold in_range in Hq. split; [right; right; left; exists b0; split; [exact Hb0| lia]|]. intros K. exact (proj1 (BM q K) ltac:(lia)). }
    assert (BX_cells : forall L SP X mm mm' A0 cs b0, xpres H L SP X mm mm' -> rw_cells asegs mm A0 cs -> In b0 L ->
              blk_addr b0 <= A0 -> A0 + Z.of_nat (cells_size cs) <= blk_addr b0 + blk_size b0 -> Bmiss X (blk_addr b0) (blk_size b0) -> rw_cells asegs mm' A0 cs).
    { intros L SP X mm mm' A0 cs b0 XP RC Hb0 B1 B2 BM. eapply rw_cells_agree; [eapply (magree_of_xpres H); exact XP| exact RC|].
      intros q Hq. unfold in_range in Hq. split; [right; right; left; exists b0; split; [exact Hb0| lia]|]. intros K. exact (proj1 (BM q K) ltac:(lia)). }
    assert (BX_addr : forall L SP X mm mm' b0, xpres H L SP X mm mm' -> addressable mm (blk_addr b0) (blk_size b0) -> In b0 L ->
              Bmiss X (blk_addr b0) (blk_size b0) -> addressable mm' (blk_addr b0) (blk_size b0)).
    { intros L SP X mm mm' b0 XP AD Hb0 BM. eapply addressable_agreeR; [eapply (magree_of_xpres H); exact XP| | exact AD].
      intros q Hq. split; [right; right; right; left; exists b0; split; [exact Hb0| exact Hq]|]. intros K. exact (proj2 (BM q K) Hq). }
    (* [comment removed for export] *)
    assert (DSX : forall L SP X mm mm', xpres H L SP X mm mm' -> bytes_at asegs mm D ds -> (forall b, In b LBc -> In b L) ->
                  (forall pD, In (pD, D, N) LBc -> Bmiss X D N) -> bytes_at asegs mm' D ds).
    { intros L SP X mm mm' XP BA SUB DX. destruct (Z.eq_dec N 0) as [N00|N00].
      - destruct ds; [| cbn in DSL; lia]. destruct BA as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - destruct (DIN ltac:(lia)) as [pD PIN].
        exact (BX_bytes L SP X mm mm' D ds (pD, D, N) XP BA (SUB _ PIN) ltac:(cbn; lia) ltac:(cbn; lia) (DX pD PIN)). }
    assert (ADX : forall L SP X mm mm', xpres H L SP X mm mm' -> (1 <= N -> addressable mm D N) -> (forall b, In b LBc -> In b L) ->
                  (forall pD, In (pD, D, N) LBc -> Bmiss X D N) -> 1 <= N -> addressable mm' D N).
    { intros L SP X mm mm' XP AD SUB DX N1. destruct (DIN N1) as [pD PIN].
      exact (BX_addr L SP X mm mm' (pD, D, N) XP (AD N1) (SUB _ PIN) (DX pD PIN)). }
    assert (XLT : forall X q, Forall (fun iv : Z * Z => snd iv <= aceil) X -> rin_ivs X q -> q < aceil).
    { intros X q FX K. destruct (rin_ivs_In _ _ K) as (iv & Hiv & Riv). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as W. cbn beta in W. lia. }
    (* [comment removed for export] *)
    assert (PAYB_img : forall X pD, In (pD, D, N) LBc -> Forall in_aimg X -> Bmiss X D N).
    { intros X pD PIN FX. pose proof (HB _ (SUBC _ PIN)) as (P1 & P2 & P3 & P4 & P5 & P6). exact (BM_img X D N FX P1 P3 P6). }
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply af_seg1 with (lo := lo) (N := N); [reflexivity| lia| lia| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW1 : Forall (aclient_write_ok H LB0) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB0 m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    pose proof (aauxv_ok_bounds _ _ AUXA) as ACB.
    assert (AUXA1 : aauxv_ok m1 B) by (eapply aauxv_ok_frame; [exact AUXA| exact MU1| exact WM1| apply Forall_cons; [apply aauxv_win_ok_stack; lia| apply Forall_nil]]).
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (XP1 : xpres H LB0 (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB0 _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn [fst snd].
      pose proof (ah_fsb H HH _ _ _ HP) as (FSB1 & FSB2 & FSB3 & FSB4). unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
    assert (STK1 : stack0 m1 lo shi) by (eapply stack0_transport; [exact STK0| exact MU1| exact WM1|]; constructor; [left; cbn; unfold AHI_LO; lia| constructor]).
    pose proof (LIBMID_xpres0_any H LIB LB0 (bv_unsigned sp) m m1 M0 LM0 XP1 SUBL ltac:(rewrite E00; intros b [])) as LM1.
    pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & GM1 & _ & _ & _ & _ & _ & RL1 & _).
    assert (DS1 : bytes_at asegs m1 D ds) by (eapply DSX; [exact XP1| exact DS| exact SUBC| intros pD _; apply BM_nil]).
    assert (AD1 : 1 <= N -> addressable m1 D N) by (intros N1; eapply ADX; [exact XP1| exact ADDR| exact SUBC| intros pD _; apply BM_nil| exact N1]).
    assert (CHA : forall mm, as_chain H mm N []) by (intros mm; apply (ah_chain_nil H HH); left; lia).
    pose proof (parse_cost_bound M0) as PCB0.
    (* [comment removed for export] *)
    pose proof (parse_one_spec H HX CNX CFX PF9new PF9free RCFG) as P1. unfold parse_one_stmt in P1.
    eapply (ah_seq H HH).
    { eapply P1 with (lo := lo) (B := B) (LIB := LIB) (LB := LB0) (M := M0) (D := D) (N := N) (ds := ds) (s := s) (LF := LF) (shi := shi) (CH := []);
        [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?E00; cbn [app]; rewrite ?unsigned_lit by (unfold FZ_R1, R_fuzz_parse_one; lia).
      all: lazymatch goal with
           | |- 0 <= N < _ => lia
           | |- zlength _ = _ => exact DSL
           | |- 1 <= _ -> exists pD, _ => intros K; destruct (DIN K) as [pD PIN]; exists pD; split; [apply SUBC; exact PIN| intros b Hb; exact (DJLC _ _ Hb PIN)]
           | |- _ = 0 -> _ => intros K; rewrite (DEMPTY K); reflexivity
           | |- mid_closed_ok _ _ => unfold mid_closed_ok; destruct (mid_err M0); [exact HEC| exact I]
           | |- ctxph_closed_ok _ _ => destruct (mid_ctx M0); [exact HCC| exact I]
           | |- lb_bytes _ + _ + _ <= _ => unfold PARSE_BYTES, DECODE_BYTES, ERRSTR_BYTES; clear - BUD MB0; destruct (is_fresh st); lia
           | |- Z.of_nat (length _) + _ + _ <= _ => unfold PARSE_CNT, DECODE_CNT, ERRSTR_CNT; clear - BUDC MC0; destruct (is_fresh st); lia
           | |- _ <= _ - PARSE_STACK _ => clear - LO PS0; lia
           | |- (length _ + _ <= _)%nat => unfold PARSE_LF, READCFG_LF, READCFG_MAXLIVE, AL_FRAMES, AFS_MAXLIVE in *; clear - LFB; lia
           | |- as_chain _ _ _ _ => apply CHA
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ PF_storenew _ _ => apply (pf_ok_closed H); exact HR1
           | |- parse_closed_ok _ _ _ _ => apply HPC
           | |- pf_ok _ PF_biofree _ _ => apply (pf_ok_closed H); exact HBF1
           | |- _ <= as_AL _ _ => unfold ACOST_BYTES in HAL; pose proof (CMM (2^23 + 2^20) (2^25) ltac:(lia)); pose proof (CFM (2^23 + 2^22) (2^25) ltac:(lia)); clear - HAL PCB0 H0 H1; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- aauxv_ok _ _ => exact AUXA1
           | |- _ => first [exact DS1| exact LM1| exact SUBL| exact HP1| exact KREL1| exact AUX1| exact BHI| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity
                       | exact SP16'| exact STK1| exact AC1| exact AD1| exact RFS1| exact RL1| lia | match goal with |- ?G => idtac "LEFTP1:" G end]
           end. }
    clear P1. intros [msF2 mo2] PO. unfold parse_one_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & M1 & LBN1 & XS2 &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & RL2 & ST2 & STK2 & ERR2 & AUX2 & HP2 & LM2 & STEP1 & NEW1 & CTX1 & EC1 & EB1 & DS2 & AD2 & FXS2 & RFS2 & XP2 & AL2).
    rewrite ?E00 in HP2. cbn [app] in HP2.
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    destruct M1 as [f1 cph1 eph1 Em1 vd1]. pose proof (proj1 STEP1) as F1. cbn [mid_flag] in F1. subst f1.
    destruct CTX1 as [bx1 CTX1]. cbn [mid_ctx] in CTX1. subst cph1.
    pose proof (newlib_bounds _ _ _ STEP1 NEW1) as (NL1 & NL2 & NL5 & NL6).
    pose proof (ctxph_nonneg H HH (CtxReady bx1)) as (NB1a & NB1b & _). pose proof (errph_nonneg eph1) as (NB1c & NB1d).
    pose proof (parse_stack_max (mkMID 1 (CtxReady bx1) eph1 Em1 vd1)) as PS1. pose proof (parse_cost_bound (mkMID 1 (CtxReady bx1) eph1 Em1 vd1)) as PCB1.
    set (E1 := mid_errblocks (mkMID 1 (CtxReady bx1) eph1 Em1 vd1)) in *.
    assert (HB2 : forall b, In b (E1 ++ LBN1 ++ LB0) -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP2 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (ND2 := ah_nodup H HH _ _ _ HP2).
    pose proof LM2 as (IM2 & MF2 & _ & EPm2 & _ & _ & _ & _ & GM2 & _). cbn [mid_flag] in MF2.
    assert (SUBA2 : forall b, In b (LBN1 ++ LIB) -> In b (E1 ++ LBN1 ++ LB0)).
    { intros b Hb. apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (SUBC2 : forall b, In b LBc -> In b (E1 ++ LBN1 ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb).
    assert (SUBE2 : forall b, In b E1 -> In b (E1 ++ LBN1 ++ LB0)) by (intros b Hb; apply in_or_app; left; exact Hb).
    pose proof (nd_app E1 (LBN1 ++ LB0) ND2) as [DJ2E ND2a]. pose proof (nd_app LBN1 LB0 ND2a) as [DJ2N _].
    assert (DJX2 : idsdisj (LBN1 ++ LIB) LBc).
    { intros b b' Hb Hb'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply DJ2N; [exact Hb| apply SUBC; exact Hb']| apply DJLC; assumption]. }
    assert (XB2 : Forall (fun iv : Z * Z => snd iv <= aceil) (memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M0) ++ XS2)).
    { apply Forall_below_app; [apply Forall_below_aimg; apply aimg_memflag|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_CTX_X|].
      apply Forall_below_app; [apply Forall_below_aimg; apply aimg_ERR_XE|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_VDSO_X|].
      apply Forall_below_app; [eapply errph_foot_below; [exact EPm0| intros b Hb; exact (proj1 (proj2 (HB _ (SUBL _ Hb))))]|].
      pose proof (fs_scratch_range_Forall H HH _ _ _ RFS1 FXS2) as K. eapply Forall_impl; [| exact K]. intros [u w] Ku. cbn in Ku |- *. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FR1| left; cbn; lia|]. eapply Forall_avoid_hi; [exact XB2| lia]. }
    assert (AUXA2 : aauxv_ok m2 B).
    { eapply aauxv_ok_xpres; [exact AUXA1| exact XP2| lia|].
      apply Forall_app; split; [apply aauxv_memflag; exact ACB|]. apply Forall_app; split; [apply aauxv_CTX_X; exact ACB|].
      apply Forall_app; split; [apply aauxv_ERR_XE; exact ACB|]. apply Forall_app; split; [apply aauxv_VDSO_X; exact ACB|].
      apply Forall_app; split; [eapply aauxv_errph_foot; [exact ACB| exact EPm0| intros b Hb; pose proof (HB _ (SUBL _ Hb)) as (K1 & K2 & _); split; [exact K1| exact K2]]|].
      apply aauxv_fs_scratch; [exact ACB| exact (fs_scratch_range_Forall H HH _ _ _ RFS1 FXS2)]. }
    (* [comment removed for export] *)
    set (XT := AERRNO_X ++ (LIBX ++ [(A_next_key + 4, A_key_lock)])) in *.
    assert (XTOP : forall (Lx Lh Lall : list block) mx cph eph sh mh SPx mA mB XS,
              ERRPH_mid Lx mx cph eph -> as_RHEAP H sh Lh mh -> (forall b, In b Lx -> In b Lh) -> (forall b, In b LBc -> In b Lh) -> idsdisj Lx LBc ->
              xpres H Lall SPx (memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X ++ errph_foot eph ++ XS) mA mB ->
              (forall b, In b LBc -> In b Lall) -> SPx <= bv_unsigned sp -> xpres H LBc (bv_unsigned sp) (XT ++ XS) mA mB).
    { intros Lx Lh Lall mx cph eph sh mh SPx mA mB XS EPm HPh SUBx SUBc DJ XP SUB LE.
      eapply (xpres_drop_nonclient H _ _ (XT ++ XS) (errph_foot eph)).
      - eapply xpres_weaken; [exact XP| exact LE| exact SUB|]. intros q Hq.
        apply rin_ivs_app in Hq. destruct Hq as [Q1|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; unfold XT; apply XF_libx; apply rin_ivs_app; left; exact Q1|].
        apply rin_ivs_app in Hq. destruct Hq as [Q2|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; unfold XT; apply XF_libx; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Q2|].
        apply rin_ivs_app in Hq. destruct Hq as [Q3|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; unfold XT; apply XF_libx; do 2 (apply rin_ivs_app; right); apply rin_ivs_app; left; exact Q3|].
        apply rin_ivs_app in Hq. destruct Hq as [Q4|Hq]; [apply rin_ivs_app; left; apply rin_ivs_app; left; unfold XT; apply XF_libx; do 3 (apply rin_ivs_app; right); exact Q4|].
        apply rin_ivs_app in Hq. destruct Hq as [Q5|Q6]; [apply rin_ivs_app; right; exact Q5| apply rin_ivs_app; left; apply rin_ivs_app; right; exact Q6].
      - intros q Hq HC. destruct eph as [|c]; cbn [errph_foot rin_ivs fst snd] in Hq; [exact Hq|]. destruct Hq as [Hq|[]].
        destruct cph as [|x]; cbn [ERRPH_mid ERRPH] in EPm; [destruct EPm|]. destruct EPm as [_ ECH].
        pose proof ECH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
        pose proof (client_outside_block H HH _ _ _ (ec_es c) LBc (bv_unsigned sp) q HPh (SUBx _ I5) SUBc
                      ltac:(intros b b' Hb Hb'; destruct Hb as [<-|[]]; apply DJ; [exact I5| exact Hb']) CEIL' HC) as K.
        rewrite Z5 in K. unfold ERRST_SIZE in *. lia. }
    assert (XC1 : forall X, xpres H LBc (bv_unsigned sp) X m m1) by (intros X; eapply xpres_weaken; [exact XP1| lia| exact SUBC| intros q []]).
    assert (XC2 : xpres H LBc (bv_unsigned sp) (XT ++ XS2) m m2).
    { eapply xpres_trans; [apply XC1|]. eapply (XTOP LIB LB0 LB0); [exact EPm0| exact HP| exact SUBL| exact SUBC| exact DJLC| exact XP2| exact SUBC| lia]. }
    (* [comment removed for export] *)
    assert (BUDGETC : MIDCOST + as_Cf H 1500 + (as_Cm H (2^16) + as_Cf H (2^16) + as_Cf H 896) <= as_Cm H (2^25) + as_Cf H (2^25)).
    { unfold MIDCOST.
        pose proof (CMS (2^23 + 2^20) (2^23 + 2^20) ltac:(lia) ltac:(lia)) as K1; pose proof (CMS (2^23 + 2^20 + (2^23 + 2^20)) 1500 ltac:(lia) ltac:(lia)) as K2;
        pose proof (CMS (2^23 + 2^20 + (2^23 + 2^20) + 1500) (2^16) ltac:(lia) ltac:(lia)) as K3; pose proof (CMM (2^23 + 2^20 + (2^23 + 2^20) + 1500 + 2^16) (2^25) ltac:(lia)) as K4;
        pose proof (CFS (2^23 + 2^22) (2^23 + 2^22) ltac:(lia) ltac:(lia)) as L1; pose proof (CFS (2^23 + 2^22 + (2^23 + 2^22)) 1500 ltac:(lia) ltac:(lia)) as L2;
        pose proof (CFS (2^23 + 2^22 + (2^23 + 2^22) + 1500) (2^16) ltac:(lia) ltac:(lia)) as L3; pose proof (CFS (2^23 + 2^22 + (2^23 + 2^22) + 1500 + 2^16) 896 ltac:(lia) ltac:(lia)) as L4;
        pose proof (CFM (2^23 + 2^22 + (2^23 + 2^22) + 1500 + 2^16 + 896) (2^25) ltac:(lia)) as L5;
        clear - K1 K2 K3 K4 L1 L2 L3 L4 L5; lia. }
    assert (BUDGET : MIDCOST + as_Cf H 1500 + (as_Cm H (2^16) + as_Cf H (2^16) + as_Cf H 896) <= as_AL H s) by (unfold ACOST_BYTES in HAL; clear - HAL BUDGETC; lia).
    pose proof (CM0 N ltac:(lia)) as CMN0. pose proof (CF0 N ltac:(lia)) as CFN0. pose proof (CF0 1500 ltac:(lia)) as CF15. pose proof (CM0 1500 ltac:(lia)) as CM15.
    pose proof (CM0 (2^16) ltac:(lia)) as CM16. pose proof (CF0 (2^16) ltac:(lia)) as CF16. pose proof (CF0 896 ltac:(lia)) as CF896.
    assert (PCNN : forall M, 0 <= PARSE_COST H M).
    { intros M. unfold PARSE_COST, NEWMEMBUF_COST, READCFG_COST, BIOFREE_COST. pose proof (ctxph_nonneg H HH (mid_ctx M)) as (_ & _ & _ & K1).
      assert (0 <= errph_cost H (mid_err M)) by (destruct (mid_err M); cbn [errph_cost]; [unfold ERRINIT_COST; pose proof (CM0 ERRINIT_BYTES ltac:(unfold ERRINIT_BYTES; lia)); pose proof (CF0 ERRINIT_BYTES ltac:(unfold ERRINIT_BYTES; lia)); lia| lia]).
      pose proof (CM0 STORE_SIZE ltac:(unfold STORE_SIZE; lia)). pose proof (CM0 BIO_SIZE ltac:(unfold BIO_SIZE; lia)). pose proof (CM0 BIOBUFMEM_SIZE ltac:(unfold BIOBUFMEM_SIZE; lia)).
      pose proof (CM0 BUFMEM_SIZE ltac:(unfold BUFMEM_SIZE; lia)). pose proof (CF0 0 ltac:(lia)). pose proof (CM0 DECODE_CUM_BYTES ltac:(unfold DECODE_CUM_BYTES; lia)). pose proof (CF0 DECODE_CUM_BYTES ltac:(unfold DECODE_CUM_BYTES; lia)).
      pose proof (CF0 (STORE_SIZE + DECODE_BYTES) ltac:(unfold STORE_SIZE, DECODE_BYTES; lia)). pose proof (CF0 BUFMEM_SIZE ltac:(unfold BUFMEM_SIZE; lia)). pose proof (CF0 BIOBUFMEM_SIZE ltac:(unfold BIOBUFMEM_SIZE; lia)). pose proof (CF0 BIO_SIZE ltac:(unfold BIO_SIZE; lia)). lia. }
    assert (CMD : CMEMDUP_STACK = 8288) by reflexivity. assert (CFSK : CFREE_STACK = 8208) by reflexivity.
    (* [comment removed for export] *)
    assert (MID : as_SR H (fz_mid ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB0 LBc LF M0 D N lo B shi m mo) (mkCfg msF2 mo2)).
    { assert (CASES : (32 <= N < 1500) \/ (N < 32 \/ 1500 <= N)) by lia. destruct CASES as [GATE|GATE].
      - (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply af_seg2a; [exact GATE| exact MI2]|]. intros msF3 mo3 KREL3 MP3 VIS3.
        destruct DCASE as [N00|(pD & PIN)]; [lia|].
        assert (CMN : as_Cm H N <= as_Cm H 1500) by (apply CMM; lia). assert (CFN : as_Cf H N <= as_Cf H 1500) by (apply CFM; lia).
        pose proof (acmemdup_spec H HH) as MD. unfold cmemdup_stmt in MD.
        eapply (ah_seq H HH).
        { eapply MD with (lo := lo) (B := B) (LB := E1 ++ LBN1 ++ LB0) (s := s2') (D := D) (bs := ds) (v := 1) (bD := (pD, D, N)) (CH := []);
            [exact VIS3| reflexivity| unfold zlength; rewrite DSL; reflexivity| ..]; unfold zlength; rewrite ?DSL; rewrite ?unsigned_lit by (unfold FZ_R2, R_fuzz_CRYPTO_memdup; lia).
          all: lazymatch goal with
               | |- 1 <= N <= _ => lia
               | |- In _ _ => apply SUBC2; exact PIN
               | |- blk_addr _ <= _ => cbn; lia
               | |- _ + _ <= blk_addr _ + blk_size _ => cbn; lia
               | |- lb_bytes _ + _ <= _ => rewrite !lb_bytes_app_s; unfold ERRSTR_BYTES in EB1; unfold mid_bytes in NL1, MB0; cbn [mid_ctx mid_err ctxph_bytes] in NL1; clear - BUD LBY0 EB1 NL1 MB0 NB1c NB0a NB0c GATE; destruct (is_fresh st); lia
               | |- Z.of_nat (length _) + _ <= _ => rewrite !length_app, !Nat2Z.inj_add; unfold ERRSTR_CNT in EC1; unfold mid_cnt in NL2, MC0; cbn [mid_ctx mid_err ctxph_cnt] in NL2; clear - BUDC LBC0 EC1 NL2 MC0 NB1d NB0b NB0d; destruct (is_fresh st); lia
               | |- _ <= _ - CMEMDUP_STACK => rewrite CMD; clear - LO; lia
               | |- as_chain _ _ _ _ => apply CHA
               | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
               | |- pf_ok _ _ _ _ => apply (pf_ok_closed H); exact HMD
               | |- _ <= as_AL _ _ => unfold MIDCOST in BUDGET; clear - BUDGET AL2 PCB0 CMN CMN0 CFN0 CF15 CM15 CM16 CF16 CF896 PCNN; pose proof (PCNN M0); lia
               | |- accessible _ _ _ => eapply addressable_accessible; [exact (AD2 ltac:(lia))| lia| lia| unfold AAPP_HI; lia]
               | |- MEMFLAG _ _ => exact MF2
               | |- _ mod 2 = 0 => reflexivity
               | |- _ => first [exact DS2| exact HP2| exact KREL3| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16'| exact AC2| exact IM2| exact GM2| lia
                           | match goal with |- ?G => idtac "LEFTMD:" G end]
               end. }
        clear MD. intros [msF4 mo4] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2' & c3' & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & A & p & s3' &
                        VIS4 & KREL4 & MP4 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & BR3 & HP3 & BLK3 & ADC3 & MF3 & IM3 & GM3 & AL3).
        unfold zlength in BR3, HP3, ADC3, AL3. rewrite DSL in BR3, HP3, ADC3, AL3.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia. rewrite (unsigned_lit ATP) in ERR3 by (unfold ATP; lia).
        pose proof BR3 as (AP & A16 & _ & ATOP & ACE & AFSB & AAP).
        assert (AUXA3 : aauxv_ok m3 B) by (eapply aauxv_ok_xpres; [exact AUXA2| exact XP3| lia| apply aauxv_memflag; exact ACB]).
        pose proof (LIBMID_mf H HH s2' m2 (LBN1 ++ LIB) (E1 ++ LBN1 ++ LB0) (bv_unsigned sp + -32) m2 m3 _ bx1 HP2 LM2 eq_refl XP3 SUBA2 SUBE2 MF3) as LM3.
        cbn [mid_ctx mid_err mid_E mid_vdso] in LM3.
        assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
        { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP3); [exact FR2| left; cbn; lia|]. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        assert (RFS3 : as_RFS H LF m3) by (eapply (RFS_via_xpres H HH); [exact RFS2| exact XP3|]; unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP; apply Forall_cons; [cbn; lia| apply Forall_nil]).
        assert (STK3 : stack0 m3 lo shi) by (eapply (stack0_xpres H); [exact XP3| exact STK2| apply stack0_ok_of_aimg; apply aimg_memflag]).
        assert (XC3 : xpres H LBc (bv_unsigned sp) (XT ++ XS2) m m3).
        { eapply xpres_trans; [exact XC2|]. eapply xpres_weaken; [exact XP3| lia| exact SUBC2|]. intros q Hq. apply rin_ivs_app; left. unfold XT. apply XF_libx. apply rin_ivs_app. left. exact Hq. }
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply af_seg3 with (bs := ds); [exact GATE| exact AP| exact ACE| exact AAP| unfold zlength; exact DSL| exact BLK3| | exact MI3]|].
        { eapply addressable_accessible; [exact ADC3| lia| lia| unfold AAPP_HI; lia]. }
        intros msF5 mo5 KREL5 MP5 (c2 & c3 & c4x & m4 & bs' & VIS5 & MU4 & WM4 & MI4 & BLK4 & LEN4).
        assert (HP4 : as_RHEAP H s3' ((p, A, N) :: E1 ++ LBN1 ++ LB0) m4).
        { eapply (ah_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (p, A, N). split; [left; reflexivity| cbn; lia]. }
        assert (AUX4 : as_rauxv_ok H m4 B).
        { eapply (ah_rauxv_frame H HH) with (LB := (p, A, N) :: E1 ++ LBN1 ++ LB0); [exact AUX3| exact MU4| exact WM4|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (p, A, N). split; [left; reflexivity| cbn; lia]. }
        assert (AUXA4 : aauxv_ok m4 B).
        { eapply aauxv_ok_frame; [exact AUXA3| exact MU4| exact WM4|]. apply Forall_cons; [| apply Forall_nil]. apply aauxv_win_ok_low; [exact ACB| cbn; lia| right; cbn; unfold AAUXV_CELL, AIMG_TOP in *; lia]. }
        assert (AC4 : ACONST m4).
        { eapply ACONST_frame_win; [exact AC3| exact MU4| exact WM4|]. apply Forall_cons; [| apply Forall_nil]. right. exists A, N. split; [exact AAP| cbn; lia]. }
        assert (ERR4 : rw_cells asegs m4 (ATP + -164) [C4 errv3]) by (eapply errno_across; [exact ERR3| exact MU4| exact WM4| unfold ATP, AIMG_TOP in *; cbn; lia]).
        assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4| cbn; lia]).
        apply (stk_transport_disjoint asegs _ m3 m4 _ _ ST3) in MU4 as ST4; [| exact WM4| cbn; lia].
        assert (XP4 : xpres H (E1 ++ LBN1 ++ LB0) (bv_unsigned sp + -32) [] m3 m4).
        { eapply (xpres_of_munch_fresh H HH); [exact HP3| lia| exact MU4| exact WM4|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
        assert (RFS4 : as_RFS H LF m4) by (eapply (RFS_via_xpres H HH); [exact RFS3| exact XP4| apply Forall_nil]).
        assert (STK4 : stack0 m4 lo shi) by (eapply (stack0_xpres H); [exact XP4| exact STK3| apply Forall_nil]).
        assert (ADC4 : addressable m4 A N).
        { eapply addressable_transport; [exact ADC3| exact MU4| exact WM4|]. pose proof (sh_aapp_range A N AAP ltac:(lia)) as (S1 & S2 & S3). pose proof (aapp_not_shadowland A N AAP).
          cbn. unfold ALOWSH_LO, AHI_LO in *. lia. }
        pose proof (LIBMID_xpres0 H (LBN1 ++ LIB) (E1 ++ LBN1 ++ LB0) (bv_unsigned sp + -32) m3 m4 _ bx1 LM3 eq_refl XP4 SUBA2 SUBE2) as LM4.
        pose proof LM4 as (IM4 & MF4 & _ & EPm4 & _ & _ & _ & _ & GM4 & _ & _ & _ & _ & _ & RL4 & _).
        assert (DS4 : bytes_at asegs m4 A bs') by (pose proof (rw_cells_bytes_at _ _ _ _ BLK4) as K; cbn [cells_bytes cbytes app] in K; rewrite app_nil_r in K; exact K).
        assert (XC4 : xpres H LBc (bv_unsigned sp) (XT ++ XS2) m m4).
        { eapply xpres_trans; [exact XC3|]. eapply xpres_weaken; [exact XP4| lia| exact SUBC2| intros q []]. }
        assert (HB4 : forall b, In b ((p, A, N) :: E1 ++ LBN1 ++ LB0) -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
        { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP4 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
        assert (ND4 := ah_nodup H HH _ _ _ HP4).
        (* [comment removed for export] *)
        pose proof (parse_one_spec H HX CNX CFX PF9new PF9free RCFG) as P2. unfold parse_one_stmt in P2.
        eapply (ah_seq H HH).
        { eapply P2 with (lo := lo) (B := B) (LIB := LBN1 ++ LIB) (LB := (p, A, N) :: LBN1 ++ LB0) (M := mkMID 1 (CtxReady bx1) eph1 Em1 vd1) (D := A) (N := N) (ds := bs') (s := s3') (LF := LF) (shi := shi) (CH := []);
            [exact VIS5| reflexivity| reflexivity| ..]; cbn [mid_errblocks mid_E mid_ctx mid_err mid_bytes mid_cnt ctxph_bytes ctxph_cnt]; change (blocks_ERRST Em1) with E1;
            rewrite ?unsigned_lit by (unfold FZ_R3, R_fuzz_parse_one_2; lia).
          all: lazymatch goal with
               | |- 0 <= N < _ => lia
               | |- zlength _ = _ => exact LEN4
               | |- 1 <= _ -> exists pD0, _ => intros _; exists p; split; [left; reflexivity| intros b Hb; apply not_eq_sym; apply (nodup_ids_cons_ne (p, A, N) _ b ND4); exact (SUBA2 _ Hb)]
               | |- _ = 0 -> _ => intros K; exfalso; clear - K GATE; lia
               | |- forall b, In b _ -> In b _ => intros b Hb; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]
               | |- mid_closed_ok _ _ => unfold mid_closed_ok; cbn [mid_err]; destruct eph1; [exact HEC| exact I]
               | |- ctxph_closed_ok _ _ => exact I
               | |- as_RHEAP _ _ _ _ => eapply PERM; [exact HP4| apply Permutation_middle]
               | |- lb_bytes _ + _ + _ <= _ => unfold mid_errblocks, mid_bytes; cbn [mid_E mid_ctx mid_err ctxph_bytes]; change (blocks_ERRST Em1) with E1;
                                                   rewrite lb_bytes_app_s, lb_bytes_cons, lb_bytes_app_s; cbn [blk_size snd]; unfold PARSE_BYTES, DECODE_BYTES, ERRSTR_BYTES in *;
                                                   unfold mid_bytes in NL1, MB0; cbn [mid_ctx mid_err ctxph_bytes] in NL1; clear - BUD LBY0 MB0 NB1c NL1 EB1 GATE NB0a NB0c; destruct (is_fresh st); lia
               | |- Z.of_nat (length _) + _ + _ <= _ => unfold mid_errblocks, mid_cnt; cbn [mid_E mid_ctx mid_err ctxph_cnt]; change (blocks_ERRST Em1) with E1;
                                                             rewrite length_app; cbn [length]; rewrite length_app, ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add; unfold PARSE_CNT, DECODE_CNT, ERRSTR_CNT in *;
                                                             unfold mid_cnt in NL2, MC0; cbn [mid_ctx mid_err ctxph_cnt] in NL2; clear - BUDC LBC0 MC0 NB1d NL2 EC1 NB0b NB0d; destruct (is_fresh st); lia
               | |- _ <= _ - PARSE_STACK _ => clear - LO PS1; lia
               | |- (length _ + _ <= _)%nat => unfold PARSE_LF, READCFG_LF, READCFG_MAXLIVE, AL_FRAMES, AFS_MAXLIVE in *; clear - LFB; lia
               | |- as_chain _ _ _ _ => apply CHA
               | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
               | |- pf_ok _ PF_storenew _ _ => apply (pf_ok_closed H); exact HR1
               | |- parse_closed_ok _ _ _ _ => apply HPC
               | |- pf_ok _ PF_biofree _ _ => apply (pf_ok_closed H); exact HBF2
               | |- 1 <= _ -> addressable _ _ _ => intros _; exact ADC4
               | |- _ <= as_AL _ _ => unfold MIDCOST in BUDGET; clear - BUDGET AL2 AL3 PCB0 PCB1 CMN CMN0 CFN0 CF15 CM15 CM16 CF16 CF896 PCNN; pose proof (PCNN M0); lia
               | |- _ mod 2 = 0 => reflexivity
               | |- aauxv_ok _ _ => exact AUXA4
               | |- _ => first [exact DS4| exact LM4| exact KREL5| exact AUX4| exact BHI| exact ST4| exact CEIL| exact ERR4| exact MI4| reflexivity| exact SP16'| exact STK4| exact AC4| exact RFS4| exact RL4| lia
                           | match goal with |- ?G => idtac "LEFTP2:" G end]
               end. }
        clear P2. intros [msF6 mo6] PO. unfold parse_one_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (x0 & x1 & x2 & e0 & e1' & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & errv5 & s5' & M2 & LBN2 & XS5 &
                        VIS6 & KREL6 & MP6 & MI5 & AC5 & RL5 & ST5 & STK5 & ERR5 & AUX5 & HP5 & LM5 & STEP2 & NEW2 & CTX2 & EC2 & EB2 & DS5 & AD5 & FXS5 & RFS5 & XP5 & AL5).
        cbn [mid_errblocks mid_E mid_ctx mid_err] in HP5, XP5. change (blocks_ERRST Em1) with E1 in HP5.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in STK5 by lia.
        pose proof (LIBMID_xpres0 H) as _tmp. clear _tmp.
        assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
        { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP5); [exact FR4| left; cbn; lia|].
          assert (XB : Forall (fun iv : Z * Z => snd iv <= aceil) (memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X ++ errph_foot eph1 ++ XS5)).
          { apply Forall_below_app; [apply Forall_below_aimg; apply aimg_memflag|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_CTX_X|].
            apply Forall_below_app; [apply Forall_below_aimg; apply aimg_ERR_XE|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_VDSO_X|].
            apply Forall_below_app; [eapply errph_foot_below; [exact EPm4| intros b Hb; exact (proj1 (proj2 (HB4 _ (or_intror (SUBA2 _ Hb)))))]|].
            pose proof (fs_scratch_range_Forall H HH _ _ _ RFS4 FXS5) as K. eapply Forall_impl; [| exact K]. intros [u w] Ku. cbn in Ku |- *. lia. }
          eapply Forall_avoid_hi; [exact XB| lia]. }
        assert (XC5 : xpres H LBc (bv_unsigned sp) (XT ++ (XS2 ++ XS5)) m m5).
        { eapply xpres_trans; [eapply xpres_weaken; [exact XC4| lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq]]|].
          eapply xpres_weaken; [| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq]].
          eapply (XTOP (LBN1 ++ LIB) ((p, A, N) :: E1 ++ LBN1 ++ LB0) ((p, A, N) :: LBN1 ++ LB0));
            [exact EPm4| exact HP4| intros b Hb; right; exact (SUBA2 _ Hb)| intros b Hb; right; exact (SUBC2 _ Hb)| exact DJX2| exact XP5| intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb| lia]. }
        (* [comment removed for export] *)
        assert (BLK5 : rw_cells asegs m5 A [CB (length bs') bs']).
        { refine (BX_cells _ _ _ m4 m5 A _ (p, A, N) XP5 BLK4 (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; unfold zlength in LEN4; lia) _).
          cbn [blk_addr blk_size fst snd].
          apply BM_app; [apply BM_img; [apply aimg_memflag| exact ATOP| lia| exact AAP]|]. apply BM_app; [apply BM_img; [apply aimg_CTX_X| exact ATOP| lia| exact AAP]|].
          apply BM_app; [apply BM_img; [apply aimg_ERR_XE| exact ATOP| lia| exact AAP]|]. apply BM_app; [apply BM_img; [apply aimg_VDSO_X| exact ATOP| lia| exact AAP]|].
          apply BM_app; [| exact (BM_xs s3' _ m4 m4 XS5 (p, A, N) HP4 (or_introl eq_refl) RFS4 FXS5)].
          destruct (errph_foot_shape _ _ _ _ EPm4) as [E|(c & E & I5 & Z5)]; rewrite E; [apply BM_nil|].
          refine (BM_blk s3' _ m4 (ec_es c) (p, A, N) _ _ HP4 (or_intror (SUBA2 _ I5)) (or_introl eq_refl) _ (Z.le_refl _) ltac:(rewrite Z5; apply Z.le_refl)).
          apply not_eq_sym. apply (nodup_ids_cons_ne (p, A, N) _ (ec_es c) ND4). exact (SUBA2 _ I5). }
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply af_seg4; exact MI5|]. intros msF7 mo7 KREL7 MP7 VIS7.
        apply (ah_done H HH). unfold fz_mid. cbn [cfg_ms cfg_model].
        exists x0, x1, x2, e3, e4, e5, e6, e7, x3, x4, x5, x6, m5, errv5, s5', M2, (LBN2 ++ LBN1), A, (Some (p, N)), (XS2 ++ XS5).
        split; [exact VIS7|]. split; [exact KREL7|].
        split; [eapply (ah_mpres_trans H HH); [exact MP1| eapply (ah_mpres_trans H HH); [exact MP2| eapply (ah_mpres_trans H HH); [exact MP3| eapply (ah_mpres_trans H HH); [exact MP4| eapply (ah_mpres_trans H HH); [exact MP5| eapply (ah_mpres_trans H HH); [exact MP6| exact MP7]]]]]]|].
        split; [exact MI5|]. split; [exact AC5|]. split; [exact ST5|]. split; [exact STK5|]. split; [exact ERR5|]. split; [exact AUX5|].
        split. { split; [cbn [blocks_of]; apply in_or_app; right; left; reflexivity|]. split; [| exact (AD5 ltac:(lia))].
                 exists bs'. replace (Z.to_nat N) with (length bs') by (unfold zlength in LEN4; lia). exact BLK5. }
        split. { eapply PERM; [exact HP5|]. cbn [blocks_of]. apply Permutation_app_head. rewrite <- !app_assoc. change ((p, A, N) :: LBN1 ++ LB0) with ([(p, A, N)] ++ LBN1 ++ LB0).
                 apply (Permutation_app_swap_app LBN2 [(p, A, N)]). }
        split; [rewrite <- app_assoc; exact LM5|].
        split; [eapply mid_step_trans; [exact STEP1| exact STEP2]|].
        split; [eapply mid_newlib_ok_trans; [exact STEP1| exact NEW1| exact STEP2| exact NEW2]|].
        split; [exact CTX2|]. split; [exact EC2|]. split; [exact EB2|].
        split; [cbn; lia|].
        split; [exact FR5|]. split; [exact RFS5|]. split; [apply Forall_app; split; [exact FXS2| exact FXS5]|].
        split; [exact XC5|].
        unfold MIDCOST. clear - AL2 AL3 AL5 PCB0 PCB1 CMN CMN0 CFN0 CM15 PCNN. pose proof (PCNN M0). lia.
      - (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply af_seg2b; [lia| exact GATE| exact MI2]|]. intros msF3 mo3 KREL3 MP3 VIS3.
        apply (ah_done H HH). unfold fz_mid. cbn [cfg_ms cfg_model].
        exists u0, u1, u2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, s2', (mkMID 1 (CtxReady bx1) eph1 Em1 vd1), LBN1, 0, None, XS2.
        split; [exact VIS3|]. split; [exact KREL3|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| eapply (ah_mpres_trans H HH); [exact MP2| exact MP3]]|].
        split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|]. split; [exact STK2|]. split; [exact ERR2|]. split; [exact AUX2|].
        split; [reflexivity|].
        split; [cbn [blocks_of app]; exact HP2|].
        split; [exact LM2|]. split; [exact STEP1|]. split; [exact NEW1|]. split; [exists bx1; reflexivity|]. split; [exact EC1|]. split; [exact EB1|].
        split; [cbn; lia|]. split; [exact FR2|]. split; [exact RFS2|]. split; [exact FXS2|]. split; [exact XC2|].
        unfold MIDCOST. pose proof (PCNN M0). pose proof (CM0 (2^23 + 2^20) ltac:(lia)). pose proof (CF0 (2^23 + 2^22) ltac:(lia)). clear - AL2 PCB0 CM15 CM16 CF16 H0 H1 H2. lia. }
    (* [comment removed for export] *)
    clear XC2 FR2 DS2 XP2 HP2 LM2 EPm2 SUBA2 SUBC2 SUBE2 DJ2E DJ2N DJX2 IM2 MF2 GM2 HB2 ND2 ST2 ERR2 AUX2 MI2 KREL2 STK2 AD2 RFS2 AC2 RL2.
    eapply (ah_seq H HH); [exact MID|]. clear MID. intros [msF8 mo8] PO. unfold fz_mid in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & s6' & M2 & LBN & P & o & XS6 &
                    VIS8 & KREL8 & MP8 & MI6 & AC6 & ST6 & STK6 & ERR6 & AUX6 & OIN & HP6 & LM6 & STEP6 & NEW6 & (bx & CTX6) & EC6 & EB6 & PB & FR6 & RFS6 & FXS6 & XC6 & AL6).
    set (E2 := mid_errblocks M2) in *. set (BO := blocks_of P o) in *. set (L6 := E2 ++ BO ++ LBN ++ LB0) in *.
    pose proof LM6 as (IM6 & MF6 & CP6 & EPm6 & EX6 & _ & _ & FIT6 & GM6 & _ & _ & _ & _ & _ & RL6 & ESH6 & EBL6). rewrite (proj1 STEP6) in MF6. rewrite CTX6 in CP6, EPm6.
    pose proof (newlib_bounds _ _ _ STEP6 NEW6) as (ML1 & ML2 & ML5 & ML6).
    pose proof (ctxph_nonneg H HH (mid_ctx M2)) as (NB2a & NB2b & _). pose proof (errph_nonneg (mid_err M2)) as (NB2c & NB2d).
    assert (HB6 : forall b, In b L6 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP6 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (ND6 := ah_nodup H HH _ _ _ HP6).
    pose proof (nd_app E2 (BO ++ LBN ++ LB0) ND6) as [DJ6E ND6a]. pose proof (nd_app BO (LBN ++ LB0) ND6a) as [DJ6B ND6b]. pose proof (nd_app LBN LB0 ND6b) as [DJ6N _].
    assert (SUBA6 : forall b, In b (LBN ++ LIB) -> In b (LBN ++ LB0)).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (DJX6 : idsdisj (LBN ++ LIB) LBc).
    { intros b b' Hb Hb'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply DJ6N; [exact Hb| apply SUBC; exact Hb']| apply DJLC; assumption]. }
    assert (OSZ : 0 <= oszb' o <= 1500).
    { destruct o as [[id n]|]; cbn [oszb']; [| lia]. destruct OIN as [OIN1 _]. pose proof (proj1 (proj2 (proj2 (ah_blocks H HH _ _ _ _ HP6 OIN1)))) as K. cbn [blk_size snd] in K.
      unfold BO, blocks_of in PB. rewrite lb_bytes_cons in PB. cbn [blk_size snd lb_bytes fold_right] in PB. lia. }
    (* [comment removed for export] *)
    pose proof (acfree_opt_spec H HH) as CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L6) (s := s6') (P := P) (o := o) (errv := errv6) (CH := []);
        [exact VIS8| reflexivity| ..]; rewrite ?unsigned_lit by (unfold FZ_R4, R_fuzz_CRYPTO_free; lia).
      all: lazymatch goal with
           | |- match _ with _ => _ end => unfold L6, E2, BO; exact OIN
           | |- _ <= _ - CFREE_STACK => rewrite CFSK; clear - LO; lia
           | |- as_chain _ _ _ _ => apply CHA
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ _ _ _ => apply (pf_ok_closed H); exact HCF
           | |- _ <= as_AL _ _ => pose proof (CFM (oszb' o) 1500 OSZ) as K; unfold MIDCOST in BUDGET, AL6; clear - BUDGET AL6 K CM16 CF16 CF896; lia
           | |- _ => first [exact HP6| exact KREL8| exact AUX6| exact ST6| exact CEIL| exact ERR6| exact MI6| reflexivity| exact SP16'| exact AC6| exact IM6| exact GM6| lia
                       | match goal with |- ?G => idtac "LEFTCF:" G end]
           end. }
    clear CF. intros [msF9 mo9] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m7 & s7' & LB7 &
                    VIS9 & KREL9 & MP9 & MI7 & AC7 & ST7 & ERR7 & AUX7 & PERM7 & SUB7 & XP7 & HP7 & IM7 & GM7 & AL7).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST7, XP7 by lia.
    assert (P7 : Permutation LB7 (E2 ++ LBN ++ LB0)).
    { apply (Permutation_app_inv_l BO). transitivity L6; [exact PERM7|]. unfold L6. apply Permutation_app_swap_app. }
    assert (KEEP7 : forall b, In b (E2 ++ LBN ++ LB0) -> In b LB7).
    { intros b Hb. eapply perm_in_rest_s; [exact PERM7| unfold L6; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb]|].
      intros K. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - exact (DJ6E _ _ Hb ltac:(apply in_or_app; left; exact K) eq_refl).
      - exact (DJ6B _ _ K Hb eq_refl). }
    assert (HB7 : forall b, In b LB7 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP7 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    pose proof (LIBMID_xpres0 H (LBN ++ LIB) LB7 (bv_unsigned sp + -32) m6 m7 M2 bx LM6 CTX6 XP7 ltac:(intros b Hb; apply KEEP7; apply in_or_app; right; exact (SUBA6 _ Hb)) ltac:(intros b Hb; apply KEEP7; apply in_or_app; left; exact Hb)) as LM7.
    pose proof LM7 as (_ & MF7 & CP7 & EPm7 & EX7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & RL7 & ESH7 & EBL7). rewrite (proj1 STEP6) in MF7. rewrite CTX6 in CP7, EPm7.
    assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP7); [exact FR6| left; cbn; lia| apply Forall_nil]. }
    assert (RFS7 : as_RFS H LF m7) by (eapply (RFS_via_xpres H HH); [exact RFS6| exact XP7| apply Forall_nil]).
    assert (STK7 : stack0 m7 lo shi) by (eapply (stack0_xpres H); [exact XP7| exact STK6| apply Forall_nil]).
    assert (XC7 : xpres H LBc (bv_unsigned sp) (XT ++ XS6) m m7).
    { eapply xpres_trans; [exact XC6|]. eapply xpres_weaken; [exact XP7| lia| intros b Hb; apply KEEP7; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb| intros q Hq; destruct Hq]. }
    assert (HP7' : as_RHEAP H s7' (blocks_ERRST (mid_E M2) ++ LBN ++ LB0) m7) by (eapply PERM; [exact HP7| exact P7]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply af_seg5; exact MI7|]. intros msF10 mo10 KREL10 MP10 VIS10.
    (* [comment removed for export] *)
    assert (ESTR : as_Cf H (estr_bytes (mid_E M2)) <= as_Cf H 896).
    { apply CFM. destruct (mid_err M2) as [|c0] eqn:EM; cbn [ERRX] in EX6.
      - rewrite EX6. change (estr_bytes errst_zero) with 0. lia.
      - destruct EX6 as ((L16 & _) & OK6 & _). pose proof (estr_bytes_bound _ OK6) as K. rewrite L16 in K. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in K. lia. }
    assert (EXB : 0 <= errph_cost H (mid_err M2) <= as_Cm H (2^16) + as_Cf H (2^16)).
    { destruct (mid_err M2); cbn [errph_cost]; unfold ERRINIT_COST, ERRINIT_BYTES; lia. }
    assert (ELF : (ERRPH_LF (mid_err M2) <= 4)%nat) by (destruct (mid_err M2); cbn; lia).
    pose proof ECL as EC. unfold errclear_stmt in EC.
    eapply (ah_seq H HH).
    { eapply EC with (lo := lo) (B := B) (LB := LBN ++ LB0) (s := s7') (ph := mid_err M2) (E := mid_E M2) (x := bx) (errv := errv6) (LF := LF) (CH := []);
        [exact VIS10| ..]; rewrite ?unsigned_lit by (unfold FZ_R5, R_fuzz_ERR_clear_error; lia).
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => change (blocks_ERRST (mid_E M2)) with E2; rewrite (lb_bytes_app_s E2), (lb_bytes_app_s LBN LB0); unfold mid_bytes in ML1, MB0; unfold ERRSTR_BYTES in EB6;
                                      clear - BUD LBY0 MB0 ML1 EB6 NB2a NB0a NB0c; destruct (is_fresh st); lia
           | |- Z.of_nat (length _) + _ <= _ => change (blocks_ERRST (mid_E M2)) with E2; rewrite (length_app E2), (length_app LBN LB0), !Nat2Z.inj_add; unfold mid_cnt in ML2, MC0; unfold ERRSTR_CNT in EC6;
                                                clear - BUDC LBC0 MC0 ML2 EC6 NB2b NB0b NB0d; destruct (is_fresh st); lia
           | |- _ <= _ - ERRCLEAR_STACK _ => pose proof (errclear_stack_max (mid_err M2)) as K; clear - LO K; lia
           | |- errph_sh0 _ _ _ _ => destruct (mid_err M2); [cbn; rewrite ?unsigned_lit by lia; eapply stack0_sub; [exact STK7| clear; lia| clear - SSH SPR LO; lia| clear - SP16' SPR; Z.div_mod_to_equations; lia]| exact I]
           | |- ERRPH _ _ _ => eapply ERRPH_mono; [| exact SUBA6]; cbn [ERRPH_mid] in EPm7; exact EPm7
           | |- ERRX _ _ _ => exact EX7
           | |- errph_below _ _ => exact EBL7
           | |- errph_shad _ _ => exact ESH7
           | |- CTXPH _ _ _ => eapply (CTXPH_mono (LBN ++ LIB) (LBN ++ LB0) SUBA6); exact CP7
           | |- (length _ + _ <= _)%nat => unfold AL_FRAMES, AFS_MAXLIVE in *; clear - LFB ELF; lia
           | |- as_chain _ _ _ _ => apply CHA
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ _ _ _ => apply (pf_ok_closed H); apply HECL
           | |- errph_closed_ok _ _ => destruct (mid_err M2); [exact HEC| exact I]
           | |- _ <= as_AL _ _ => unfold ERRCLEAR_COST; unfold MIDCOST in BUDGET, AL6; pose proof (CFM (oszb' o) 1500 OSZ); clear - BUDGET AL6 AL7 ESTR EXB OSZ CF15 CM16 CF16 CF896 H0; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact HP7'| exact KREL10| exact AUX7| exact SP16'| exact ST7| exact CEIL| exact ERR7| exact MI7| reflexivity| exact AC7| exact MF7| exact IM7| exact GM7| exact RL7| exact RFS7| lia
                       | match goal with |- ?G => idtac "LEFTEC:" G end]
           end. }
    clear EC. intros [msF11 mo11] PO. unfold errclear_post, c4_frame in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LBN3 & c & XS8 &
                    VIS11 & MP11 & (KREL11 & MI8 & AC8 & ST8 & AUX8 & HP8 & MF8 & IM8 & GM8 & RL8) & ERR8 & ED8 & EP8 & CP8 & ES8 & LSH8 & FXS8 & XP8 & RFS8 & AL8).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST8, XP8 by lia.
    set (M3 := mkMID 1 (CtxReady bx) (ErrReady c) errst_cleared (mid_vdso M2)).
    assert (XP8' : xpres H (LBN ++ LB0) (bv_unsigned sp + -32) (XS8 ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M2)) m7 m8).
    { eapply xpres_weaken; [exact XP8| lia| intros b Hb; exact Hb|]. intros q Hq.
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq]. }
    assert (LM8 : LIBMID (LBN3 ++ LBN ++ LIB) m8 M3).
    { eapply (LIBMID_errcall H HH); [exact HP7'| exact SUBA6| exact LM7| exact CTX6| exact RFS7| exact FXS8| exact XP8'| rewrite (blocks_ERRST_canonical errst_cleared (or_intror eq_refl)); exact HP8| exact CP8| exact EP8| exact ED8| exact ES8| exact errst_fits_cleared| exact LSH8| exact MF8]. }
    assert (HB8 : forall b, In b (LBN3 ++ LBN ++ LB0) -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP8 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (XB8 : Forall (fun iv : Z * Z => snd iv <= aceil) (ERR_XE ++ errph_foot (mid_err M2))).
    { apply Forall_below_app; [apply Forall_below_aimg; apply aimg_ERR_XE|].
      eapply errph_foot_below; [exact EPm7| intros b Hb; exact (proj1 (proj2 (HB7 _ (KEEP7 _ (in_or_app _ _ _ (or_intror (SUBA6 _ Hb)))))))]. }
    assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact FR7| left; cbn; lia|]. apply Forall_app. split.
      - pose proof (fs_scratch_range_Forall H HH _ _ _ RFS7 FXS8) as K. eapply Forall_impl; [| exact K]. intros [u w] Ku. cbn in Ku |- *. lia.
      - eapply Forall_avoid_hi; [exact XB8| lia]. }
    assert (STK8 : stack0 m8 lo shi).
    { eapply (stack0_xpres H); [exact XP8| exact STK7|]. apply Forall_app; split; [eapply Forall_impl; [| exact FXS8]; intros iv Pv; exact (fs_scratch_stack0_ok _ _ _ RFS7 Pv)|].
      apply Forall_app; split; [apply stack0_ok_of_aimg; apply aimg_ERR_XE|].
      destruct (mid_err M2) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. cbn [ERRPH_mid ERRPH] in EPm7. destruct EPm7 as [_ ECH7].
      pose proof ECH7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). destruct (HB7 _ (KEEP7 _ (in_or_app _ _ _ (or_intror (SUBA6 _ I5))))) as (_ & _ & _ & _ & _ & Q5).
      apply Forall_cons; [eapply stack0_ok_aapp; [exact Q5| apply Z.le_refl| rewrite Z5; apply Z.le_refl]| apply Forall_nil]. }
    assert (XC8 : xpres H LBc (bv_unsigned sp) (XT ++ (XS6 ++ XS8)) m m8).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XC7| lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq]]|].
      eapply xpres_weaken; [| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq]].
      eapply (XTOP (LBN ++ LIB) LB7 (LBN ++ LB0) m7 (CtxReady bx) (mid_err M2) s7' m7 (bv_unsigned sp + -32) m7 m8 XS8);
        [cbn [ERRPH_mid] in EPm7 |- *; exact EPm7| exact HP7| intros b Hb; apply KEEP7; apply in_or_app; right; exact (SUBA6 _ Hb)
        | intros b Hb; apply KEEP7; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb| exact DJX6| | intros b Hb; apply in_or_app; right; apply SUBC; exact Hb| lia].
      eapply xpres_weaken; [exact XP8| lia| intros b Hb; exact Hb|]. intros q Hq.
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [do 5 (apply rin_ivs_app; right); exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [do 2 (apply rin_ivs_app; right); apply rin_ivs_app; left; exact Hq|].
      do 4 (apply rin_ivs_app; right). apply rin_ivs_app; left. exact Hq. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL11| exact VIS11| eapply af_seg6 with (lo := lo); [exact FR8| exact ST8| exact CEIL| lia| exact MI8| exact RAE]|].
    intros msF12 mo12 KREL12 MP12 [VIS12 ST8r].
    (* [comment removed for export] *)
    assert (STEP3 : mid_step M2 M3).
    { unfold mid_step, M3. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; rewrite CTX6 in Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 Hc. rewrite Hc in ED8. cbn [errph_delta] in ED8. destruct ED8 as [-> _]. reflexivity. }
    assert (NEW3 : mid_newlib_ok M2 M3 LBN3).
    { unfold mid_newlib_ok, M3. cbn [mid_ctx mid_err]. rewrite CTX6. exists [], LBN3. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct (mid_err M2) as [|c0]; [exact ED8|]. cbn [errph_delta] in ED8. destruct ED8 as [_ E3]. exact E3. }
    pose proof (mid_step_trans _ _ _ STEP6 STEP3) as STEPT. pose proof (mid_newlib_ok_trans _ _ _ _ _ STEP6 NEW6 STEP3 NEW3) as NEWT.
    pose proof (newlib_bounds _ _ _ STEPT NEWT) as (_ & _ & TB5 & TB6).
    assert (FITS : lib_fits ((LBN3 ++ LBN) ++ LIB) /\ (is_fresh st = false -> (LBN3 ++ LBN) ++ LIB = LIB)).
    { destruct (is_fresh st) eqn:FS.
      - destruct (FRESH eq_refl) as (-> & _ & _). rewrite app_nil_r. split; [| intros; discriminate].
        unfold lib_fits. unfold CTXINIT_CNT, ERRINIT_CNT, CTXINIT_BYTES, ERRINIT_BYTES in TB5, TB6. lia.
      - destruct (INITED eq_refl) as ((x0 & CX0) & (c0 & CE0') & SZ). rewrite (newlib_nil _ _ _ _ _ CX0 CE0' NEWT). cbn [app]. split; [exact SZ| reflexivity]. }
    destruct FITS as [FITS LIBEQ].
    apply (ah_done H HH). unfold fuzz_post. cbn [cfg_ms cfg_model al_LIBST al_is_fresh al_LIBX al_cost ECHL].
    exists z0, z1, z2, h1, h2, h3, h4, h5, h6, h7, z3, z4, z5, z6, m8, errv8, s8', ((LBN3 ++ LBN) ++ LIB), LBc, (Inited (mkLI bx c (mid_vdso M2))), (XS6 ++ XS8).
    split; [exact VIS12|]. split; [exact KREL12|].
    split; [eapply (ah_mpres_trans H HH); [exact MP8| eapply (ah_mpres_trans H HH); [exact MP9| eapply (ah_mpres_trans H HH); [exact MP10| eapply (ah_mpres_trans H HH); [exact MP11| exact MP12]]]]|].
    split; [exact MI8|]. split; [exact RL8|]. split; [exact ST8r|]. split; [exact ERR8|]. split; [exact AUX8|].
    split; [unfold LB0 in HP8; rewrite <- !app_assoc; exact HP8|].
    split; [apply Permutation_refl|].
    split; [eapply LIBST_of_mid; [rewrite <- app_assoc; exact LM8| right; reflexivity| exact FITS]|].
    split; [reflexivity|].
    unfold lib_fits in FITS. unfold ALIB_CNT_MAX, ALIB_BYTES_MAX. split; [clear - FITS; lia|]. split; [clear - FITS; lia|].
    split; [exact LIBEQ|].
    split; [apply Forall_app; split; [exact FXS6| exact FXS8]|].
    split. { eapply xpres_weaken; [exact XC8| lia| intros b Hb; exact Hb|]. intros q Hq. unfold XT in Hq. unfold LIBXT, LIBXP.
             apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [| apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq].
             apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq| apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq]. }
    split; [exact RFS8|]. split; [exact AC8|]. split; [exact STK8|].
    unfold fuzz_cost. cbn [al_cost ECHL]. unfold acost, ACOST_BYTES. unfold MIDCOST in BUDGETC, AL6. unfold ERRCLEAR_COST in AL8. pose proof (CFM (oszb' o) 1500 OSZ) as K.
    clear - BUDGETC AL6 AL7 AL8 ESTR EXB OSZ CF15 CM16 CF16 CF896 K. lia.
  Qed.
End W.

Print Assumptions fuzz_spec.
