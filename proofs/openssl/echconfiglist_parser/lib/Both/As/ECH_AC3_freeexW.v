(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsCall AsWalk AsStack0 ECH_AImg ECH_Xpres ECH_ARep
  ECH_ALib ECH_Iface ECH_AKit ECH_AsKit ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AC1_free ECH_AStmt_C2 ECH_AC2_small ECH_AStmt_C5 ECH_AC5_small
  ECH_AStmt_C3 ECH_AC3_ready ECH_AC4_frame ECH_AC3_freeex.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- ?g => idtac "GOAL:" g end.
Ltac show_regs := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma rw_cells_nil : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [].
  Proof.
    intros m A HA. split; [split; [exact I|]|].
    - unfold bytes_at. cbn [length cells_bytes]. repeat split; try lia.
    - unfold wr_at. cbn [cells_size]. repeat split; try lia.
  Qed.


  (* [comment removed for export] *)
  Lemma MEMFLAG_xpres0 : forall LB SP m m1 v, xpres H LB SP [] m m1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros LB SP m m1 v XP (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply (xpres_rw_cells' H); [exact XP| exact MF| | apply Forall_nil]. right; left. unfold A_mem_inited, aimg_client. cbn. lia.
  Qed.
  Lemma arelro_xpres0 : forall LB SP m m', arelro_lib m -> xpres H LB SP [] m m' -> arelro_lib m'.
  Proof.
    intros LB SP m m' RL XP i Hi. destruct (XP i) as [E _]; [lia| | rewrite E; apply RL; exact Hi].
    split; [right; left; unfold aimg_client; lia| intros K; exact K].
  Qed.


  (* [comment removed for export] *)
  Lemma rw_cells_zero16_C8 : forall m A, rw_cells asegs m A [CB 16 (poison_bytes 16 0)] -> rw_cells asegs m A [C8 (wz 0); C8 (wz 0)].
  Proof.
    intros m A [[Hwf Hb] Hw].
    assert (E : le8 (wz 0) = poison_bytes 8 0) by reflexivity.
    split; [split|].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app] in *. rewrite E. cbn [poison_bytes repeat app] in *. exact Hb.
    - cbn [cells_size csize] in *. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Definition afx_entry_post (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 : word) (F : bvmap 5 word) (fc : bv 32)
      (obj ad lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (sp1 : Z) (jl : list byte) (gapc : list cell) (m1 : mem),
      ms' = MS (mkR ra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 obj) (Z_to_bv 64 ad) a3
                    a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFX_BODY) fc None m1 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 sp1 [CB 88 jl] /\ rw_cells asegs m1 (sp1 + 88) gapc /\ sp1 + 88 + Z.of_nat (cells_size gapc) = bv_unsigned sp - 104
      /\ bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 /\ sp1 mod 32 = 0 /\ stk asegs m1 lo sp1.

  Lemma afx_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (obj ad lo : Z),
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CFREEEX_STACK -> bv_unsigned sp mod 16 = 0 -> mem_inv asegs m ->
    evt asegs (afx_entry_post ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 F fc obj ad lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 obj) (Z_to_bv 64 ad) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO SPA MI.
    unfold P_CRYPTO_free_ex_data, AFX_BODY, CFREEEX_STACK, FR_CRYPTO_free_ex_data, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
      CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
      GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, CRYPTO_EX_INDEX_BIO in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 192%nat ST. do 16 st1.
    zstep. rewrite land_align32 by lia.
    assert (CASES : (bv_unsigned sp + -192) mod 32 = 0 \/ (bv_unsigned sp + -192) mod 32 = 16) by (clear - SPA SPR; Z.div_mod_to_equations; lia).
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [LOC0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -192 + Z.of_nat 88) with (bv_unsigned sp + -104) in FR by lia.
    apply rw_cells_flatten in LOC0. cbn [cells_size csize cells_bytes cbytes Nat.add app length] in LOC0.
    destruct CASES as [CSA|CSB].
    - rewrite CSA, Z.sub_0_r. step.
      apply evt_done. unfold afx_entry_post.
      eexists (bv_unsigned sp + -192), _, [], _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|]. split; [exact LOC0|].
      split; [apply rw_cells_nil; lia|]. split; [cbn [cells_size]; lia|]. split; [lia|]. split; [clear - CSA SPR; Z.div_mod_to_equations; lia| exact ST].
    - rewrite CSB. replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia. step.
      carve_frame 16%nat ST.
      lazymatch type of LOC0 with rw_cells _ _ _ [CB 88 ?j] =>
        apply (rw_cells_split_CB asegs _ _ [] 88 j [] [72;16]%nat) in LOC0; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in LOC0 end.
      lazymatch type of LOC0 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in LOC0 end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in LOC0. destruct LOC0 as [L72 GAP]. cbn [cells_size csize Nat.add] in GAP.
      replace (bv_unsigned sp + -192 + Z.of_nat 72) with (bv_unsigned sp + -208 + 88) in GAP by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (LOC : rw_cells asegs mx (bv_unsigned sp + -208) ([CB 16 _] ++ [CB 72 _]))
        by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact FR0|]; cbn [cells_size csize Nat.add];
            replace (bv_unsigned sp + -208 + Z.of_nat 16) with (bv_unsigned sp + -192) by lia; exact L72) end.
      apply rw_cells_flatten in LOC. cbn [cells_size csize cells_bytes cbytes Nat.add app length] in LOC. clear FR0 L72.
      apply evt_done. unfold afx_entry_post.
      eexists (bv_unsigned sp + -208), _, [CB 16 _], _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|]. split; [exact LOC|].
      split; [exact GAP|]. split; [cbn [cells_size csize Nat.add]; lia|]. split; [lia|]. split; [clear - CSB SPR; Z.div_mod_to_equations; lia| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition afx_c1_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
      (s6v s7v s9v : word) (ad lo sp1 ff : Z) (mc : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AFX_RA_MS) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1)
                    (Z_to_bv 64 ad) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                    (Z_to_bv 64 ad) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 A_defctx_exmeth_bio) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) s6v s7v
                    (Z_to_bv 64 ASHADOW_BASE) s9v (Z_to_bv 64 (sh ff)) (Z_to_bv 64 18446744073709551615) t3 t4 t5 t6)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m' (seg_rom asegs)
      /\ munch [(lo, sp1)] mc m' /\ wmono asegs mc m' /\ mem_inv asegs m' /\ stk asegs m' lo sp1 /\ ACONST m'.

  Lemma afx_segC1 : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s7v s9v rax : word) (F : bvmap 5 word) (fc : bv 32)
      (mc : mem) (obj ad lo sp1 ff : Z) (j2 : list byte),
    rw_cells asegs mc sp1 [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 A_defctx_global);
                           C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ad); CB 16 j2; C8 (Z_to_bv 64 ff)] ->
    rw_cells asegs mc ad [C8 (wz 0); C8 (wz 0)] -> ad mod 8 = 0 -> accessible mc ad 16 -> ad + 16 <= lo -> AIMG_TOP <= ad -> ad + 16 < AAPP_HI ->
    bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 ->
    stk asegs mc lo sp1 -> aceil <= lo -> lo <= bv_unsigned sp - CFREEEX_STACK -> mem_inv asegs mc -> ACONST mc ->
    evt asegs (afx_c1_post sp gp tp F fc s6v s7v s9v ad lo sp1 ff mc)
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 ad) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 A_defctx_exmeth_bio) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) s6v s7v
                (Z_to_bv 64 ASHADOW_BASE) s9v (Z_to_bv 64 (sh ff)) (Z_to_bv 64 18446744073709551615) t3 t4 t5 t6)
          F (Z_to_bv 64 AFX_RA_CF) fc None mc (seg_rom asegs)).
  Proof.
    intros until j2. intros LOC AD AD8 ACC ADLO ADT ADH SP1 ST CEIL LO MI AC.
    unfold AFX_RA_CF, AFX_RA_MS, CFREEEX_STACK, FR_CRYPTO_free_ex_data, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
      CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
      GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, AIMG_TOP, AAPP_HI in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold wz in AD.
    pose proof (munch_refl [(lo, sp1)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, sp1)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    do 3 st1. ck8_check ACC (ad + 8). st1. step.
    eapply evt_cut.
    { pose proof ask_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold FR_sk_free; lia). }
    intros ms_ PO. unfold sknull_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & mn & -> & MUn & WMn & MIn & ACn & STn).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUn, STn by lia.
    carry MUn WMn. extend_munch MU WM MUn WMn. clear MI ST. rename MIn into MI. rename STn into ST.
    (* [comment removed for export] *)
    do 3 st1. step.
    unfold afx_c1_post. finish. all: try exact MU.
  Qed.

  (* [comment removed for export] *)
  Definition afx_final (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
      (s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s1e s0e rae : word) (lo ff fp : Z) (LF : list fframe) (mc : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 fp) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc rae) fc None m' (seg_rom asegs)
      /\ munch [(fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]%Z mc m' /\ wmono asegs mc m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ as_RFS H LF m' /\ ACONST m'.

  Lemma afx_segC2 : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s4v s5v s6v s7v s8v s9v s11v rax : word) (F : bvmap 5 word) (fc : bv 32)
      (mc : mem) (LF : list fframe) (s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s1e s0e rae : word)
      (lo sp1 ff fp obj ad : Z) (j2 : list byte) (hj sj : list byte) (gapc : list cell),
    as_RFS H ((2, ff, fp) :: LF) mc -> fresh_frame H LF 2 ff fp -> ACONST mc ->
    rw_cells asegs mc (bv_unsigned sp + -104) [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
    rw_cells asegs mc sp1 [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 A_defctx_global);
                           C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ad); CB 16 j2; C8 (Z_to_bv 64 ff)] ->
    rw_cells asegs mc (sp1 + 88) gapc -> sp1 + 88 + Z.of_nat (cells_size gapc) = bv_unsigned sp - 104 ->
    rw_cells asegs mc ff [CB 248 hj; C8 (Z_to_bv 64 fp)] -> rw_cells asegs mc (sh ff) [CB 32 sj] -> rw_cells asegs mc fp [C1 (b8 1)] ->
    bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 ->
    stk asegs mc lo sp1 -> aceil <= lo -> lo <= bv_unsigned sp - CFREEEX_STACK -> mem_inv asegs mc -> bv_unsigned rae mod 2 = 0 ->
    evt asegs (afx_final sp gp tp F fc s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s1e s0e rae lo ff fp LF mc)
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                s2v (Z_to_bv 64 (ff + 32)) s4v s5v s6v s7v s8v s9v (Z_to_bv 64 (sh ff)) s11v t3 t4 t5 t6)
          F (Z_to_bv 64 AFX_RA_MS) fc None mc (seg_rom asegs)).
  Proof.
    intros until gapc. intros RFS FRESH AC FR LOC GAP GSZ FF SH FP SP1 ST CEIL LO MI RAE.
    unfold AFX_RA_MS, CFREEEX_STACK, FR_CRYPTO_free_ex_data, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
      CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
      GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range rae) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ GAP) as GAPB. pose proof (rw_cells_bound _ _ _ _ LOC) as LOCB.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & F1 & F2 & F4).
    change (fsz 2) with 256 in R2, P6. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6, F1, F2.
    pose proof (aapp_not_shadowland _ _ F4) as F5. unfold AFS_SIZE, ALOWSH_LO, AHI_LO in F5.
    set (shf := sh ff) in *.
    assert (SHFB : sh AIMG_TOP + 4608 <= shf /\ shf + 32 <= AHI_LO)
      by (subst shf; unfold sh, AHI_LO, AIMG_TOP; rewrite ASHADOW_BASE_val; clear - R1 R2 ACEILB; Z.div_mod_to_equations; lia).
    let v := eval vm_compute in (sh AIMG_TOP + 4608) in change (sh AIMG_TOP + 4608) with v in SHFB. unfold AHI_LO in SHFB.
    assert (FFshf : ff + 256 <= shf \/ shf + 32 <= ff) by (clear - F5 P5 P6 SHFB; lia).
    assert (FPshf : fp + 1 <= shf \/ shf + 32 <= fp) by (clear - F5 P3 P4 SHFB; lia).
    assert (DJ3 : chunk_disj shf 32 ff 256) by (unfold chunk_disj; clear - FFshf; lia).
    assert (DJ6 : chunk_disj ff 256 shf 32) by (unfold chunk_disj; clear - FFshf; lia).
    assert (DJ7 : chunk_disj fp 1 shf 32) by (unfold chunk_disj; clear - FPshf; lia).
    assert (DJ14 : chunk_disj shf 32 fp 1) by (unfold chunk_disj; clear - FPshf; lia).
    change (stale (ff + 256 <= shf \/ shf + 32 <= ff)) in FFshf. change (stale (fp + 1 <= shf \/ shf + 32 <= fp)) in FPshf.
    change (stale (as_FSB H + 11571200 <= 2147446784 \/ 17594333495296 <= as_FSB H)) in F5.
    pose proof (munch_refl [(fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 27 st1. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    (* [comment removed for export] *)
    do 51 st1. step.
    (* [comment removed for export] *)
    release_frame LOC ST (sp1 + 88). release_frame GAP ST (bv_unsigned sp + -104). release_frame FR ST (bv_unsigned sp).
    unfold afx_final. finish.
    all: try exact MU.
    - rewrite <- (lf_remove_head 2 ff fp LF). eapply (ah_release H HH); [exact RFS| left; reflexivity| exact MU| exact WM| |].
      + apply Forall_cons; [right; cbn [fst snd]; split; reflexivity|].
        apply Forall_cons; [left; unfold afs_write_ok; right; exists (2, ff, fp); split; [left; reflexivity| cbn [fst snd ff_addr ff_class blk_addr]; change (fsz 2) with 256; lia]|].
        apply Forall_cons; [left; unfold afs_write_ok; left; cbn [fst snd]; unfold stale in F5; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - F1 F2 F5 SHFB; lia|].
        apply Forall_nil.
      + lazymatch goal with |- mrd _ ?mx _ = _ => match goal with Hc : rw_cells asegs mx fp _ |- _ => exact (rw_cells_C1_mrd _ _ _ _ _ Hc) end end.
    - eapply ACONST_frame; [exact AC| exact MU| exact WM|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [ apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]
              | eapply (aconst_ok_aapp _ _ _ _ F4); unfold AFS_SIZE; lia ].
  Qed.
  (* [comment removed for export] *)
  Lemma acfreeex_spec : cfreeex_stmt H.
  Proof.
    unfold cfreeex_stmt, exdata_stmt_at. intros until CH. cbv zeta.
    intros VIS A0 A1 A2 [C0 K0] AD ADLO AD8 ACC AIN CS EX SEP HP KREL AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM RL RFS LFN CHN CHS HAL RAE. subst a0 a1 a2. subst c0 k0.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). acb.
    assert (LO' : lo <= bv_unsigned sp - 8416).
    { revert LO. unfold CFREEEX_STACK, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
        CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
        FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK. clear. intros LO. lia. }
    (* [comment removed for export] *)
    pose proof EX as EX0. destruct EX as (XI & XZ & XR & XM). destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *. subst xn. unfold MUTEX_SIZE in *.
    pose proof (ah_blocks H HH _ _ _ _ HP XI) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). cbn [blk_addr blk_size fst snd] in X1, X2, X3, X4, X5, X6, X7.
    destruct AIN as ([[bp bA] bN] & BIN & BLO & BHI). cbn [blk_addr blk_size fst snd] in BLO, BHI.
    pose proof (ah_blocks H HH _ _ _ _ HP BIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, B6, B7.
    pose proof (ah_thr H HH _ _ _ HP) as THR. unfold AIMG_TOP in X4, B4. unfold AFS_SIZE in X6, B6.
    subst tp. unfold errno_addr in ERR |- *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afx_pre; [exact ST| exact CEIL| exact LO| exact SPA| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (sp1 & jl & gapc & m1 & VIS1 & MU1 & WM1 & MI1 & FR1 & LOC1 & GAP1 & GSZ & SP1 & SP32 & ST1).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| |].
    { eapply afx_segA with (lo := lo) (LB := LB) (xp := xp) (bA := bA) (bN := bN); try eassumption; try reflexivity; try lia.
    }
    clear VIS VIS1 KREL.
    intros msF2 mo2 KREL2 MP2 PO. unfold afx_mid in PO.
    destruct PO as (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & j2 & hj & sj
                    & VIS2 & MU2 & WM2 & MI2 & ST2 & AC2 & RFS2 & FRESH & FR2 & LOC2 & GAP2 & FF2 & SH2 & FP2 & AD2 & CS2 & XM2).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & F1 & F2 & F4).
    change (fsz 2) with 256 in R2, P6. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6, F1, F2.
    pose proof (aapp_not_shadowland _ _ F4) as F5. unfold AFS_SIZE, ALOWSH_LO, AHI_LO in F5.
    assert (SHIN : sh (as_FSB H) <= sh ff /\ sh ff + 32 <= sh (as_FSB H + AFS_SIZE))
      by (unfold sh, AFS_SIZE; clear - P5 P6 M64; Z.div_mod_to_equations; lia).
    set (shf := sh ff) in *.
    assert (SHFB : 2148993224 <= shf /\ shf + 32 <= AHI_LO)
      by (subst shf; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - R1 R2 ACEILB; Z.div_mod_to_equations; lia). unfold AHI_LO in SHFB.
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32); (xa + 4, xa + 8)]).
    { unfold aclient_write_ok, AFS_FLAGS, AFS_SIZE in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; right; left. exact SHIN.
      - right; right; left. exists (xp, xa, 40). split; [exact XI| cbn; lia]. }
    assert (HP2 : as_RHEAP H s LB m2) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU2| exact WM2| exact CW]).
    assert (AUX2 : as_rauxv_ok H m2 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU2| exact WM2| exact CW]).
    assert (ERR2 : rw_cells asegs m2 (ATP + -164) [C4 errv]).
    { revert ERR. rewrite unsigned_lit by (unfold ATP; lia). intros ERR. eapply errno_across; [exact ERR| exact MU2| exact WM2|].
      unfold ATP, AFS_FLAGS; cbn; clear - CEIL ACEILB F1 P1 R1 SHFB B4 BLO X4; repeat split; lia. }
    assert (IM2 : IMPL_mem m2) by (eapply IMPL_across; [exact MU2| exact WM2| unfold A_malloc_impl, AFS_FLAGS; cbn; clear - CEIL ACEILB F1 P1 R1 SHFB B4 BLO X4; repeat split; lia| exact IM]).
    assert (GM2 : GOT_mem m2) by (eapply GOT_across; [exact MU2| exact WM2| unfold A_got_CRYPTO_malloc, AFS_FLAGS; cbn; clear - CEIL ACEILB F1 P1 R1 SHFB B4 BLO X4; repeat split; lia| exact GM]).
    assert (XP2 : xpres H LB (bv_unsigned sp) ((ad, ad + 16) :: mutex_foot xa ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]) m m2).
    { eapply (xpres_of_munch H s LB _ _ _ m m m2); [exact HH| exact HP| exact MU2| exact WM2|]. unfold mutex_foot, AFS_FLAGS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd app];
        first [ left; lia | right; intros q Hq; cbn; lia ]. }
    assert (CH0 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m2); [exact CHN| exact CHS| exact MU2|]. unfold AFS_FLAGS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; clear - LO' F1 F2 P1 P2 P4 P6 R1 R2 SHFB B4 B5 BLO BHI X4 X5 CEIL SPR ACEILB; lia. }
    assert (CH1 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR2 as FRl.
      lazymatch type of FRl with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
        change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest) with ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ rest) in FRl end.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRl. destruct FRl as [_ FRl]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FRl.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -104 + 88) by lia.
      first [exact FRl | revert FRl; rewrite !Z_to_bv_bv_unsigned; intros FRl; exact FRl]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> sp1 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : sp1 mod 16 = 0) by (clear - SP32; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS2| ..];
        rewrite ?unsigned_lit by lia.
      all: first [exact HP2| exact KREL2| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16'| exact AC2| exact CH1| exact CHS1
                 | exact IM2| exact GM2| unfold CFREE_STACK, AFREE_STACK; lia| lia| show_goal]. }
    clear CF.
    intros [msF3 mo3] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & sx3 &
                    VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & HP3 & IM3 & GM3 & AL3).
    rewrite (unsigned_lit sp1) in ST3, XP3 by lia.
    unfold AFX_RA_CF in VIS3. replace (ret_pc (Z_to_bv 64 2091260)) with (Z_to_bv 64 2091260) in VIS3 by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (T : forall A cs, rw_cells asegs m2 A cs -> aclient_range H LB sp1 A (Z.of_nat (cells_size cs)) -> rw_cells asegs m3 A cs)
      by (intros A cs Hc Hr; eapply (xpres_rw_cells' H); [exact XP3| exact Hc| exact Hr| apply Forall_nil]).
    apply T in FR2; [| left; cbn; lia]. apply T in LOC2; [| left; cbn; lia]. apply T in GAP2; [| left; lia].
    apply T in FF2; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia].
    apply T in SH2; [| right; right; right; right; right; left; cbn; exact SHIN].
    apply T in FP2; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia].
    apply T in AD2; [| right; right; left; exists (bp, bA, bN); split; [exact BIN| cbn; lia]].
    unfold MUTEX in XM2. apply T in XM2; [| right; right; left; exists (xp, xa, 40); split; [exact XI| cbn; lia]]. clear T.
    assert (RFS3 : as_RFS H ((2, ff, fp) :: LF) m3) by (eapply (RFS_via_xpres H HH); [exact RFS2| exact XP3| apply Forall_nil]).
    assert (CS3 : CTX_statics m3 x).
    { eapply (CTX_statics_frame []); [exact CS2|]. eapply magree_mono; [eapply (magree_lib_xpres H); exact XP3|].
      intros a Ha. eapply lib_addr_mono; [| exact Ha]. intros b Hb. destruct Hb. }
    (* [comment removed for export] *)
    pose proof (aapp_not_shadowland _ _ B7) as BNS. pose proof (aapp_not_shadowland _ _ X7) as XNS. unfold ALOWSH_LO, AHI_LO in BNS, XNS.
    assert (ADFF : ad + 16 <= ff \/ ff + 256 <= ad) by (clear - B6 BLO BHI P5 P6; lia).
    assert (ADSH : sh AIMG_TOP <= sh ad /\ sh ad + 2 <= AHI_LO /\ (sh ad + 2 <= shf \/ shf + 32 <= sh ad)).
    { subst shf. unfold sh, AHI_LO, AIMG_TOP. rewrite ASHADOW_BASE_val. clear - ADFF B4 B5 BLO BHI AD8 M8 ACEILB.
      assert (Q1 : 12599296 / 8 <= ad / 8) by (apply Z.div_le_mono; lia).
      assert (Q2 : ad / 8 + 2 <= 2^44) by (Z.div_mod_to_equations; lia).
      split; [lia|]. split; [lia|].
      destruct ADFF as [D|D]; [left | right].
      - assert (Q3 : (ad + 16) / 8 <= ff / 8) by (apply Z.div_le_mono; lia).
        replace ((ad + 16) / 8) with (ad / 8 + 2) in Q3 by (rewrite <- (Z.div_add ad 2 8) by lia; reflexivity). lia.
      - assert (Q3 : (ff + 256) / 8 <= ad / 8) by (apply Z.div_le_mono; lia).
        replace ((ff + 256) / 8) with (ff / 8 + 32) in Q3 by (rewrite <- (Z.div_add ff 32 8) by lia; reflexivity). lia. }
    let v := eval vm_compute in (sh AIMG_TOP) in change (sh AIMG_TOP) with v in ADSH. unfold AHI_LO in ADSH.
    assert (ACC2 : accessible m2 ad 16).
    { eapply accessible_transport; [exact ACC| exact MU2|]. intros q Hq. unfold outside. cbn.
      clear - Hq ADSH SHFB ACEILB CEIL LO' F5 F1 P1 P2 P3 P4 P5 P6 R1 R2 BNS BLO BHI XNS X4 B4 AD8. unfold sh in *. rewrite ?ASHADOW_BASE_val in *.
      assert (Q8 : ad / 8 <= q / 8 /\ q / 8 <= ad / 8 + 1) by (clear - Hq AD8; Z.div_mod_to_equations; lia).
      unfold AFS_FLAGS. repeat split; lia. }
    assert (ACC3 : accessible m3 ad 16).
    { eapply (ashobj_accessible_xpres H HH) with (SP := sp1) (X := []); [exact HP2| lia| left; exists (bp, bA, bN); split; [exact BIN| cbn; lia]| exact ACC2| exact XP3| apply Forall_nil]. }
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| |].
    { eapply afx_segC1 with (lo := lo); try eassumption; try (unfold AIMG_TOP, AAPP_HI in *; lia). }
    intros msF4 mo4 KREL4 MP4 PO. unfold afx_c1_post in PO.
    destruct PO as (z0 & z1 & z2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & AC4).
    (* [comment removed for export] *)
    assert (T4 : forall A cs, rw_cells asegs m3 A cs -> (A + Z.of_nat (cells_size cs) <= lo \/ sp1 <= A) -> rw_cells asegs m4 A cs)
      by (intros A cs Hc Hr; eapply rw_cells_transport; [exact Hc| exact MU4| exact WM4| cbn; lia]).
    apply T4 in FR2; [| right; lia]. apply T4 in LOC2; [| right; lia]. apply T4 in GAP2; [| right; lia].
    apply T4 in FF2; [| left; cbn; lia]. apply T4 in SH2; [| left; cbn; clear - SHFB ACEILB CEIL; lia]. apply T4 in FP2; [| left; cbn; lia].
    apply T4 in AD2; [| left; cbn; lia]. apply T4 in XM2; [| left; cbn; lia]. clear T4.
    assert (HP4 : as_RHEAP H sx3 LB m4) by (eapply (ah_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4| constructor; [left; cbn; lia| constructor]]).
    assert (AUX4 : as_rauxv_ok H m4 B) by (eapply (ah_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4| constructor; [left; cbn; lia| constructor]]).
    assert (RFS4 : as_RFS H ((2, ff, fp) :: LF) m4)
      by (eapply (ah_RFS_frame H HH); [exact RFS3| exact MU4| exact WM4|];
          apply Forall_cons; [left; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - F1 F2 CEIL LO' SP1 ACEILB; lia| apply Forall_nil]).
    assert (CS4 : CTX_statics m4 x)
      by (eapply CTX_statics_across; [exact CS3| exact MU4| exact WM4|]; apply Forall_cons; [cbn [fst snd]; unfold AIMG_TOP; clear - CEIL ACEILB; lia| apply Forall_nil]).
    assert (ERR4 : rw_cells asegs m4 (ATP + -164) [C4 errv]).
    { revert ERR3. rewrite unsigned_lit by (unfold ATP; lia). intros ERR3. eapply errno_across; [exact ERR3| exact MU4| exact WM4| unfold ATP; cbn; clear - CEIL ACEILB LO' SP1; repeat split; lia]. }
    (* [comment removed for export] *)
    pose proof AD2 as ADcb. apply rw_cells_flatten in ADcb. cbn [cells_size csize cells_bytes cbytes Nat.add app] in ADcb.
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| |].
    { eapply (asan_memset_specZ H HH) with (lo := lo); try eassumption; try lia.
      all: lazymatch goal with
           | |- accessible _ _ _ => eapply accessible_across; [exact ACC3| exact MU4| apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]]
           | |- shvis _ _ _ => eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP4 BIN)| lia| exact BLO| exact BHI| lia| lia]
           | |- in_app_mem _ _ => eapply aapp_in_app_mem; [exact B7| exact BLO| exact BHI]
           | |- aconst_ok _ => eapply aconst_ok_aapp; [exact B7| lia| lia]
           | |- _ => show_goal
           end.
      all: fail "CUT-MSpre". }
    intros msF5 mo5 KREL5 MP5 PO. unfold amemset_postZ in PO.
    destruct PO as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & ADZ & AC5).
    change (Z.to_nat 16) with 16%nat in ADZ. pose proof (rw_cells_zero16_C8 _ _ ADZ) as AD5. clear ADZ.
    (* [comment removed for export] *)
    assert (T5 : forall A cs, rw_cells asegs m4 A cs -> (A + Z.of_nat (cells_size cs) <= ad \/ ad + 16 <= A) -> (A + Z.of_nat (cells_size cs) <= sp1 - 4096 \/ sp1 <= A) -> rw_cells asegs m5 A cs)
      by (intros A cs Hc H1 H2; eapply rw_cells_transport; [exact Hc| exact MU5| exact WM5| cbn; clear - H1 H2; lia]).
    apply T5 in FR2; [| cbn; lia| cbn; right; lia]. apply T5 in LOC2; [| cbn; lia| cbn; right; lia]. apply T5 in GAP2; [| lia| right; lia].
    apply T5 in FF2; [| cbn; clear - ADFF; lia| cbn; left; lia]. apply T5 in SH2; [| cbn; clear - BNS BLO BHI SHFB; lia| cbn; left; clear - SHFB ACEILB CEIL LO' SP1; lia].
    apply T5 in FP2; [| cbn; clear - B6 BLO BHI P3 P4; lia| cbn; left; lia].
    apply T5 in XM2; [| cbn; clear - SEP; lia| cbn; left; lia]. clear T5.
    pose proof XM2 as XM5. pose proof FP2 as FP5. clear XM2 FP2.
    assert (CW5 : Forall (aclient_write_ok H LB) [(ad, ad + 16); (sp1 - 4096, sp1)]).
    { unfold aclient_write_ok. apply Forall_cons; [right; right; left; exists (bp, bA, bN); split; [exact BIN| cbn; lia]|].
      apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (HP5 : as_RHEAP H sx3 LB m5) by (eapply (ah_RHEAP_frame H HH); [exact HP4| exact MU5| exact WM5| exact CW5]).
    assert (AUX5 : as_rauxv_ok H m5 B) by (eapply (ah_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5| exact CW5]).
    assert (RFS5 : as_RFS H ((2, ff, fp) :: LF) m5).
    { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - B6 B4 BLO BHI; lia|].
      apply Forall_cons; [left; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - F1 F2 CEIL LO' SP1 ACEILB; lia| apply Forall_nil]. }
    assert (CS5 : CTX_statics m5 x)
      by (eapply CTX_statics_across; [exact CS4| exact MU5| exact WM5|]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - B4 BLO CEIL ACEILB LO' SP1; lia).
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv])
      by (eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; clear - B4 BLO CEIL ACEILB LO' SP1; repeat split; lia]).
    assert (MF5 : MEMFLAG m5 1).
    { eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; clear - B4 BLO CEIL ACEILB LO' SP1; repeat split; lia|].
      eapply MEMFLAG_across; [exact MU4| exact WM4| unfold A_mem_inited; cbn; clear - CEIL ACEILB LO' SP1; repeat split; lia|].
      eapply MEMFLAG_xpres0; [exact XP3|]. eapply MEMFLAG_across; [exact MU2| exact WM2| | exact MF].
      unfold A_mem_inited, AFS_FLAGS; cbn; clear - CEIL ACEILB F1 P1 R1 SHFB X4; repeat split; lia. }
    assert (IM5 : IMPL_mem m5).
    { eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; clear - B4 BLO CEIL ACEILB LO' SP1; repeat split; lia|].
      eapply IMPL_across; [exact MU4| exact WM4| unfold A_malloc_impl; cbn; clear - CEIL ACEILB LO' SP1; repeat split; lia| exact IM3]. }
    assert (GM5 : GOT_mem m5).
    { eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; clear - B4 BLO CEIL ACEILB LO' SP1; repeat split; lia|].
      eapply GOT_across; [exact MU4| exact WM4| unfold A_got_CRYPTO_malloc; cbn; clear - CEIL ACEILB LO' SP1; repeat split; lia| exact GM3]. }
    assert (RL5 : arelro_lib m5).
    { eapply arelro_across; [| exact MU5| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - B4 BLO CEIL ACEILB LO' SP1; lia].
      eapply arelro_across; [| exact MU4| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - CEIL ACEILB LO' SP1; lia].
      eapply arelro_xpres0; [| exact XP3].
      eapply arelro_across; [exact RL| exact MU2| unfold AFS_FLAGS; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - CEIL ACEILB F1 P1 R1 SHFB X4; lia]. }
    (* [comment removed for export] *)
    unfold AFX_RA_MS in VIS5 |- *. replace (ret_pc (Z_to_bv 64 2091304)) with (Z_to_bv 64 2091304) in VIS5 by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| |].
    { eapply afx_segC2 with (lo := lo) (obj := obj) (ad := ad);
        try eassumption; try reflexivity; try lia. }
    clear VIS2 VIS3 VIS4 VIS5 KREL1 KREL2 KREL3 KREL4.
    intros msF6 mo6 KREL6 MP6 PO. unfold afx_final in PO.
    destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m6 & VIS6 & MU6 & WM6 & MI6 & ST6 & RFS6 & AC6).
    fold shf in MU6.
    (* [comment removed for export] *)
    assert (CW6 : Forall (aclient_write_ok H LB) [(fp, fp + 1); (ff, ff + 256); (shf, shf + 32)]).
    { unfold aclient_write_ok, AFS_SIZE in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; right; left. exact SHIN. }
    apply (ah_done H HH). unfold exdata_post, c3_frame. cbv beta. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, (Z_to_bv 64 fp), e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, m6, sx3.
    exists [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 2); (sh ff, sh ff + fshn 2)].
    split; [exact VIS6|]. split; [exact I|].
    split; [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact MP3]| exact MP4]| exact MP5]| exact MP6]|].
    split.
    { split; [exact KREL6|]. split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
      split; [rewrite unsigned_lit by (unfold ATP; lia); eapply errno_across; [exact ERR5| exact MU6| exact WM6| unfold ATP; cbn; clear - P1 R1 SHFB; repeat split; lia]|].
      split; [eapply (ah_rauxv_frame H HH); [exact AUX5| exact MU6| exact WM6| exact CW6]|].
      split; [eapply (ah_RHEAP_frame H HH); [exact HP5| exact MU6| exact WM6| exact CW6]|].
      split. { eapply MEMFLAG_across; [exact MU6| exact WM6| unfold A_mem_inited; cbn; clear - P1 R1 SHFB; repeat split; lia| exact MF5]. }
      split. { eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; clear - P1 R1 SHFB; repeat split; lia| exact IM5]. }
      split. { eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; clear - P1 R1 SHFB; repeat split; lia| exact GM5]. }
      eapply arelro_across; [exact RL5| exact MU6| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - P1 R1 SHFB; lia]. }
    (* [comment removed for export] *)
    assert (STW : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) [(fp, fp + 1); (ff, ff + 256); (shf, shf + 32)])
      by (unfold AIMG_TOP; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - P1 R1 SHFB; lia).
    split; [eapply CTX_statics_across; [exact CS5| exact MU6| exact WM6| exact STW]|].
    split. { rewrite Hx. unfold EXLOCK, MUTEX. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [reflexivity|]. split; [exact XR|].
             eapply rw_cells_transport; [exact XM5| exact MU6| exact WM6|]. cbn. clear - X6 XNS P3 P4 P5 P6 SHFB. repeat split; lia. }
    split; [eapply rw_cells_transport; [exact AD5| exact MU6| exact WM6| cbn; clear - B6 BLO BHI BNS P3 P4 P5 P6 SHFB; repeat split; lia]|].
    split; [subst shf; change 256 with (fsz 2); change 32 with (fshn 2); exact (fs_scratch_of_fresh H _ _ _ _ FRESH)|].
    split; [exact RFS6|].
    split.
    { (* [comment removed for export] *)
      rewrite Hx. cbn [blk_addr fst snd]. change (fsz 2) with 256. change (fshn 2) with 32. fold shf.
      eapply (xpres_trans H); [exact XP2|]. eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP3| lia| auto| intros q K; destruct K]|].
      eapply (xpres_trans H); [eapply (xpres_of_munch H sx3 LB _ _ _ m3 m3 m4); [exact HH| exact HP3| exact MU4| exact WM4| constructor; [left; cbn; lia| constructor]]|].
      eapply (xpres_trans H).
      - eapply (xpres_of_munch H sx3 LB _ _ _ m4 m4 m5); [exact HH| exact HP4| exact MU5| exact WM5|]. unfold mutex_foot, AFS_FLAGS.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd app]; first [left; lia| right; intros q Hq; cbn; lia].
      - eapply (xpres_of_munch H sx3 LB _ _ _ m5 m5 m6); [exact HH| exact HP5| exact MU6| exact WM6|]. unfold mutex_foot, AFS_FLAGS.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd app]; right; intros q Hq; cbn; lia. }
    exact AL3.
    Unshelve. all: exact [].   (* [comment removed for export] *)
  Qed.
End S.
