(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_r2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AASAN_REALLOC : Z := 0x3287c.

Section R2.
Hypothesis get_thread_stats_proof : get_thread_stats_spec.
Hypothesis set_errno_enomem_proof : set_errno_enomem_spec.

(* [comment removed for export] *)
Lemma realloc_g1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (A n S lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  a0 = wz A -> a1 = wz n -> a2 = wz S -> A <> 0 -> 0 < n < 2^32 -> 0 <= A < 2^64 -> 0 <= S < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jr : list byte) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x32994) (wz (bv_unsigned sp - 64)) gp tp t0' t1' t2' (wz S) (wz A) (wz A_ALLOC) (wz n) (wz 8) (wz S) (wz 1) (wz 1) a6' a7'
                    (wz A_ALLOC) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz AALLOCATE) fc None m' (seg_rom asegs)
      /\ munch [(st_t st + 2856, st_t st + 2872); (bv_unsigned sp - 96, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ RTREP st m'
      /\ stk asegs m' lo (bv_unsigned sp - 64)
      /\ rw_cells asegs m' (bv_unsigned sp - 64) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz 0x32918)]
      /\ rw_cells asegs m' (bv_unsigned sp - 16) [CB 8 jr; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AASAN_REALLOC) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI TP -> -> -> HA Hn RA RS ST HCL LO.
  pose proof (munch_refl [(st_t st + 2856, st_t st + 2872); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU0.
  pose proof (t_range st WF) as TR. olin TR. pose proof (tpx_ok_of_RTWF st WF) as HX.
  destruct (rr_thread st m HR) as (TV & _).
  destruct (vis_c8 m _ _ (st_t st + 2856) TV ltac:(lia) ltac:(lia)) as [sj1 TS1].
  destruct (vis_c8 m _ _ (st_t st + 2864) TV ltac:(lia) ltac:(lia)) as [sj2 TS2]. clear TV.
  unfold AASAN_REALLOC, AALLOCATE, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. idtac.
  leaf_prep. subst tp.
  carve_frame 16%nat ST.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  carve_frame 48%nat ST1.
  do 7 lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU0 WM. clear MU0.
  call get_thread_stats_proof; [exact HR1| exact WF| eassumption| reflexivity| rewrite ?unsigned_lit by lia; exact ST1| idtac; lia| rewrite ?unsigned_lit by lia; lia|].
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. restk. rewrite ?unsigned_lit in ST by lia. unfold T_STATS.
  clear HR1.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (HR2 : RTREP st mx) end.
  { lazymatch type of MU with munch ?W _ ?mx =>
      eapply (tpz_transport_cache st WF HX W ltac:(unfold tpz_ok, T_ACACHE, T_UNWINDING, CEIL; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) m mx MU WM HR) end.
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma realloc_g2_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A k n r : Z) (b1 : byte) (cid : word),
  mem_inv asegs m ->
  a0 = wz r -> s1 = wz A -> s3 = wz n -> r <> 0 -> 0 <= r < 2^64 -> 0 <= k < 2^40 -> 0 <= n < 2^64 ->
  AIMG_HI + 16 <= A -> A + 8 <= alloc_ceiling ->
  rw_cells asegs m (A + -16) [C1 (zb CHUNK_ALLOCATED); C1 b1; C2 (wz (size_hi k)); C4 (wz (size_lo k)); C8 cid] ->
  ro_cells asegs m 0xa1fa8 [C8 (wz 0xa3e00)] -> ro_cells asegs m 0xa3e00 [C8 (wz A_MUSL_MEMCPY)] ->
  evt asegs (fun ms' => exists (a3' : word),
      ms' = MS (mkR (wz 0x32a0c) sp gp tp t0 t1 t2 s0 s1 (wz r) (wz A) (wz (Z.min n (usz k))) a3' a4 a5 a6 a7
                    s2 (wz (Z.min n (usz k))) (wz r) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz A_MUSL_MEMCPY) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32994) fc None m (seg_rom asegs)).
Proof.
  intros until cid. intros MI -> -> -> Hr Rr Hk Hn A1 A2 HDR G1 G2.
  (nelimp (size_hilo k Hk) 3%nat; intros SH1 SL1 SHL).
  unfold CHUNK_ALLOCATED, KHIGHMEM_BEG, AIMG_HI, A_MUSL_MEMCPY in *. idtac. leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (sxb_zb_small' 2) by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. lstep. (* [comment removed for export] *) rewrite size_join by lia.
  lstep; if2 BR. (* [comment removed for export] *)
  - lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 635376)) with (Z_to_bv 64 635376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite (Z.min_l n (usz k)) by lia.
    finish.
  - lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep.
    replace (ret_pc (Z_to_bv 64 635376)) with (Z_to_bv 64 635376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite (Z.min_r n (usz k)) by lia.
    finish.
Qed.

(* [comment removed for export] *)
Lemma realloc_g4_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vra v0 v1 v2 v3 v4 v5 v6 w0 w1 w2 w3 w4 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP r : Z) (jr : list byte),
  mem_inv asegs m ->
  bv_unsigned sp = SP + -2208 -> s4 = wz r -> r <> 0 -> 0 <= r < 2^64 ->
  alloc_ceiling <= SP + -2208 -> SP <= 2^64 ->
  rw_cells asegs m (SP + -2208) [C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 (wz 0x32918)] ->
  rw_cells asegs m (SP + -2160) [CB 8 jr; C8 (wz 0x54a40)] ->
  rw_cells asegs m (SP + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  evt asegs (fun ms' =>
      ms' = MS (mkR vra (wz SP) gp tp t0 t1 t2 v0 v1 (wz r) a1 a2 a3 a4 a5 a6 a7
                    v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32a28) fc None m (seg_rom asegs)).
Proof.
  intros until jr. intros MI ESP -> Hr Rr C1 C2 FRR FRA FRI.
  idtac. leaf_prep.
  replace sp with (Z_to_bv 64 (SP + -2208)) by (rewrite <- ESP; apply Z_to_bv_bv_unsigned).
  lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x32918)) with (Z_to_bv 64 0x32918) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x54a40)) with (Z_to_bv 64 0x54a40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. do 8 lstep. lstep. lstep. (* [comment removed for export] *)
  replace (SP + -2208 + 48 + 16 + 112 + 2032) with SP by lia.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma realloc_g5_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vra v0 v1 v2 v3 v4 v5 v6 w0 w1 w2 w3 w4 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP lo : Z) (jr : list byte) (errv : word),
  mem_inv asegs m -> tp = wz ATP ->
  bv_unsigned sp = SP + -2208 -> a0 = wz 0 ->
  alloc_ceiling <= lo -> lo + 16 <= SP + -2208 -> SP <= 2^64 ->
  stk asegs m lo (SP + -2208) ->
  rw_cells asegs m AERRNO [C4 errv] ->
  rw_cells asegs m (SP + -2208) [C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 (wz 0x32918)] ->
  rw_cells asegs m (SP + -2160) [CB 8 jr; C8 (wz 0x54a40)] ->
  rw_cells asegs m (SP + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz SP) gp tp t0' t1' t2' v0 v1 (wz 0) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch [(lo, SP + -2144); (AERRNO, AERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (SP + -2144)
      /\ rw_cells asegs m' AERRNO [C4 (wz ENOMEM)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32994) fc None m (seg_rom asegs)).
Proof.
  intros until errv. intros MI TP ESP -> HCL LO C2 ST ERR FRR FRA FRI.
  pose proof (munch_refl [(lo, SP + -2144); (AERRNO, AERRNO + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold AERRNO, ATP, ENOMEM in *. idtac. leaf_prep. subst tp.
  replace sp with (Z_to_bv 64 (SP + -2208)) by (rewrite <- ESP; apply Z_to_bv_bv_unsigned).
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  release_frame FRR ST (SP + -2208 + 48). replace (SP + -2208 + 48) with (SP + -2160) in ST by lia.
  replace (ret_pc (Z_to_bv 64 0x32918)) with (Z_to_bv 64 0x32918) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  callxp ltac:(eapply set_errno_enomem_proof with (lo := lo) (errv := errv);
    [ eassumption| reflexivity| exact ERR| rewrite ?unsigned_lit by lia; exact ST| idtac; lia| rewrite ?unsigned_lit by lia; lia ])
    ltac:(unfold leaf_post, AERRNO, ATP, ENOMEM; change (6148688 - 164) with 6148524; rewrite ?unsigned_lit by lia).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (SP + -2160) [CB 8 _; C8 _] |- _ => rename H into FRA' end.
  release_frame FRA' ST2 (SP + -2160 + 16).
  replace (ret_pc (Z_to_bv 64 0x54a40)) with (Z_to_bv 64 0x54a40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. do 8 lstep. lstep. lstep. (* [comment removed for export] *)
  try replace (SP + -2160 + 16 + 112 + 2032) with SP by lia. try replace (SP + -2208 + 48 + 16 + 112 + 2032) with SP by lia.
  try replace (SP + -2160 + 16) with (SP + -2144) in * by lia.
  finish; eassumption.
Qed.
End R2.


End CeilWrap.
End RTW_m_r2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_m_rtail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec RTW_m_r2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_dcore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma trs_put_twice : forall tr T T1 T2, trs_put tr T T1 -> trs_put tr T1 T2 -> trs_put tr T T2.
Proof.
  intros tr T T1 T2 [[I1 ->]|[N1 ->]] H2.
  - exact H2.
  - destruct H2 as [[I2 ->]|[N2 ->]]; [right; auto|]. exfalso. apply N2. left. reflexivity.
Qed.
Lemma trs_put_in : forall tr T T1, trs_put tr T T1 -> In tr T1.
Proof. intros tr T T1 [[I ->]|[N ->]]; [exact I| left; reflexivity]. Qed.

Lemma bytes_at_inj : forall m a xs ys, bytes_at asegs m a xs -> bytes_at asegs m a ys -> length xs = length ys -> xs = ys.
Proof.
  intros m a xs ys (_ & _ & HX) (_ & _ & HY) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length xs)) as [Hi|Hi].
  - rewrite <- (HX i Hi), <- (HY i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None xs i) Hi), (proj2 (nth_error_None ys i) ltac:(lia)). reflexivity.
Qed.

Lemma bytes_at_firstn : forall m a bs k, bytes_at asegs m a bs -> bytes_at asegs m a (firstn k bs).
Proof.
  intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply (proj1 (bytes_at_app _ _ _ _ _) ) in H. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_merge : forall m a n1 n2 b1 b2, rw_cells asegs m a [CB n1 b1; CB n2 b2] -> rw_cells asegs m a [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m a n1 n2 b1 b2 H. pose proof H as [[Hwf _] _]. cbn in Hwf. eapply rw_cells_rebytes; [| | | exact H].
  - cbn. rewrite length_app. lia.
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Definition realloc_tail_post (sp gp tp : word) (s7 s8 s9 s10 s11 : word) (rac s0c s1c s2c s3c s4c s5c s6c : word) (F : bvmap 5 word) (fc : bv 32)
    (st4 : rtstate) (tr : list Z) (A k n r lo : Z) (old : list byte) (LB1 : list cblock) (errv : word) (m4 : word -> option byte) (g4 : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate) (junk : list byte),
    ms' = MS (mkR rac sp gp tp t0 t1 t2 s0c s1c (wz r) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rac) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv]
    /\ cj_pres (st_sp0 st4) (remove_first ck_eqb (A, k) LB1) (st_lf st4) (bv_unsigned sp) m4 m'
    /\ gmono g4 g' /\ trs_put tr (st_trs st4) (st_trs st')
    /\ RTS st' m' mo' g' /\ LOK asegs mo' /\ BINV mo' g'
    /\ st_sp0 st' = st_sp0 st4 /\ st_lb st' = (r, n) :: remove_first ck_eqb (A, k) LB1 /\ st_lf st' = st_lf st4
    /\ st_apend st' = st_apend st4 /\ st_spend st' = st_spend st4 /\ st_qpend st' = st_qpend st4
    /\ st_qtmp st' = [] /\ st_qcur st' = []
    /\ budget_ok st4 g4 st' g' cost_free
    /\ rw_cells asegs m' r [CB (Z.to_nat (Z.min k n)) (firstn (Z.to_nat (Z.min k n)) old); CB (Z.to_nat (n - Z.min k n)) junk].

Definition realloc_tail_stmt : Prop :=
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (rac s0c s1c s2c s3c s4c s5c s6c w0 w1 w2 w3 w4 : word) (jr : list byte)
         (F : bvmap 5 word) (fc : bv 32) (m4 : word -> option byte) (mo4 : Model) (g4 : lghost)
         (st4 : rtstate) (A k n r : Z) (tr : list Z) (lo : Z) (old uj : list byte) (LB1 : list cblock) (errv : word),
  RTS st4 m4 mo4 g4 -> st_lb st4 = (r, n) :: LB1 -> In (A, k) LB1 -> ~ In r (map fst LB1) -> ablock_range r n ->
  st_qtmp st4 = [] -> st_qcur st4 = [] -> st_qpend st4 = [] -> st_apend st4 = [] -> 0 < n < 2^32 -> r <> 0 -> tp = wz ATP ->
  rw_cells asegs m4 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2120)); C4 (wz (zlen tr)); C4 (wz 0)] ->
  rw_cells asegs m4 (bv_unsigned sp + -2120) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr -> In tr (st_trs st4) ->
  rw_cells asegs m4 r [CB (Z.to_nat n) uj] ->
  bytes_at asegs m4 A (firstn (Z.to_nat (Z.min k n)) old) -> Z.of_nat (length old) = k ->
  rw_cells asegs m4 AERRNO [C4 errv] ->
  rw_cells asegs m4 (bv_unsigned sp + -2208) [C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 (wz 0x32918)] ->
  rw_cells asegs m4 (bv_unsigned sp + -2160) [CB 8 jr; C8 (wz 0x54a40)] ->
  rw_cells asegs m4 (bv_unsigned sp + -64) [C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
  wr_at asegs m4 (bv_unsigned sp + -2144) 2144 ->
  bv_unsigned sp <= st_sp0 st4 ->
  rt_prov st4 + cost_free <= g_res g4 ->
  stk asegs m4 lo (bv_unsigned sp + -2208) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  mem_inv asegs m4 ->
  LSCPS asegs (realloc_tail_post sp gp tp s7 s8 s9 s10 s11 rac s0c s1c s2c s3c s4c s5c s6c F fc st4 tr A k n r lo old LB1 errv m4 g4)
        (MS (mkR (wz 0x32994) (wz (bv_unsigned sp + -2208)) gp tp t0 t1 t2 (wz (bv_unsigned sp + -2136)) (wz A) (wz r) a1 a2 a3 a4 a5 a6 a7
                 (wz A_ALLOC) (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x32994) fc None m4 (seg_rom asegs)) mo4 g4.

Section RTAIL.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis quarantine_put_proof : quarantine_put_spec2.

Theorem realloc_tail_proof : realloc_tail_stmt.
Proof.
  unfold realloc_tail_stmt. intros until errv.
  intros (HR4 & WF4 & HM4 & HG4 & HF4 & HSW4) Elb4 HIN1 NIN ABR Sqt Sqc Sqp Sap Hn RNZ TP SOBJ TRC2 TRL TRR TIN JK1 OLD4 LOLD ERR4 FRR3 FRA3 FR1 WR3 SPB4 COST ST4 HCL LO MI4.
  pose proof (wb_sp0 st4 (wf_base_ok st4 WF4)) as SP0. unfold AMALLOC_STACK in LO. unfold cost_free in COST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  change AERRNO with 6148524 in ERR4.
  apply lscps_assume. intros NWX HO4 HB4.
  assert (HINo : In (A, k) (st_lb st4)) by (rewrite Elb4; right; exact HIN1).
  assert (HINr : In (r, n) (st_lb st4)) by (rewrite Elb4; left; reflexivity).
  assert (HBo : In (A, k) (all_blocks st4)) by (unfold all_blocks; apply in_or_app; left; exact HINo).
  assert (HBr : In (r, n) (all_blocks st4)) by (unfold all_blocks; apply in_or_app; left; exact HINr).
  assert (NE : A <> r).
  { intros ->. apply NIN. apply in_map_iff. exists (r, k). split; [reflexivity| exact HIN1]. }
  pose proof (blocks_disj st4 WF4 A k r n HBo HBr NE) as DJ.
  (nelimp (block_geom st4 WF4 A k HBo) 7%nat; intros Gk _ OK OX OY OCE _). unfold usz in OY. unfold KHIGHMEM_BEG, AIMG_HI in OK. olin_all.
  (nelimp (block_geom st4 WF4 r n HBr) 9%nat; intros _ _ RK RX RY RCE RL16 RH16 _). unfold usz in RY. unfold KHIGHMEM_BEG, AIMG_HI in RK. olin_all.
  pose proof (block_extra st4 WF4 A k HBo) as (E8 & _).
  pose proof ABR as ABR'. unfold ablock_range, KHIGHMEM_BEG, AIMG_HI in ABR'. idtac.
  set (cl := Z.min n (usz k)) in *.
  assert (CL : 1 <= cl <= n /\ cl <= Z.max k 1) by (unfold usz in *; subst cl; lia).
  (* [comment removed for export] *)
  destruct (rr_live st4 m4 HR4 A k HINo) as ((b1 & cid & HC4 & HB1ok) & _ & _ & V4 & _).
  unfold hdr_cells, hdr_state_live, b_chunk_beg in HC4. replace (A - 16) with (A + -16) in HC4 by lia.
  pose proof (R_link_at m4 0xa1fa8 0xa3e00 (rr_link st4 m4 HR4) ltac:(vm_compute; reflexivity)) as GOT1.
  pose proof (R_link_at m4 0xa3e00 0x9b1f0 (rr_link st4 m4 HR4) ltac:(vm_compute; reflexivity)) as GOT2.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  eapply evt_cut; [eapply realloc_g2_spec with (A := A) (k := k) (n := n) (r := r);
    [ exact MI4| reflexivity| reflexivity| reflexivity| exact RNZ| lia| lia| lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia
    | exact HC4| exact GOT1| unfold A_MUSL_MEMCPY; exact GOT2 ] |].
  cbv beta. intros ms5 PO5. destruct PO5 as (a3x & ->).
  cbv beta delta [wz] in *. change (Z.min n (usz k)) with cl.
  (* [comment removed for export] *)
  destruct (vis_carve m4 _ _ A (Z.to_nat cl) V4 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold usz in *; lia)) as [ob OB].
  pose proof OB as [[_ OBB] _]. cbn [cells_bytes cbytes app] in OBB. rewrite app_nil_r in OBB.
  assert (LOB : length ob = Z.to_nat cl) by (pose proof OB as [[Hwf _] _]; cbn in Hwf; tauto).
  assert (EO : k <> 0 -> ob = firstn (Z.to_nat cl) old).
  { intros K1. assert (Ecl : Z.min k n = cl) by (subst cl; unfold usz; (lia_on Gk K1)).
    eapply (bytes_at_inj m4 A); [exact OBB| rewrite <- Ecl; exact OLD4|]. rewrite LOB, length_firstn. lia. }
  apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [Z.to_nat cl; Z.to_nat (n - cl)]%nat) in JK1; [| cbn; lia]. cbn [mk_CB_cells app firstn skipn] in JK1.
  pose proof (proj1 (rw_cells_app m4 r [CB (Z.to_nat cl) _] [CB (Z.to_nat (n - cl)) _]) JK1) as [DST JREST]. cbn [cells_size Cells.csize Nat.add] in JREST. clear JK1.
  pose proof (munch_refl [(r, r + cl)] m4) as MU. pose proof (wmono_refl asegs m4) as WM4.
  sepM. callxp ltac:(eapply memcpy_spec with (src := ob);
    [ rewrite unsigned_lit by lia; exact OBB| rewrite unsigned_lit by lia; exact LOB| rewrite !unsigned_lit by lia; exact DST
    | rewrite !unsigned_lit by (lia_on Hn OX ALx E8 ABR' CL); unfold usz in *; (lia_on DJ OX OY RX RY)| exact MI4 ])
    ltac:(unfold memcpy_post; rewrite !unsigned_lit by (lia_on Hn ABR' CL OX ALx E8); clear OLD4 DST).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI6; rename mx into m6 end.
  match goal with H : rw_cells _ m6 r [CB _ ob] |- _ => rename H into DST6 end.
  replace (ret_pc (Z_to_bv 64 0x32a0c)) with (Z_to_bv 64 0x32a0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (HR6 : RTREP st4 m6).
  { (nelimp (block_extra st4 WF4 r n HBr) 5%nat; intros RE8 REAB REABA REMB RERZ). pose proof (rz_size_range n) as [RRZ _].
    assert (SHB : SH (b_lo r n) + sh_tot n <= SH CEIL).
    { unfold sh_tot. rewrite <- rt_SH_aligned_add by (Z.div_mod_to_equations; lia). apply rt_SH_mono. change (b_lo r n + asz n) with (b_hi r n). unfold CEIL. lia. }
    rewrite SH_CEIL in SHB.
    (nelimp (block_geom st4 WF4 r n HBr) 4%nat; intros _ _ GKx _). (nelimp (ablk_lin _ _ GKx) 3%nat; intros GKa GKb _). pose proof (ablk_disj_band _ _ GKx) as GKd.
    unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in GKa, GKd. pose proof (rt_SH_mono 0 (b_lo r n) ltac:(lia)) as SHB0. change (SH 0) with 0x7fff8000 in SHB0.
    eapply (lbz_all st4 WF4 (tpx_ok_of_RTWF st4 WF4) r n HBr [(r, r + cl)] ltac:(constructor; [unfold lbz_ok; cbn [fst snd]; left; lia| constructor]) m4 m6 MU WM4 HR4).
    unfold WOK_block, b_chunk_beg.
    split; [cbn; lia|]. split; [intros HRZ; cbn; specialize (RERZ HRZ); unfold b_alloc_beg in *; lia|].
    split; [intros EP; specialize (REMB EP); pose proof REMB as REMB'; unfold b_map_beg, SEC_RZ, SEC_HDR in REMB'; cbn; lia|].
    cbn. blia. }
  assert (CP46 : cj_pres (st_sp0 st4) (remove_first ck_eqb (A, k) LB1) (st_lf st4) (bv_unsigned sp) m4 m6).
  { eapply cj_pres_of_munch; [exact MU| exact WM4|]. intros a Ha HC. cbn. split; [| exact I]. intros Hin.
    repeat match goal with X : olin_done _ _ |- _ => clear X end.
    destruct HC as [H|[H|[(A' & n' & Hb & Hr')|[(Fr & j & Hb & Hr')|H]]]].
    - unfold CEIL in *. lia.
    - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in H. (lia_on Hn RNZ SP0 NE DJ OX ALx RX RY RH16 ALx0 E8 ABR' CL H Hin).
    - pose proof (remove_first_In _ _ _ _ Hb) as Hb0.
      assert (HB' : In (A', n') (all_blocks st4)) by (unfold all_blocks; apply in_or_app; left; rewrite Elb4; right; exact Hb0).
      assert (NE' : A' <> r).
      { intros ->. apply NIN. apply in_map_iff. exists (r, n'). split; [reflexivity| exact Hb0]. }
      pose proof (blocks_disj st4 WF4 A' n' r n HB' HBr NE') as D'. (nelimp (block_geom st4 WF4 A' n' HB') 6%nat; intros _ _ _ X' Y' _). unfold usz in Y'. (lia_on RX RY Hr' Hin D' X' Y').
    - (nelimp (frame_range st4 WF4 Fr j Hb) 4%nat; intros Hk X Y AL). (nelimp (fs_range st4 WF4) 3%nat; intros F1 F2 _).
      pose proof (loose_blockfree st4 WF4 _ _ (wb_fs_loose st4 (wf_base_ok st4 WF4)) r n HBr) as D'. change FS_FRAMES_OFF with 36864 in X. unfold FS_TOTAL in *.
      destruct Hr' as [Hr'|Hr']; [unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on Hn RNZ SP0 NE DJ OX ALx RX RY RH16 ALx0 E8 ABR' CL Hr' Hin X Y AL D')|].
      pose proof (rt_SH_bounds Fr ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as SBlo. pose proof (rt_SH_bounds (Fr + fsz j) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; (cut_on [Hn SP0 RY RH16 ALx0 ABR' CL Hr' Hin X Y AL F1 SBlo] blia))) as SB. rewrite (rt_SH_aligned_add Fr (fsz j) AL) in SB. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
    - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 17594333495296 in H. lia. }
  assert (ES46 : errno_same m4 m6).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG6 : GWIN st4 m6 mo4 g4) by (eapply GWIN_mem; [exact HG4| exact HO4| exact WM4]).
  assert (WR6 : wr_at asegs m6 (bv_unsigned sp + -2144) 2144) by (first [exact WR3| eapply wr_at_wmono; [exact WR3| exact WM4]]).
  clear MU WM4.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof (dealloc_core_proof depot_put_proof quarantine_put_proof) as DC. unfold dealloc_core_stmt in DC.
    eapply DC with (st := st4) (A := A) (n := k) (S := bv_unsigned sp + -2136) (tr := tr) (lo := lo); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR6 WF4 HM4 HG6 HF4 HSW4).
    - exact HINo. - exact Sqt. - exact Sqc. - exact Sqp. - exact Sap.
    - exact TP.
    - replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia.
      apply (proj2 (rw_cells_app m6 _ [C8 _] [C8 _])). split; [exact (rw_cells_take m6 _ [C8 _] [C4 _; C4 _] SOBJ)|]. cbn [cells_size Cells.csize Nat.add].
      apply c44_c8; [lia|]. exact (rw_cells_drop m6 _ [C8 _] [C4 _; C4 _] SOBJ).
    - replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia. exact (proj1 TRC2).
    - exact TRL. - exact TRR. - left. exact TIN.
    - rewrite unsigned_lit by lia. lia. - unfold BST_SIZE. lia. - rewrite unsigned_lit by lia. lia.
    - unfold cost_free. lia.
    - rewrite unsigned_lit by lia. first [exact ST4| replace (bv_unsigned sp + -2144 + -64) with (bv_unsigned sp + -2208) by lia; exact ST4].
    - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEALLOC_STACK. lia.
    - exact MI6. }
  cbv beta. intros ms7 mo7 g7 PO.
  (nelim PO 36%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m7 st7 -> MI7 ST7 ES67 CP67 GM7 TP7 RTS7 HO7 HB7 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 BO67)
.
  rewrite unsigned_lit in ST7, CP67 by lia.
  replace (ret_pc (Z_to_bv 64 0x32a28)) with (Z_to_bv 64 0x32a28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS7 6%nat; intros HR7 WF7 HM7 HG7 HF7 HSW7).
  (* [comment removed for export] *)
  unfold cli_pres in CP67. rewrite Q1, Q2, Q3, Elb4 in CP67.
  assert (RNEQ : ck_eqb (A, k) (r, n) = false).
  { unfold ck_eqb. cbn [fst snd]. destruct (Z.eqb_spec A r) as [E|NE']; [exfalso; exact (NE E)| reflexivity]. }
  cbn [remove_first] in CP67. rewrite RNEQ in CP67.
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP67) in FRR3; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP67) in FRA3; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP67) in FR1; [| left; cbn; lia].
  apply (cj_pres_wr_at _ _ _ _ _ _ _ _ CP67) in WR6; [| left; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP67) in DST6; [| do 3 right; left; exists r, n; split; [left; reflexivity| cbn; lia]].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP67) in JREST; [| do 3 right; left; exists r, n; split; [left; reflexivity| cbn; lia]].
  apply lscps_assume. intros _ _ _.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  eapply evt_cut; [eapply realloc_g4_spec with (SP := bv_unsigned sp) (r := r);
    [ exact MI7| rewrite unsigned_lit by lia; lia| reflexivity| exact RNZ| lia| idtac; lia| lia
    | exact FRR3
    | exact FRA3
    | exact FR1 ] |].
  cbv beta. intros ms8 ->. cbv beta delta [wz] in *. try rewrite Z_to_bv_bv_unsigned.
  apply evt_done. apply lscps_done. unfold realloc_tail_post.
  nexists 14%nat. exists m7, st7.
  (* [comment removed for export] *)
  assert (JNK : exists junk, rw_cells asegs m7 r [CB (Z.to_nat (Z.min k n)) (firstn (Z.to_nat (Z.min k n)) old); CB (Z.to_nat (n - Z.min k n)) junk]).
  { destruct (Z.eq_dec k 0) as [K0|K1].
    - (* [comment removed for export] *)
      exists (ob ++ firstn (Z.to_nat (n - cl)) (skipn (Z.to_nat cl) uj)). rewrite K0. rewrite Z.min_l by lia. cbn [Z.to_nat firstn]. rewrite Z.sub_0_r.
      pose proof (rw_cells_CB_merge m7 r _ _ _ _ ltac:(apply (proj2 (rw_cells_app m7 r [CB _ _] [CB _ _])); split; [exact DST6| cbn [cells_size Cells.csize Nat.add]; exact JREST])) as M.
      replace (Z.to_nat cl + Z.to_nat (n - cl))%nat with (Z.to_nat n) in M by lia.
      eapply rw_cells_rebytes; [| | | exact M]; cbn; [| rewrite app_nil_r; reflexivity| lia].
      pose proof M as [[Hwf _] _]. cbn in Hwf. split; [reflexivity| tauto].
    - assert (Ecl : Z.min k n = cl) by (subst cl; unfold usz; (lia_on Gk K1)).
      rewrite Ecl. exists (firstn (Z.to_nat (n - cl)) (skipn (Z.to_nat cl) uj)).
      rewrite <- (EO K1). apply (proj2 (rw_cells_app m7 r [CB _ _] [CB _ _])). split; [exact DST6|]. cbn [cells_size Cells.csize Nat.add]. exact JREST. }
  destruct JNK as [junk JNK]. exists junk.
  split; [reflexivity|]. split; [exact MI7|].
  split.
  { release_frame FRR3 ST7 (bv_unsigned sp + -2160). release_frame FRA3 ST7 (bv_unsigned sp + -2144).
    eapply stk_merge; [exact ST7| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2144 + 2144) at 2 by lia.
    apply stk_of_wr_high; [exact WR6| unfold AIMG_HI; lia]. }
  split.
  { eapply rw_cells_same; [exact ERR4|]. intros a Ha. cbn in Ha.
    replace a with (AERRNO + (a - 6148524)) by (unfold AERRNO, ATP; lia). apply ES67. unfold AERRNO, ATP in *. lia. }
  split.
  { eapply cj_pres_trans; [exact CP46|]. eapply cj_pres_weaken; [exact CP67| lia| intros b Hb; right; exact Hb| auto]. }
  split; [exact GM7|]. split; [exact TP7|].
  split; [exact (RTS_intro _ _ _ _ HR7 WF7 HM7 HG7 HF7 HSW7)|]. split; [exact HO7|]. split; [exact HB7|].
  split; [exact Q1|]. split; [rewrite Q2, Elb4; cbn [remove_first]; rewrite RNEQ; reflexivity|]. split; [exact Q3|].
  split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
  split; [exact BO67|]. exact JNK.
Qed.
End RTAIL.


End CeilWrap.
End RTW_m_rtail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_quarantine_iface RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib4 RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_fz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_realloc0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_realloc0.RTW_m_f1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_realloc0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_realloc0.RTW_m_r1.
Import RTW_m_r2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_dcore.
Import RTW_m_rtail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section REALLOC.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis get_thread_stats_proof : get_thread_stats_spec.
Hypothesis set_errno_enomem_proof : set_errno_enomem_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis allocate_ok : allocate_spec.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis quarantine_put_proof : quarantine_put_spec2.

Theorem art_realloc_proof : realloc_lscps_stmt ARTd.
Proof.
  unfold realloc_lscps_stmt. intros until tl. intros HART HINLB OLD LOLD SPB0 ST HCL LO ERR MI TP -> -> Hn COST [RA1 RA2] UWT ROOM.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & (HR & WF & HM & HG & HFR & HSWR) & HO & HBI & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  (nelim HQ 5%nat; intros Qap Qsp Qqp Qqt Qqc).
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. rewrite Esp0 in SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  assert (HIN : In (A, k) (st_lb st)) by (rewrite Elb; exact HINLB).
  assert (HB : In (A, k) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HIN).
  (nelimp (block_geom st WF A k HB) 10%nat; intros Gn GA GK GX GY GCE GL16 GH16 GEA _). unfold usz in GY. unfold KHIGHMEM_BEG, AIMG_HI in GK. olin_all.
  pose proof (block_extra st WF A k HB) as (E8 & _).
  pose proof (alloc_deposit_le_cost n ltac:(lia)) as DEP. unfold cost_realloc, cost_free in COST.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2144) 2144 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  assert (OLDp : True -> bytes_at asegs m A old) by (intros _; exact OLD). clear OLD.
  apply lscps_assume. intros NWX _ _.
  (* [comment removed for export] *)
  (nelimp (set_ia_same st) 18%nat; intros Isp0 Ilb Ilf Itrs It Ictx Iqp Iqt Iqc Iap Isp Isec Iqth Idep Ifs Ipa Isb Ipb).
  set (st1 := set_ia_inited st) in *.
  pose proof (RTWF_ia' st WF) as WF1. pose proof (RTMODEL_ia' st mo HM) as HM1.
  change (set_ia_inited st) with st1 in WF1, HM1.
  pose proof (rt_prov_ia' st) as PV1. change (set_ia_inited st) with st1 in PV1.
  assert (HIN1 : In (A, k) (st_lb st1)) by (rewrite Ilb; exact HIN).
  pose proof (munch_refl [(lo, bv_unsigned sp); (701568, 701568 + 528432); (1285384, 1285384 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  sepM. callxp ltac:(eapply (realloc_r1_spec try_asan_init_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (A := A) (n := n);
              [exact HR| exact WF| exact MI| reflexivity| reflexivity| lia| exact ST| idtac; lia| unfold R1_DEPTH; lia])
         ltac:(unfold r1_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED; change (set_ia_inited st) with st1; clear ST).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2136) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2120) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : RTREP _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR1; rename mx into m1 end.
  change (set_ia_inited st) with st1 in HR1.
  pose proof WM as WM01.
  replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in OBJ1 by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2120 + 8 * zlen (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_REALLOC; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -64 + Z.of_nat 48) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_REALLOC; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  remember (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) as tr eqn:Etr.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
    intros a Ha HC. cbn. split; [| split; [| split; [| exact I]]].
    - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC]. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2120))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2136 + Z.of_nat 12) with (bv_unsigned sp + -2124) in OBc by lia.
  (* [comment removed for export] *)
  assert (HG1 : GWIN st1 m1 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  sepM. callxp ltac:(eapply unwind_ok with (st := st1) (S := bv_unsigned sp + -2136) (pc0 := PC0_REALLOC) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HFR (SWIN_ia' st g HSWR))
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia; exact OBJ1
    | eapply wr_at_weaken; [first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_REALLOC; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Isp0, Esp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Isp0, !Esp0, !It, !unsigned_lit by lia; rewrite <- !Etr; clear PC3 OBJ1; clear ST1).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2136 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2136 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C4 _; C4 _])). split; [exact OBa|]. cbn [cells_size Cells.csize Nat.add].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2136 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2124) by lia. exact OBc. }
  clear SZ2 OBa OBc.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (munch_refl [(st_t st + 2856, st_t st + 2872); (bv_unsigned sp + -2144 - 96, bv_unsigned sp + -2144)] m2) as MU. pose proof (wmono_refl asegs m2) as WM2.
  sepM. callxp ltac:(eapply (realloc_g1_spec get_thread_stats_proof) with (st := st1) (A := A) (n := n) (S := bv_unsigned sp + -2136) (lo := lo);
    [ exact HR2| exact WF1| exact MI2| exact TP| reflexivity| reflexivity| reflexivity| lia| lia| lia| lia
    | rewrite unsigned_lit by lia; exact ST2| idtac; lia| rewrite unsigned_lit by lia; lia ])
    ltac:(unfold AALLOCATE, A_ALLOC; rewrite !It, !unsigned_lit by lia; clear ST2).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR3; rename mx into m3 end.
  match goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
  match goal with H : rw_cells _ m3 (bv_unsigned sp + -2144 - 64) _ |- _ => rename H into FRR3 end.
  match goal with H : rw_cells _ m3 (bv_unsigned sp + -2144 - 16) _ |- _ => rename H into FRA3 end.
  assert (CP23 : cli_pres st (bv_unsigned sp) m2 m3).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM2|]; [unfold CEIL; lia|].
    unfold T_ACACHE, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES03 : errno_same m m3).
  { eapply errno_same_trans; [exact ES02|]. eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (HG3 : GWIN st1 m3 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  assert (WR3 : wr_at asegs m3 (bv_unsigned sp + -2144) 2144) by (first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]).
  clear MU WM2.
  (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof allocate_ok as AL. unfold allocate_spec in AL.
    eapply AL with (lo := lo) (st := st1) (n := n) (S := bv_unsigned sp + -2136) (tr := tr); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR3 WF1 HM1 HG3 HFR (SWIN_ia' st g HSWR)).
    - exact tpx_ok_of_RTWF. - rewrite Iap; exact Qap. - lia. - exact TP.
    - replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia. exact SOBJ.
    - exact (proj1 TRC2).
    - exact TRL. - exact TRR.
    - rewrite unsigned_lit by lia. lia. - rewrite Isp0, Esp0. unfold BST_SIZE. lia.
    - rewrite Itrs, Etrs. exact ROOM.
    - rewrite PV1. lia.
    - rewrite unsigned_lit by lia. exact ST3. - idtac. lia. - rewrite unsigned_lit by lia. unfold AALLOCATE_STACK. lia.
    - rewrite unsigned_lit, Isp0, Esp0 by lia. lia. - exact MI3. }
  cbv beta. intros ms4 mo4 g4 PO.
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 st4 -> MI4 r -> RTS4 ST4 CP34 ES34 GM4 Esp04 Elf4 AS4 RES).
  rewrite unsigned_lit in ST4, CP34 by lia.
  replace (ret_pc (Z_to_bv 64 0x32994)) with (Z_to_bv 64 0x32994) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS4 6%nat; intros HR4 WF4 HM4 HG4 HF4 HSW4). (nelim AS4 5%nat; intros Sap Ssp Sqp Sqt Sqc).
  (* [comment removed for export] *)
  unfold cli_pres in CP34. rewrite Isp0, Ilb, Ilf, Esp0, Elb, Elf in CP34.
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP34) in FRR3; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP34) in FRA3; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP34) in FR1; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP34) in SOBJ; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP34) in TRC2; [| left; rewrite trace_cells_size; lia].
  apply (cj_pres_wr_at _ _ _ _ _ _ _ _ CP34) in WR3; [| left; lia].
  assert (ERR4 : rw_cells asegs m4 6148524 [C4 errv]).
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn in Ha.
    replace a with (AERRNO + (a - 6148524)) by (unfold AERRNO, ATP; lia). apply ES34. lia. }
  assert (CP04 : cj_pres sp0 LB LF (bv_unsigned sp) m m4).
  { unfold cli_pres in *. rewrite Esp0, Elb, Elf in CP01, CP12, CP23.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP12|]. eapply cj_pres_trans; [exact CP23|].
    eapply cj_pres_weaken; [exact CP34| lia| auto| auto]. }
  apply lscps_assume. intros _ HO4 HB4.
  destruct RES as [(-> & Elb4 & Etrs4 & BO4)|(RNZ & ABR & NIN & NFR & Elb4 & TP4 & BO4 & JK)].
  - (* [comment removed for export] *)
    eapply lscps_step_evt. cbv beta delta [wz] in *.
    pose proof (munch_refl [(lo, bv_unsigned sp + -2144); (6148524, 6148524 + 4)] m4) as MU. pose proof (wmono_refl asegs m4) as WM4.
    sepM. callxp ltac:(eapply (realloc_g5_spec set_errno_enomem_proof) with (SP := bv_unsigned sp) (lo := lo) (errv := errv);
      [ exact MI4| exact TP| rewrite unsigned_lit by lia; lia| reflexivity| idtac; lia| lia| lia
      | replace (bv_unsigned sp + -2208) with (bv_unsigned sp + -2144 - 64) by lia; exact ST4
      | exact ERR4
      | replace (bv_unsigned sp + -2208) with (bv_unsigned sp + -2144 - 64) by lia; exact FRR3
      | replace (bv_unsigned sp + -2160) with (bv_unsigned sp + -2144 - 16) by lia; exact FRA3
      | exact FR1 ])
      ltac:(unfold AERRNO, ATP, ENOMEM; change (6148688 - 164) with 6148524; clear ERR4 FRA3 FRR3; clear ST4).
    cbv beta delta [wz] in *. try rewrite Z_to_bv_bv_unsigned.
    match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI5; rename mx into m5 end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : rw_cells _ m5 6148524 _ |- _ => rename H into ERR5 end.
    apply evt_done. apply lscps_done. unfold arealloc_post.
    nexists 15%nat. exists m5, (Z_to_bv 64 ENOMEM), TRS. split; [reflexivity|]. split; [exact MI5|].
    split.
    { eapply stk_merge; [exact ST5| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2144 + 2144) at 2 by lia.
      apply stk_of_wr_high; [| unfold AIMG_HI; lia]. first [exact WR3| eapply wr_at_wmono; [exact WR3| exact WM4]]. }
    split; [exact ERR5|].
    split; [exact GM4|]. split; [right; reflexivity|].
    left. split; [reflexivity|].
    assert (HLB : forall A' k', In (A', k') LB -> AIMG_HI <= A').
    { intros A' k' Hin. rewrite <- Elb in Hin. (nelimp (block_geom st WF A' k' ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 5%nat; intros _ _ G1 G2 _). blia. }
    assert (HLF : forall Fr k', In (Fr, k') LF -> AIMG_HI <= Fr).
    { intros Fr k' Hin. rewrite <- Elf in Hin. (nelimp (frame_range st WF Fr k' Hin) 3%nat; intros _ X _). pose proof (fs_range st WF) as (F1 & _).
      change FS_FRAMES_OFF with 36864 in X. blia. }
    split.
    + assert (ART4 : ARTd sp0 SPB LB LF TRS (B - cost_realloc n) m4 mo4 g4).
      { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
          | rewrite Esp04, Isp0; exact Esp0| rewrite Elb4, Ilb; exact Elb| rewrite Elf4, Ilf; exact Elf| rewrite Etrs4, Itrs; exact Etrs
          | unfold QUIET; rewrite Sap, Ssp, Sqp, Sqt, Sqc, Iap, Isp, Iqp, Iqt, Iqc; repeat split; assumption
          | unfold cost_realloc, cost_free; lia| | exact HSPB| exact HSW4].
        unfold budget_ok, cost_realloc, cost_free in *. lia. }
      eapply artd_frame; [exact ART4| exact MU| exact WM4|].
      constructor; [| constructor; [| constructor]]; unfold cj_write_ok; cbn [fst snd].
      * right. left. idtac. lia.
      * do 3 right. left. unfold AERRNO, ATP. lia.
    + eapply cj_pres_trans; [exact CP04|]. eapply cj_pres_of_munch; [exact MU| exact WM4|].
      intros a Ha HC. cbn. split; [| split; [| exact I]].
      * intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| rewrite Esp0, Elb, Elf; exact HC].
      * intros Hin. apply (errno_not_client sp0 LB LF (bv_unsigned sp) a); [unfold AERRNO, ATP; lia| unfold CEIL; lia| exact HLB| exact HLF| exact HC].
  - (* [comment removed for export] *)
    (nelim JK 3%nat; intros uj JK1 JK2).
    assert (OLD4 : bytes_at asegs m4 A (firstn (Z.to_nat (Z.min k n)) old)).
    { eapply cj_pres_bytes_at; [exact CP04| apply bytes_at_firstn; exact (OLDp I)|].
      do 3 right. left. exists A, k. split; [exact HINLB|]. rewrite length_firstn. lia. }
    replace (bv_unsigned sp + -2144 - 64) with (bv_unsigned sp + -2208) in * by lia.
    replace (bv_unsigned sp + -2144 - 16) with (bv_unsigned sp + -2160) in * by lia.
    eapply lscps_mono.
    { pose proof (realloc_tail_proof depot_put_proof quarantine_put_proof) as RT. unfold realloc_tail_stmt in RT.
      eapply RT with (st4 := st4) (LB1 := st_lb st1) (old := old);
        first [ eassumption
              | exact (RTS_intro _ _ _ _ HR4 WF4 HM4 HG4 HF4 HSW4)
              | rewrite Sqt, Iqt; exact Qqt
              | rewrite Sqc, Iqc; exact Qqc
              | rewrite Sqp, Iqp; exact Qqp
              | rewrite Sap, Iap; exact Qap
              | exact (trs_put_in _ _ _ TP4)
              | replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by lia; exact TRC2
              | rewrite Esp04, Isp0, Esp0; lia
              | idtac; lia
              | unfold budget_ok, alloc_deposit, cost_free, AMALLOC_STACK in *; lia ]. }
    cbv beta. intros ms7 mo7 g7 PO.
    (nelim PO 37%nat; intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m7 st7 junk -> MI7 ST7 ERR7 CP47 GM7 TP7 RTS7 HO7 HB7 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 BO47 CELLS)
.
    (nelim RTS7 6%nat; intros HR7 WF7 HM7 HG7 HF7 HSW7).
    unfold arealloc_post. nexists 15%nat. exists m7, errv, (st_trs st7). split; [reflexivity|]. split; [exact MI7|]. split; [exact ST7|].
    split; [exact ERR7|].
    split; [eapply gmono_trans; [exact GM4| exact GM7]|].
    split; [left; rewrite <- Etrs, <- Itrs; eapply trs_put_twice; [exact TP4| exact TP7]|].
    right. exists r, junk.
    rewrite <- Elb. rewrite (cb_remove_first st A k WF HIN). rewrite Ilb in CP47, Q2, NIN.
    split; [reflexivity|]. split; [exact ABR|]. split; [exact NIN|]. split; [rewrite <- Elf, <- Ilf; exact NFR|].
    split.
    + eapply (ARTd_intro st7); [exact HR7| exact WF7| exact HM7| exact HO7| exact HB7| exact HG7| exact HF7
        | rewrite Q1, Esp04, Isp0; exact Esp0| exact Q2| rewrite Q3, Elf4, Ilf; exact Elf| reflexivity
        | unfold QUIET; rewrite Q4, Q5, Q6, Q7, Q8, Sap, Ssp, Sqp, Iap, Isp, Iqp; repeat split; first [assumption| reflexivity]
        | unfold cost_realloc, cost_free; lia| | exact HSPB| exact HSW7].
      unfold budget_ok, cost_realloc, cost_free, alloc_deposit in *. lia.
    + split; [| exact CELLS].
      eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP04| lia| intros b Hb; rewrite <- Elb; eapply remove_first_In; exact Hb| auto]|].
      rewrite Esp04, Isp0, Esp0, Elf4, Ilf, Elf in CP47. exact CP47.
Qed.
End REALLOC.


End CeilWrap.
