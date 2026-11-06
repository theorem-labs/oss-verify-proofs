(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_mutex Fz_T_lock Fz_I3_gdcw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition e_fxi : Z := 0x1f39c0.      (* [comment removed for export] *)
Definition e_fxi_ex : Z := 0x1f36f0.   (* [comment removed for export] *)
Definition e_gx : Z := 0x1f2e74.       (* [comment removed for export] *)
Definition e_gal : Z := 0x1f387c.      (* [comment removed for export] *)
Definition SITE_fx_gx : Z := 0x1f372c. Definition SITE_gx_gdc : Z := 0x1f2e8c. Definition SITE_fx_gal : Z := 0x1f3740. Definition SITE_fx_unlock : Z := 0x1f3824.
Definition SITE_gal_lock : Z := 0x1f391c.
(* [comment removed for export] *)
Definition GSH_GLOBAL : Z := 2149000113.

(* [comment removed for export] *)
Definition fxi_w0_post (sp gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s2e s3e s4e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_gx_gdc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) s1 (Z_to_bv 64 0) (Z_to_bv 64 g_shadow_memory_dynamic_address)
                 (Z_to_bv 64 (-1)) a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_gdc) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 sp; C8 (Z_to_bv 64 SITE_fx_gx)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4e; C8 s3e; C8 s2e; C8 s1; C8 s0e; C8 rae]
    /\ stk bsegs m' lo (bv_unsigned sp + -80).

Lemma fxi_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> mem_inv bsegs m ->
  evt bsegs (fxi_w0_post sp gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s2 s3 s4 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_fxi) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST HLOS HLO SPH UT SHC MI. unfold e_fxi. unfold g_shadow_memory_dynamic_address, SHB in SHC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia.
  carve_frame 16%nat ST.
  do 10 zstep.
  release_frame FR ST SP.
  zstep.
  carve_frame 64%nat ST.
  do 15 zstep.
  lazymatch goal with FRH : rw_cells bsegs ?mm (SP + -64) (CB 8 ?jj :: ?rest) |- _ => set (j8 := jj) in FRH end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths. ths. if_false. ths.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. rewrite ?Z_to_bv_bv_unsigned in FR0.
  unfold fxi_w0_post, SITE_gx_gdc, SITE_fx_gx, e_gdc, g_shadow_memory_dynamic_address, SHB. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR0|]. split; [exact FR| assumption].
Qed.

(* [comment removed for export] *)
Definition fxi_w1_post (sp gp tp t0 t1 t2 s1 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s2e s3e s4e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo lk : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
    ms = MS (mkR rae sp gp tp t0 t1 t2 s0e s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6 a7 s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc rae) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (lk + 4, lk + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' lk (mutex_cells z64 z64) /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fxi_w1 : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s2e s3e s4e : word)
    (F : bvmap 5 word) fc (m : mem) (lo lk : Z) (j8 : list byte),
  stk bsegs m lo (bv_unsigned sp + -80) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 176 -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 sp; C8 (Z_to_bv 64 SITE_fx_gx)] ->
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4e; C8 s3e; C8 s2e; C8 s1; C8 s0e; C8 rae] ->
  ro_cells bsegs m GSH_GLOBAL [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xbd1d88 [C8 (Z_to_bv 64 lk)] -> rw_cells bsegs m lk (mutex_cells z64 z64) ->
  0x10007fff8000 <= lk -> lk + 40 <= lo -> lk mod 16 = 0 ->
  mem_inv bsegs m ->
  evt bsegs (fxi_w1_post sp gp tp t0 t1 t2 s1 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae s0e s2e s3e s4e F fc lo lk m)
    (MS (mkR (Z_to_bv 64 SITE_gx_gdc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) s1 (Z_to_bv 64 0xbd1d80) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gx_gdc) fc None m (seg_rom bsegs)).
Proof.
  intros until j8. intros ST HLOS HLO SPH UT SHC FR0 FR GB LKP MC LKH LKLO LK16 MI. unfold SITE_gx_gdc, SITE_fx_gx, GSH_GLOBAL in *. unfold g_shadow_memory_dynamic_address, SHB in *.
  unfold mutex_cells in MC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 176, SP); (lk + 4, lk + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(SP - 176, SP); (lk + 4, lk + 8)]) by ut_fp_lia.
  assert (EUl : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  ths. th_if_lit. ths. ths. th_if_lit. ths.
  ths. ths. release_frame FR0 ST (SP + -64). ths. ths.
  ths. if_false. do 4 ths.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => th_frame 32%nat [8; 8; 8; 8]%nat H end. do 5 ths.
  do 3 ths. ths. if_true.
  ths. ths. ths. th_if_lit.
  do 5 ths. ths. ths. if_false. ths. ths. if_false. ths. if_true. ths.
  tcall (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | lia | left; lia].
  cbv beta delta [mkR]. unfold mutex_cells in *.
  ths. if_false. do 3 ths. ths. th_if_lit. ths. ths.
  do 4 ths. release_frame FR0 PC (SP + -64). ths. ths.
  ths. if_false. ths. if_true.
  ths. ths. ths. th_if_lit.
  do 3 ths. ths. if_false. ths. ths.
  tcall (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | lia | left; lia].
  cbv beta delta [mkR]. unfold mutex_cells in *.
  ths. do 7 ths. release_frame FR PC SP. ths. ths.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold fxi_w1_post. apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [unfold mutex_cells; eassumption | assumption].
Qed.
