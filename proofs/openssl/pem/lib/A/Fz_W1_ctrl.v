(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_ukit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Export Fz_W1_pploc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_ctrl_sync : Z := 0x3049d4.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctrl_frame (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition ci_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' v a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma ci_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R fl : Z) (iw shw rrw numw padw rlw rdw rmaxw rflw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R [C8 rlw; C8 rdw; C8 rmaxw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  mem_inv asegs m ->
  evt asegs (ci_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc rlw lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 3) a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI.
  unfold e_mem_ctrl, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia). assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  zstep. zstep. do 3 zstep. zstep. th_if_lit.                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.  (* [comment removed for export] *)
  zstep. rewrite (zx32_small fl) by lia. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite FL512. zstep. zstep. zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep.                                                       (* [comment removed for export] *)
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.                                                       (* [comment removed for export] *)
  zstep. do 3 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. th_if_lit.
  zstep. zstep. zstep.
  do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ci_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition cp_s0_post (sp gp tp a2 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (BI BB BM R PP fl lo : Z) (rlw rdw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) rlw (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880))
                 sp a2 (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (BM + 8))
                 (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000)
                 s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) rdw (Z_to_bv 64 127) t6)
            F (Z_to_bv 64 e_mem_buf_sync) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (CB 8 j :: ctrl_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80).

Lemma cp_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R PP fl : Z) (iw shw rrw numw padw rlw rdw rmaxw rflw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R [C8 rlw; C8 rdw; C8 rmaxw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  0 < PP < 2^64 -> mem_inv asegs m ->
  evt asegs (cp_s0_post sp gp (Z_to_bv 64 0xba3ef0) a2 s8 s9 s10 s11 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BI BB BM R PP fl lo rlw rdw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 115) a2 (Z_to_bv 64 PP) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO HPP MI.
  unfold e_mem_ctrl, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia). assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (zx32_small fl) by lia. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite FL512. zstep. zstep. zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit. zstep. zstep. th_if_lit.
  zstep. zstep. if_cases Kp; zify_cond Kp; try (exfalso; rewrite ?unsigned_lit in Kp by lia; lia). try clear Kp.
  zstep. th_if_lit.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold cp_s0_post, SITE_ctrl_sync, e_mem_buf_sync, ctrl_frame. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition cp_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BM PP lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(PP, PP + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)].

Lemma cp_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6 (s1x s4x s6x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BB BM R PP : Z) (oldpp : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: ctrl_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo -> 0 <= BM < 2^64 ->
  rw_cells asegs m PP [C8 oldpp] -> acc asegs m PP 8 -> PP mod 8 = 0 -> 0 < PP -> (PP + 8 <= IMG_UT_LO \/ IMG_UT_HI <= PP) -> PP + 8 <= 2^47 -> (PP + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= PP) ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> mem_inv asegs m ->
  evt asegs (cp_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc BM PP lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 BB) (Z_to_bv 64 PP) s4x (Z_to_bv 64 1) s6x (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ctrl_sync) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT FR BBC ACCBB BB0 BBAL BBHI BBLO HBM PPC ACCPP PPAL PP0 PPUT PPHI PPSH PPSEP MI.
  unfold SITE_ctrl_sync, ctrl_frame, IMG_UT_LO, IMG_UT_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(PP, PP + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(PP, PP + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(PP, PP + 8)]) by sh_fp_lia.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -80)) = SP + -80) by (apply unsigned_lit; lia).
  do 3 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep.
  zstep. do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold cp_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CCtrl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.

(* [comment removed for export] *)
Definition ctrl_info_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len off fl : Z) (iw shw rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 3 -> a3 = Z_to_bv 64 0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (len - off)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).

Theorem ctrl_info_cps : ctrl_info_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len off fl iw shw rrw numw padw rmaxw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL INR RAL RC ART0 MI0 CALL.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - LOR; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  unfold readp_cells in RC.
  pose proof (ci_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw shw rrw numw padw _ _ rmaxw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
  fold usp in MU1, ST1. exists m1. split; [do 16 eexists; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Hx); lia.
Qed.

(* [comment removed for export] *)

Definition CP_W (BM R D max PP : Z) : list (Z * Z) := [(PP, PP + 8); (BM, BM + 8); (R + 8, R + 16); (D, D + max)].

(* [comment removed for export] *)
Definition ctrl_ptr_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl iw PP : Z) (shw rrw numw padw rmaxw flw oldpp : word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> 0 < max < 2 ^ 31 -> length junk = Z.to_nat max -> rw_cells asegs m D [CB (Z.to_nat max) junk] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (CP_W BM R D max PP) m m'
        /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw) /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw' flw)
        /\ rw_cells asegs m' D [CB (Z.to_nat max) (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))]
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)])).

Theorem ctrl_ptr_cps : ctrl_ptr_stmt.
Proof.
  pose proof (mem_buf_sync_cps RT AF GOBJ AFP MMV) as C_SY.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl iw PP shw rrw numw padw rmaxw flw oldpp junk
    FDO MST -> -> -> -> INBI BIAL BW FLOK HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBB NDBM NDR HOFF HLEN HMAX LJ DC PPAL PPC LOC ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  pose proof (live_ne_apart RT AF Σ m BB 16 BM 32 ART0 INBB INBM ltac:(intros E; injection E; lia)) as APBM.
  pose proof (live_ne_apart RT AF Σ m BB 16 R 32 ART0 INBB INR ltac:(intros E; injection E; lia)) as APBR.
  pose proof (live_ne_apart RT AF Σ m D max BB 16 ART0 IND INBB ltac:(intros E; injection E; intros _; exact NDBB)) as APDB.
  destruct (pp_facts RT AF Σ m usp lo PP ART0 LOC PPAL LOW LOR SPT) as (PP0 & PPHI & PPUT & PPSH & PPSEP & PPA & PPAP & PPACC).
  pose proof (PPAP BM 32 INBM) as APPM. pose proof (PPAP R 32 INR) as APPR. pose proof (PPAP D max IND) as APPD. pose proof (PPAP BB 16 INBB) as APPB.
  (* [comment removed for export] *)
  unfold readp_cells in RC.
  pose proof (cp_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R PP fl (Z_to_bv 64 iw) shw rrw numw padw _ _ rmaxw flw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO
                ltac:(clear - PP0 PPHI; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x) by (intros x Hx; apply PR1; [exact Hx | exact I]).
  assert (AGL : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 5. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max flw)).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw flw)).
  { unfold readp_cells. apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]. }
  assert (DC1 : rw_cells asegs m1 D [CB (Z.to_nat max) junk]).
  { apply (rw_cells_agree asegs m m1 _ _ DC); [apply AGL; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact DLO | exact WM1]. }
  assert (PPC1 : rw_cells asegs m1 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m m1 _ _ PPC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  (* [comment removed for export] *)
  apply (C_SY Σ PMc (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) (Z_to_bv 64 (len - off))
           (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880)) sp a2 (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (BM + 8))
           (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000)
           s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) (Z_to_bv 64 (D + off)) (Z_to_bv 64 127) t6 F fc m1 lo BI 128 BB BM R D len max off fl iw shw rrw numw padw rmaxw flw junk
           FDO MST eq_refl eq_refl INBI ltac:(clear; lia) BIAL BW1 HIW INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 NMR IND NDBB NDBM NDR HOFF HLEN HMAX LJ DC1 ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c1 Hc1').
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v2 & rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BMC2 & RC2 & DC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ctrl_sync) in Hc2' by (unfold SITE_ctrl_sync; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> outside (SY_W BM R D max) (bv_unsigned x) -> m2 x = m1 x)
    by (intros x Hx Ho; exact (PRES2 x Hx Ho)).
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m1 m2 _ _ BBC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | unfold SY_W; cbn [outside]; clear - Hx APBM APBR APDB; lia]. }
  assert (PPC2 : rw_cells asegs m2 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m1 m2 _ _ PPC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [| unfold SY_W; cbn [outside]; clear - Hx APPM APPR APPD; lia].
    apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [| auto | auto | unfold usp1; clear; lia].
    replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold ctrl_frame in Hx. cbn [cells_size csize Nat.add length] in Hx.
    apply P2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold SY_W; cbn [outside]; unfold usp1 in *; clear - Hx BMLO RLO DLO HLO1; lia]. }
  assert (ACC2 : acc asegs m2 PP 8).
  { apply (PPACC m2 ART2). intros a (f & k & Hin & Hs1 & Hs2).
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f k ART0 Hin)) as FSA.
    pose proof (FSA BM 32 INBM) as X1. pose proof (FSA R 32 INR) as X2. pose proof (FSA D max IND) as X3.
    assert (HS : bv_unsigned a < 0x10007fff8000).
    { pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & FH & _). unfold shad in Hs2.
      assert ((f + fs_size k) / 8 <= 2 ^ 44 - 1) by (clear - FH SP0R; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia). unfold SHB in Hs2. clear - H Hs2. lia. }
    rewrite (P2 a ltac:(do 4 right; exists f, k; split; [exact Hin | split; [exact Hs1 | exact Hs2]]) ltac:(unfold SY_W; cbn [outside]; clear - Hs1 Hs2 X1 X2 X3; lia)).
    apply MU1. cbn [outside]. split; [| exact I]. clear - HS NUM HLO1. lia. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (cp_s1_walk ra (Z_to_bv 64 SITE_ctrl_sync) sp gp y0 y1 y2 v2 h1 h2 h3 h4 h5 h6 h7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 a2 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) F2 fc2 m2 lo BB BM R PP oldpp j
                HLO1 HLOS SPH ST2 UT2 FR2 BBC2 (proj2 (af_acc_live RT AF Σ m2 BB 16 ART2 INBB)) BB0 BBAL BBHI BBLO ltac:(clear - BM0 BMLO HLO1 SPH; lia)
                PPC2 ACC2 PPAL PP0 PPUT PPHI PPSH ltac:(fold usp; exact PPSEP) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & PPC3).
  fold usp in ST3. exists rmaxw2, m3. split; [do 16 eexists; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin. apply Hx.
    apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [| auto | auto | unfold usp1; clear; lia].
    replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hin. lia. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  assert (E3 : forall x : word, outside [(PP, PP + 8)] (bv_unsigned x) -> m3 x = m2 x) by (intros x Hx; exact (MU3 x Hx)).
  split.
  { intros x Hx Ho. unfold CP_W in Ho. cbn [outside] in Ho.
    rewrite (E3 x ltac:(cbn [outside]; clear - Ho; lia)). rewrite (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(unfold SY_W; cbn [outside]; clear - Ho; lia)).
    exact (P1 x Hx). }
  split.
  { apply (rw_cells_agree asegs m2 m3 _ _ BMC2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply E3. cbn [outside]. clear - Hx APPM. lia. }
  split.
  { apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply E3. cbn [outside]. clear - Hx APPR. lia. }
  split; [| exact PPC3].
  apply (rw_cells_agree asegs m2 m3 _ _ DC2); [| exact WM3]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia.
  apply E3. cbn [outside]. clear - Hx APPD. lia.
Qed.

(* [comment removed for export] *)
Definition ctrl_ptr_same_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R fl iw PP : Z) (shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PP, PP + 8)] m m'
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)])).

Theorem ctrl_ptr_same_cps : ctrl_ptr_same_stmt.
Proof.
  pose proof (mem_buf_sync_same_cps RT AF GOBJ AFP) as C_SS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw PP shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp
    FDO MST -> -> -> -> INBI BIAL BW FLOK HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC PPAL PPC LOC ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  destruct (pp_facts RT AF Σ m usp lo PP ART0 LOC PPAL LOW LOR SPT) as (PP0 & PPHI & PPUT & PPSH & PPSEP & PPA & PPAP & PPACC).
  pose proof (PPAP BM 32 INBM) as APPM. pose proof (PPAP R 32 INR) as APPR. pose proof (PPAP BB 16 INBB) as APPB.
  (* [comment removed for export] *)
  pose proof (cp_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R PP fl (Z_to_bv 64 iw) shw rrw numw padw rlw dw rmw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO
                ltac:(clear - PP0 PPHI; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x) by (intros x Hx; apply PR1; [exact Hx | exact I]).
  assert (AGL : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 5. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM [C8 lw; C8 dw; C8 mw; C8 flw]).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R [C8 rlw; C8 dw; C8 rmw; C8 rflw]).
  { apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]. }
  assert (PPC1 : rw_cells asegs m1 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m m1 _ _ PPC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  (* [comment removed for export] *)
  apply (C_SS Σ PMc (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) rlw
           (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880)) sp a2 (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (BM + 8))
           (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000)
           s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) dw (Z_to_bv 64 127) t6 F fc m1 lo BI 128 BB BM R fl iw shw rrw numw padw lw dw mw flw rlw rmw rflw
           FDO MST eq_refl eq_refl INBI ltac:(clear; lia) BIAL BW1 HIW INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c1 Hc1').
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ctrl_sync) in Hc2' by (unfold SITE_ctrl_sync; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx; exact (PRES2 x Hx)).
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m1 m2 _ _ BBC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2. apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia]. }
  assert (PPC2 : rw_cells asegs m2 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m1 m2 _ _ PPC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2. apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [| auto | auto | unfold usp1; clear; lia].
    replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold ctrl_frame in Hx. cbn [cells_size csize Nat.add length] in Hx.
    apply P2. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (ACC2 : acc asegs m2 PP 8).
  { apply (PPACC m2 ART2). intros a (f & k & Hin & Hs1 & Hs2).
    assert (HS : bv_unsigned a < 0x10007fff8000).
    { pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & FH & _). unfold shad in Hs2.
      assert ((f + fs_size k) / 8 <= 2 ^ 44 - 1) by (clear - FH SP0R; unfold USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia). unfold SHB in Hs2. clear - H Hs2. lia. }
    rewrite (P2 a ltac:(do 4 right; exists f, k; split; [exact Hin | split; [exact Hs1 | exact Hs2]])).
    apply MU1. cbn [outside]. split; [| exact I]. clear - HS NUM HLO1. lia. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (cp_s1_walk ra (Z_to_bv 64 SITE_ctrl_sync) sp gp y0 y1 y2 v2 h1 h2 h3 h4 h5 h6 h7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 a2 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) F2 fc2 m2 lo BB BM R PP oldpp j
                HLO1 HLOS SPH ST2 UT2 FR2 BBC2 (proj2 (af_acc_live RT AF Σ m2 BB 16 ART2 INBB)) BB0 BBAL BBHI BBLO ltac:(clear - BM0 BMLO HLO1 SPH; lia)
                PPC2 ACC2 PPAL PP0 PPUT PPHI PPSH ltac:(fold usp; exact PPSEP) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & PPC3).
  fold usp in ST3. exists m3. split; [do 16 eexists; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin. apply Hx.
    apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [| auto | auto | unfold usp1; clear; lia].
    replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hin. lia. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split; [| exact PPC3].
  intros x Hx Ho. rewrite (MU3 x Ho). rewrite (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia])). exact (P1 x Hx).
Qed.
End CCtrl.
