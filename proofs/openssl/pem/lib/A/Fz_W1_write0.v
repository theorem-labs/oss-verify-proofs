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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs Fz_W1_write Fz_W1_writec Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition wr_z_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (BI BB fl lo : Z) (rrw numw padw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)).

Lemma wr_z_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB fl : Z) (rrw numw padw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))] ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> mem_inv asegs m ->
  evt asegs (wr_z_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 F fc BI BB fl lo rrw numw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_write) fc None m (seg_rom asegs)).
Proof.
  intros until padw. intros HLO HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO MI.
  unfold e_mem_write, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 10 zstep. zstep.
  zstep. zstep. zstep. zstep.
  do 5 zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.
  zstep. cbv beta. rewrite (Z_to_bv_unsigned 8 (fl ≫ 8)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  zstep. rewrite (fl_rdonly_byte fl) by lia. zstep. th_if_lit.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -80). zstep. try th_ret_lit.
  (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; lia). try clear Kb.
  zstep. zstep. do 10 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_z_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CWz.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.

Definition WRZ_W (BI : Z) : list (Z * Z) := [(BI + 48, BI + 52)].

(* [comment removed for export] *)
Definition write_zero_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB fl : Z) (rrw numw padw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a2 = Z_to_bv 64 0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_write m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (WRZ_W BI) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)))).

Theorem write_zero_cps : write_zero_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB fl rrw numw padw
    FDO MST -> -> -> INBI BIAL BW FLOK ART0 MI0 CALL.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - LOR; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (bio_flags_byte1 m BI _ _ fl rrw numw padw _ ltac:(destruct FLOK; lia) BW) as FB1.
  (* [comment removed for export] *)
  pose proof (wr_z_walk ra sp gp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB fl rrw numw padw
                HLO1 HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & BW1).
  fold usp in MU1, ST1. exists m1. split; [do 16 eexists; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 96) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx;
      [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  split; [| exact BW1].
  intros x Hx Ho. apply MU1. unfold WRZ_W in Ho. cbn [outside] in Ho |- *. split; [clear - Ho; lia | split; [| exact I]].
  destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia.
Qed.
End CWz.
