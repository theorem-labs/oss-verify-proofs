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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_z_enew : Z := 0x30cb30.   (* [comment removed for export] *)
Definition SITE_z_edbg : Z := 0x30cb4c.   (* [comment removed for export] *)
Definition SITE_z_eerr : Z := 0x30cb60.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition z_c_post (sp1 : Z) (ra' : Z) (pc' : Z) (gp s0 s1 a0' a1' a2' a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (wz ra') (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc') fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma z_c0_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => z_c_post sp1 SITE_z_enew FZ_ERR_NEW gp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RZT) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold J_RZT, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  unfold z_c_post, SITE_z_enew, FZ_ERR_NEW. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma z_c1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => z_c_post sp1 SITE_z_edbg FZ_ERR_SET_DEBUG gp s0 s1 (wz LIT_FILE) (wz 996) (wz LIT_FUNC) a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_z_enew) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_z_enew, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold z_c_post, SITE_z_edbg, FZ_ERR_SET_DEBUG, LIT_FILE, LIT_FUNC. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma z_c2_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => z_c_post sp1 SITE_z_eerr FZ_ERR_SET_ERROR gp s0 s1 (wz 9) (wz 100) (wz 0) a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_z_edbg) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_z_edbg, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  unfold z_c_post, SITE_z_eerr, FZ_ERR_SET_ERROR. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma z_j_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RELOAD) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_z_eerr) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_z_eerr, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  unfold J_RELOAD. apply evt_done. split; [reflexivity| exact I].
Qed.

Section CRzt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_EN : err_new_rest_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
(* [comment removed for export] *)
Hypothesis GO_file : GOBJ LIT_FILE LIT_FILE_SZ.
Hypothesis GO_func : GOBJ LIT_FUNC LIT_FUNC_SZ.
Hypothesis C_ED : err_set_debug_stmt RT GOBJ libenv errst_live FZ_SITES FZ_CALLS.
Hypothesis C_EE : err_set_error_stmt RT libenv errst_live FZ_SITES FZ_CALLS.
Hypothesis RL : RELOAD_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_post := (pem_post RT libenv errst_live).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Theorem RZT_proof : RZT_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 cj F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6
         ctxv namev nn hBv dBv bn KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
  cbv zeta. intros COM REST REM LRM PFR FFC ON CXA CJL CXC NMA NN BNL NMC NUL MBX MBY. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_WE_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  pose proof (z_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m
                SP0' SPH MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  eapply (pem_call_enew RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live FZ_SITES FZ_CALLS C_EN T en Σ m off crem lrem _ SITE_z_enew
            F fc u0 u1 u2 a0 a1 a2 a3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) u3 u4 u5 u6 c1 COM REST ltac:(clear - REM; unfold C_END in *; lia) ltac:(cbn; tauto) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ1 m1 F1 fc1 v1 y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c1' COM1 LV1 FRS1 PR1 EL1 Hc1.
  pose proof COM1 as (_ & MI1 & _).
  (* [comment removed for export] *)
  pose proof (z_c1_walk (wz SITE_z_enew) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) v1 b1 b2 b3 d4 d5 d6 d7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) y3 y4 y5 y6 F1 fc1 m1 SP0' SPH MI1) as W.
  cl_lift W Hc1 c2 Hc2. destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc2'). clear Hc2 Hc1.
  eapply (pem_call_edbg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_live FZ_SITES FZ_CALLS C_ED T en Σ1 m1 off (crem - 1) lrem _ SITE_z_edbg
            LIT_FILE 21 LIT_FUNC 16 996 pem_file_str pem_func_str F1 fc1 u0 u1 u2 b3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) u3 u4 u5 u6 c2 COM1 EL1
            ltac:(clear - REM; unfold C_END in *; lia) LRM ltac:(cbn; tauto) ltac:(clear; lia) (pem_file_lit GOBJ GO_file) (pem_func_lit GOBJ GO_func)
            Hc2').
  clear Hc2' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ2 m2 F2 fc2 v2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c2' QF QN COM2 LV2 FRS2 PR2 EL2 QFP QNP Hc2.
  pose proof COM2 as (_ & MI2 & _).
  (* [comment removed for export] *)
  pose proof (z_c2_walk (wz SITE_z_edbg) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) v2 e1 e2 e3 e4 e5 e6 e7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) z3 z4 z5 z6 F2 fc2 m2 SP0' SPH MI2) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc3'). clear Hc3 Hc2.
  eapply (pem_call_eerr RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_live FZ_SITES FZ_CALLS C_EE T en Σ2 m2 off (crem - 1 - 2) (lrem - 2) _ [(QN, 16); (QF, 21)] SITE_z_eerr 100
            F2 fc2 u0 u1 u2 e3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) u3 u4 u5 u6 c3 COM2 EL2
            ltac:(intros e [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]) ltac:(clear - REM; unfold C_END in *; lia) ltac:(cbn; tauto) ltac:(clear; lia) Hc3').
  clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ3 m3 F3 fc3 v3 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c3' COM3 LV3 FRS3 PR3 EL3 Hc3.
  pose proof COM3 as (_ & MI3 & _).
  (* [comment removed for export] *)
  assert (LIN : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3, LV2; right; right; rewrite LV1; exact He).
  assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)) m m3).
  { intros a Ha Ho. rewrite FRS2, FRS1 in PR3. rewrite FRS1 in PR2. rewrite LV1 in PR1, PR2.
    rewrite (PR3 a (aclient_mono _ _ _ _ _ _ _ Ha LIN (fun e He => He) (Z.le_refl _)) Ho). rewrite (PR2 a Ha Ho). exact (PR1 a Ha Ho). }
  (* [comment removed for export] *)
  pose proof (z_j_walk (wz SITE_z_eerr) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en)) v3 g1 g2 g3 g4 g5 g6 g7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) w3 w4 w5 w6 F3 fc3 m3 MI3) as W.
  cl_lift W Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ3 _ _ c4 Hc4) as (ms4 & (-> & _) & Hc4'). clear Hc4 Hc3.
  (* [comment removed for export] *)
  assert (HP : Permutation ((QN, 16) :: (QF, 21) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])
                           ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (ctxv, ECTX)) ++ opt_ent (Some (namev, nn))) ++ [(QN, 16); (QF, 21)] ++ [])).
  { rewrite app_nil_r. cbn [opt_ent app]. apply Permutation_cons_app. apply Permutation_cons_app. rewrite app_nil_r.
    apply Permutation_app_head. apply Permutation_app_head. apply perm_swap. }
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ3 m3 off _ _ _ _ COM3 HP) as COM4.
  pose proof COM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CFR3 & _).
  refine (RL en Σ3 m3 off (crem - 1 - 2 - 2) (lrem - 2) [(QN, 16); (QF, 21)] [] j0 lH (loc_F RT en) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 eH eD (wz SITE_z_eerr) w0 w1 w2 v3 g1 g2 g3 g4 g5 g6 g7
            s2 s4 s6 w3 w4 w5 w6 (Some (ctxv, ECTX)) (Some (namev, nn)) ctxv namev nn hBv dBv 0 KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY
            COM4 _ ltac:(clear - REM; unfold C_END in *; lia) _ _ eq_refl _ _ _ _ _ T c4 Hc4' Hk).
  - split; [right; exists 1, 0; split; [exact EL3| cbn; clear; lia]|].
    split; [apply Forall_cons; [cbn; clear; lia| apply Forall_cons; [cbn; clear; lia| apply Forall_nil]]|].
    split; [intros e He; rewrite LV3, LV2; destruct He as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]|].
    intros e He. apply CFR3. destruct He as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity].
  - exact (pem_frame_keep RT en m m3 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR PR PD TOP HWS).
  - exact (ff_keep m m3 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  - cbv iota beta. split; [reflexivity|]. split; [clear - NN; lia|].
    pose proof (rw_cells_bound asegs m namev _ NMC) as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2. apply rw_cells_CB0; [exact NB1| clear - NB2; lia].
  - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; [| apply LIN]; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => H0) e x ltac:(apply in_or_app; left; exact He) Hx).
  - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; [| apply LIN]; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => H0) e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) Hx).
  - destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m3 off crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m3 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    left. split; [reflexivity|]. split; [reflexivity|]. split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|].
    split; [apply G8; [cbn; tauto| exact O3]|]. exists (wz 0). apply G8; [cbn; tauto| exact O4].
  - cbn. clear - OFF. lia.
Qed.
End CRzt.
