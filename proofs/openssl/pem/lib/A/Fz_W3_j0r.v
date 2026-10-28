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
Definition SITE_r0_enew : Z := 0x30c228.   (* [comment removed for export] *)
Definition SITE_r0_edbg : Z := 0x30c244.   (* [comment removed for export] *)
Definition SITE_r0_eerr : Z := 0x30c25c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition r0_c_post (sp1 : Z) (ra' : Z) (pc' : Z) (gp s0 s1 a0' a1' a2' a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (wz ra') (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc') fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma r0_c0_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => r0_c_post sp1 SITE_r0_enew FZ_ERR_NEW gp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold J_RAISE0, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  unfold r0_c_post, SITE_r0_enew, FZ_ERR_NEW. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma r0_c1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => r0_c_post sp1 SITE_r0_edbg FZ_ERR_SET_DEBUG gp s0 s1 (wz LIT_FILE) (wz 955) (wz LIT_FUNC) a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_r0_enew) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_r0_enew, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold r0_c_post, SITE_r0_edbg, FZ_ERR_SET_DEBUG, LIT_FILE, LIT_FUNC. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma r0_c2_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => r0_c_post sp1 SITE_r0_eerr FZ_ERR_SET_ERROR gp s0 s1 (wz 9) (wz 0x80106) (wz 0) a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_r0_edbg) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_r0_edbg, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold r0_c_post, SITE_r0_eerr, FZ_ERR_SET_ERROR. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma r0_j_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz 0) s4 s5 s6 (wz 0) s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_END1) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_r0_eerr) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_r0_eerr, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  unfold J_END1. apply evt_done. split; [reflexivity| exact I].
Qed.

Local Ltac fix_addr sp1 K := lazymatch goal with |- rw_cells _ _ ?a _ /\ _ => replace a with (sp1 + K) by lia | |- rw_cells _ _ ?a _ => replace a with (sp1 + K) by lia end.
Lemma rw_cells_blur_all0 : forall (m : word -> option byte) A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_blur m A cs []). rewrite app_nil_r. exact H. Qed.
(* [comment removed for export] *)
Lemma frame0_blob : forall RT (en : pem_entry RT) (m : word -> option byte) j0 lH lF endv lE x1 x2 gap,
  rw_cells asegs m (e_sp1 RT en) [CB 24 j0] -> rw_cells asegs m (e_sp1 RT en + 24) lH -> Z.of_nat (cells_size lH) = 56 ->
  rw_cells asegs m (e_sp1 RT en + 80) lF -> Z.of_nat (cells_size lF) = 24 -> rw_cells asegs m (e_sp1 RT en + 104) [C8 endv] ->
  rw_cells asegs m (e_sp1 RT en + 112) lE -> Z.of_nat (cells_size lE) = 104 -> rw_cells asegs m (e_sp1 RT en + 216) [C8 (Z_to_bv 64 (e_BI RT en))] ->
  rw_cells asegs m (e_sp1 RT en + 224) [C8 x1; C8 x2; C8 (Z_to_bv 64 (e_f RT en))] -> rw_cells asegs m (e_sp1 RT en + 248) [CB (Z.to_nat (e_pd RT en)) gap] ->
  (e_pd RT en = 0 \/ e_pd RT en = 16) ->
  exists nj jj, rw_cells asegs m (e_sp1 RT en) [CB nj jj] /\ Z.of_nat nj = 248 + e_pd RT en.
Proof.
  intros RT en m j0 lH lF endv lE x1 x2 gap FR0 FRH SZH FRF SZF FR104 FRE SZE FRB FR224 FRG PD.
  set (sp1 := e_sp1 RT en) in *.
  assert (FRA : rw_cells asegs m sp1 ([CB 24 j0] ++ lH ++ lF ++ [C8 endv] ++ lE ++ [C8 (Z_to_bv 64 (e_BI RT en))] ++ [C8 x1; C8 x2; C8 (Z_to_bv 64 (e_f RT en))] ++ [CB (Z.to_nat (e_pd RT en)) gap])).
  { apply (proj2 (rw_cells_app _ sp1 _ _)). split; [exact FR0|]. cbn [cells_size csize Nat.add]. fix_addr sp1 24.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRH|]. rewrite <- (Nat2Z.id (cells_size lH)), SZH. fix_addr sp1 80.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRF|]. rewrite <- (Nat2Z.id (cells_size lF)), SZF. fix_addr sp1 104.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR104|]. cbn [cells_size csize Nat.add]. fix_addr sp1 112.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRE|]. rewrite <- (Nat2Z.id (cells_size lE)), SZE. fix_addr sp1 216.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRB|]. cbn [cells_size csize Nat.add]. fix_addr sp1 224.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR224|]. cbn [cells_size csize Nat.add]. fix_addr sp1 248. exact FRG. }
  apply rw_cells_blur_all0 in FRA. do 2 eexists. split; [exact FRA|].
  rewrite ?cells_size_app, ?Nat2Z.inj_add, SZH, SZF, SZE. cbn [cells_size csize Nat.add]. lia.
Qed.

Section CJ0r.
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
Hypothesis EN0 : END0_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
Local Notation pem_post := (pem_post RT libenv errst_live).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Theorem RAISE0_proof : RAISE0_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s10 s11 t3 t4 t5 t6 lE.
  cbv zeta. intros COM REST REM LRM FR0 FRH SZH FRF SZF FR104 FRE SZE FRB FR224 FRG FFC ON. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m _ crem lrem _ COM) as [ELV CLV].
  pose proof (com_WE_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m _ crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  destruct (frame0_blob RT en m j0 lH lF endv lE x1 x2 gap FR0 FRH SZH FRF SZF FR104 FRE SZE FRB FR224 FRG PD) as (nj & jj & FBL & NJ).
  (* [comment removed for export] *)
  pose proof (r0_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5
                (wz (e_f RT en)) s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m SP0' SPH MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  eapply (pem_call_enew RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live FZ_SITES FZ_CALLS C_EN T en Σ m _ crem lrem _ SITE_r0_enew
            F fc u0 u1 u2 a0 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5 (wz (e_f RT en)) s7 s10 s11 u3 u4 u5 u6 c1
            COM REST ltac:(clear - REM; unfold C_END in *; lia) ltac:(cbn; tauto) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ1 m1 F1 fc1 v1 y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c1' COM1 LV1 FRS1 PR1 EL1 Hc1.
  pose proof COM1 as (_ & MI1 & _).
  (* [comment removed for export] *)
  pose proof (r0_c1_walk (wz SITE_r0_enew) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) v1 b1 b2 b3 d4 d5 d6 d7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5
                (wz (e_f RT en)) s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 y3 y4 y5 y6 F1 fc1 m1 SP0' SPH MI1) as W.
  cl_lift W Hc1 c2 Hc2. destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc2'). clear Hc2 Hc1.
  eapply (pem_call_edbg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_live FZ_SITES FZ_CALLS C_ED T en Σ1 m1 _ (crem - 1) lrem _ SITE_r0_edbg
            LIT_FILE 21 LIT_FUNC 16 955 pem_file_str pem_func_str F1 fc1 u0 u1 u2 b3 b4 b5 b6 b7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5 (wz (e_f RT en)) s7
            s10 s11 u3 u4 u5 u6 c2 COM1 EL1
            ltac:(clear - REM; unfold C_END in *; lia) LRM ltac:(cbn; tauto) ltac:(clear; lia) (pem_file_lit GOBJ GO_file) (pem_func_lit GOBJ GO_func)
            Hc2').
  clear Hc2' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ2 m2 F2 fc2 v2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c2' QF QN COM2 LV2 FRS2 PR2 EL2 QFP QNP Hc2.
  pose proof COM2 as (_ & MI2 & _).
  (* [comment removed for export] *)
  pose proof (r0_c2_walk (wz SITE_r0_edbg) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) v2 e1 e2 e3 e4 e5 e6 e7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5
                (wz (e_f RT en)) s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 z3 z4 z5 z6 F2 fc2 m2 SP0' SPH MI2) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc3'). clear Hc3 Hc2.
  eapply (pem_call_eerr RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_live FZ_SITES FZ_CALLS C_EE T en Σ2 m2 _ (crem - 1 - 2) (lrem - 2) _ [(QN, 16); (QF, 21)] SITE_r0_eerr 0x80106
            F2 fc2 u0 u1 u2 e3 b4 b5 b6 b7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5 (wz (e_f RT en)) s7 s10 s11 u3 u4 u5 u6 c3 COM2 EL2
            ltac:(intros e [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]) ltac:(clear - REM; unfold C_END in *; lia) ltac:(cbn; tauto) ltac:(clear; lia) Hc3').
  clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ3 m3 F3 fc3 v3 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c3' COM3 LV3 FRS3 PR3 EL3 Hc3.
  pose proof COM3 as (_ & MI3 & _).
  (* [comment removed for export] *)
  assert (LIN : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3, LV2; right; right; rewrite LV1; exact He).
  assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)) m m3).
  { intros a Ha Ho. rewrite FRS2, FRS1 in PR3. rewrite FRS1 in PR2. rewrite LV1 in PR1, PR2.
    rewrite (PR3 a (aclient_mono _ _ _ _ _ _ _ Ha LIN (fun e He => He) (Z.le_refl _)) Ho). rewrite (PR2 a Ha Ho). exact (PR1 a Ha Ho). }
  (* [comment removed for export] *)
  pose proof (r0_j_walk (wz SITE_r0_eerr) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en)) v3 g1 g2 g3 g4 g5 g6 g7 (wz (e_f RT en)) s3 (wz (e_flags RT en)) s5
                (wz (e_f RT en)) s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 w3 w4 w5 w6 F3 fc3 m3 MI3) as W.
  cl_lift W Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ3 _ _ c4 Hc4) as (ms4 & (-> & _) & Hc4'). clear Hc4 Hc3.
  pose proof COM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CFR3 & _).
  refine (EN0 en Σ3 m3 _ (crem - 1 - 2 - 2) (lrem - 2) [(QN, 16); (QF, 21)] nj jj hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_r0_eerr) w0 w1 w2 v3 g1 g2 g3 g4 g5 g6 g7
            s5 s10 s11 w3 w4 w5 w6 COM3 _ ltac:(clear - REM; unfold C_END in *; lia) _ NJ _ _ T c4 Hc4' Hk).
  - split; [right; exists 1, 0; split; [exact EL3| cbn; clear; lia]|].
    split; [apply Forall_cons; [cbn; clear; lia| apply Forall_cons; [cbn; clear; lia| apply Forall_nil]]|].
    split; [intros e He; rewrite LV3, LV2; destruct He as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]|].
    intros e He. apply CFR3. exact He.
  - eapply stack_keep; [exact FBL| exact PR| clear; lia| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, NJ; clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia|].
    intros x Hx. apply HWS. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, NJ in Hx. clear - Hx TOP PD. unfold e_sp1, USTACK_TOP in *. lia.
  - exact (ff_keep m m3 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  - destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m3 _ crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m3 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4].
Qed.
End CJ0r.
