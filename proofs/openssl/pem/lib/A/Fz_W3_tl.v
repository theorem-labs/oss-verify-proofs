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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_aux4 Fz_W3_lits Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_tl_ctrl : Z := 0x30c8e4.   (* [comment removed for export] *)
Definition SITE_tl_cnew : Z := 0x30c950.   (* [comment removed for export] *)

Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma tl_c0_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (dBv : Z) (q0 q1 q2 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 80) [C8 q0; C8 q1; C8 q2] ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz SITE_tl_ctrl) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) (wz dBv) (wz 115) (wz 0) q2 a4' a5' a6' a7' s2 (wz dBv) s4 q2 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz FZ_BIO_CTRL) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_TAIL) fc None m (seg_rom asegs)).
Proof.
  intros until q2. intros SP0 SPH MI FRF. unfold J_TAIL, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold SITE_tl_ctrl, FZ_BIO_CTRL. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma tl_c1n_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (f BM n : Z) (hj : list byte) (lenv : word) (j1 : list byte) (tav : word) (j2 j3 : list byte) (w1 w2 w3 q0 q2 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [C8 q0; C8 (wz (f + 32)); C8 q2] ->
  rw_cells asegs m f (ff_cells hj lenv j1 tav j2 (wz BM) j3) ->
  rw_cells asegs m BM [C8 (wz n); C8 w1; C8 w2; C8 w3] -> acc asegs m BM 32 -> BM mod 8 = 0 -> 0 < BM -> BM + 32 <= sp1 -> 1 <= n < 2 ^ 31 ->
  evt asegs (fun ms => exists (t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms = MS (mkR (wz SITE_tl_cnew) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) (wz n) (wz (f + 32)) a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (f + 64)) s6 s7 s8 (wz SHB) s10 s11 t3' t4' t5' t6')
               F (wz FZ_EVP_CTX_NEW) fc None m' (seg_rom asegs)
       /\ munch [(f + 32, f + 36)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' f (ff_cells hj (wz n) j1 tav j2 (wz BM) j3))
    (MS (mkR (wz SITE_tl_ctrl) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (f + 64)) s6 s7 s8 (wz SHB) s10 s11 t3 t4 t5 t6)
        F (wz SITE_tl_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until q2. intros SP0 SPH F0 FH MI FRF FFC BMC ACC BAL B0 BH NR. unfold SITE_tl_ctrl, TP_A, SHB in *. unfold ff_cells in FFC.
  pose proof (munch_refl [(f + 32, f + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  zstep.
  zstep. zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. replace (n ≫ 31) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  zstep. th_if_lit.
  zstep. zstep. lfix. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  zstep.
  unfold SITE_tl_cnew, FZ_EVP_CTX_NEW. apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FFC].
Qed.

(* [comment removed for export] *)
Lemma tl_c1z_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (f BM : Z) (hj : list byte) (lenv : word) (j1 : list byte) (tav : word) (j2 j3 : list byte) (w1 w2 w3 q0 q2 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [C8 q0; C8 (wz (f + 32)); C8 q2] ->
  rw_cells asegs m f (ff_cells hj lenv j1 tav j2 (wz BM) j3) ->
  rw_cells asegs m BM [C8 (wz 0); C8 w1; C8 w2; C8 w3] -> acc asegs m BM 32 -> BM mod 8 = 0 -> 0 < BM -> BM + 32 <= sp1 ->
  evt asegs (fun ms => exists (t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms = MS (mkR (wz SITE_tl_ctrl) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) (wz 0) (wz (f + 32)) a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz 0) s6 s7 s8 (wz SHB) s10 (wz 0) t3' t4' t5' t6')
               F (wz J_END) fc None m' (seg_rom asegs)
       /\ munch [(f + 32, f + 36)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' f (ff_cells hj (wz 0) j1 tav j2 (wz BM) j3))
    (MS (mkR (wz SITE_tl_ctrl) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (f + 64)) s6 s7 s8 (wz SHB) s10 s11 t3 t4 t5 t6)
        F (wz SITE_tl_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until q2. intros SP0 SPH F0 FH MI FRF FFC BMC ACC BAL B0 BH. unfold SITE_tl_ctrl, TP_A, SHB in *. unfold ff_cells in FFC.
  pose proof (munch_refl [(f + 32, f + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  zstep.
  zstep. zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. change Startup_glue.z64 with (Z_to_bv 64 0). try change (0 ≫ 31) with 0.
  zstep. try th_if_lit.
  zstep. zstep. lfix. zstep. try th_if_lit.
  zstep. zstep.
  unfold J_END. apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FFC].
Qed.

(* [comment removed for export] *)
Lemma tl_c2_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (p : Z),
  0 < p < 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_tl_cnew) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_INI) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_tl_cnew) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_tl_cnew) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros HP MI. unfold SITE_tl_cnew, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  zstep. if_false. unfold J_INI. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Section CTl.
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
Hypothesis C_BT : bio_ctrl_ptr_stmt RT.
Hypothesis C_CN : evp_ctx_new_stmt RT FZ_SITES FZ_CALLS.
Hypothesis ENDP : END_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis INIP : INI_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keepL : forall (en : pem_entry) Σ Σ' (m m' : mem) off crem lrem cur,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
  In (e_E RT en, 904) (rt_live RT Σ') -> errst_at_rest (e_E RT en) [] m'.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ Σ' m m' off crem lrem cur COM REST PR INE'. apply (errst_rest_agree m m' _ _ REST). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
  apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INE' | exact R] | exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM _ R)].
Qed.

Lemma mcost_nonneg : forall n, 0 <= mcost n.
Proof. intros n. unfold mcost. destruct (n <=? 64512) eqn:E; [lia| apply Z.leb_gt in E; lia]. Qed.

(* [comment removed for export] *)
Theorem TAIL_proof : TAIL_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6
         namev nn hBv dBv bn KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM REST REM LRM PFR FFC ON NMA NN BNL NMC HIN MBX MBY LSUM. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FLO & _ & FR4). change (fs_size 1) with 128 in FLO, FR4.
  assert (FH : e_f RT en + 128 <= e_sp1 RT en) by (clear - FLO LOW HLO; lia).
  assert (HNM : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite map_app, map_app, <- app_assoc in ND'. pose proof (nd_split _ _ ND') as (_ & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDYN & _ & _). pose proof (nd_split _ _ NDYN) as (_ & _ & DJY). clear ND' ND2 NDYN.
  assert (NNY : ~ In (namev, nn) (mbio_ent KY maxY)) by (intros X; exact (DJY namev (in_map fst _ _ X) ltac:(cbn; left; reflexivity))).
  assert (NXY : forall e, In e (mbio_ent KX maxX) -> ~ In e (mbio_ent KY maxY)).
  { intros e He X. exact (DJX (fst e) (in_map fst _ _ He) ltac:(apply in_or_app; left; apply in_or_app; left; exact (in_map fst _ _ X))). }
  assert (NEY : ~ In (e_E RT en, 904) (mbio_ent KY maxY)).
  { intros X. apply (NTL (e_E RT en, 904) (or_introl eq_refl)). apply in_or_app; right. cbn [fst]. apply (in_map fst _ (e_E RT en, 904)). apply in_or_app; right; apply in_or_app; left; exact X. }
  assert (CR7 : C_END + 7 <= crem) by (pose proof (mcost_nonneg (lenX + 1)) as M1; pose proof (mcost_nonneg lenY) as M2; clear - REM M1 M2; lia).
  (* [comment removed for export] *)
  pose proof PFR as (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG). unfold loc_F in FRF.
  pose proof (tl_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz (e_flags RT en)) s5 (wz (e_f RT en)) (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) s11 t3 t4 t5 t6 F fc m dBv _ _ _ SP0' SPH MI FRF) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1 HA.
  clear FR0 FRH SZH FRF SZF FR104 FRE FR224 FRG.
  (* [comment removed for export] *)
  assert (HP1 : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)]) (mbio_ent KY maxY ++ mbio_ent KX maxX ++ [(namev, nn)])) by apply Permutation_app_swap_app.
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM HP1) as COM1.
  eapply (pem_call_bptr RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BT T en Σ m off crem lrem (mbio_ent KX maxX ++ [(namev, nn)])
            KY dBv methY lenY maxY 0 hj lenv j1 tav j2 bmv j3 SITE_tl_ctrl F fc u0 u1 u2 b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz (e_f RT en + 64))
            (wz (e_f RT en)) (wz hBv) (wz namev) s11 u3 u4 u5 u6 c1 COM1 MBY FFC ltac:(unfold SITE_tl_ctrl; clear; lia) eq_refl Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m1 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 BM COM2 PR1 WS1 WFR1 WL1 FFC1 MBY1 MI1 Hc2.
  replace (lenY - 0) with lenY in MBY1 by (clear; lia). pose proof COM2 as (ART1 & _).
  assert (REST1 : errst_at_rest (e_E RT en) [] m1).
  { apply (errst_rest_agree m m1 _ _ REST). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
    apply PR1; [apply (acl_live _ _ _ (e_E RT en) 904); [exact (ELV _ INE)| exact R]| exact (WL1 (e_E RT en) 904 _ (ELV _ INE) NEY R)]. }
  pose proof (pem_frame_keep RT en m m1 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR PR1 PD TOP WS1) as PFR1.
  assert (ON1 : out_null RT en m1).
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m1 off crem lrem _ _ _ COM1 WS1 WFR1 PR1) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m1 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
  assert (NMC1 : rw_cells asegs m1 namev [CB (Z.to_nat nn) bn]).
  { eapply rw_cells_agree_nw; [exact NMC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. assert (Ha' : namev <= bv_unsigned a < namev + nn) by (clear - Ha NN; lia).
    apply PR1; [apply (acl_live _ _ _ namev nn); [exact (CLV _ HNM)| exact Ha']|].
    exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM1 WL1 (namev, nn) _ ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity) NNY Ha'). }
  assert (MBX1 : mbio_rep (rt_live RT Σ) m1 KX hBv methX lenX maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR1| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM1 WL1 e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NXY e He) Hx). }
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ _ COM2 (Permutation_sym HP1)) as COM3.
  clear COM1 COM2 PR1 WS1 WFR1 WL1 REST PFR FFC ON NMC MBX MBY MI.
  (* [comment removed for export] *)
  pose proof MBY1 as (fl1 & rrw1 & numw1 & padw1 & nr1 & nw1 & EBI & EBM & INBI & BI16 & NDK & METH & HEAD & W1C & FLOK & TAILC & (rmw & INBB & BB16 & BBC & INBM & BM16 & INRP & RP16 & Y1 & Y2 & Y3 & INNER)).
  rewrite <- EBM in INBM, BM16, INNER.
  assert (BMC : exists w1 w2 flw, rw_cells asegs m1 BM [C8 (wz lenY); C8 w1; C8 w2; C8 flw]).
  { destruct (k_d KY) as [d|]; [destruct INNER as (junk & _ & _ & C & _)| destruct INNER as (_ & C & _)]; eexists _, _, _; exact C. }
  clear HEAD W1C TAILC BBC INNER INBB INRP. destruct BMC as (w1 & w2 & flw & BMC).
  destruct (af_acc_live RT AF Σ m1 BM 32 ART1 INBM) as [_ ACC1].
  pose proof (af_live_range RT AF Σ m1 BM 32 ART1 INBM) as (B0 & BHI & _).
  assert (BH : BM + 32 <= e_sp1 RT en) by (clear - BHI LOW HLO; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof PFR1 as (_ & _ & _ & FRF1 & _). unfold loc_F in FRF1.
  (* [comment removed for export] *)
  assert (WS2 : forall x, e_sp1 RT en <= x < USTACK_TOP -> outside [(e_f RT en + 32, e_f RT en + 36)] x) by (intros x Hx; cbn; split; [clear - Hx FH; lia| exact I]).
  assert (WL2 : forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> outside [(e_f RT en + 32, e_f RT en + 36)] x).
  { intros p n x Hin Hx. cbn. split; [| exact I]. destruct (FR4 p n Hin) as [Q|Q]; clear - Q Hx; lia. }
  assert (WFR2 : forall f' k x, In (f', k) (e_frames RT en) -> f' <= x < f' + fs_size k - 8 -> outside [(e_f RT en + 32, e_f RT en + 36)] x).
  { intros f' k x Hin Hx. cbn. split; [| exact I]. intros R.
    apply (proj1 (proj2 (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ (e_f RT en + 32, e_f RT en + 36) x COM3 ltac:(right; right; cbn; clear; lia) ltac:(cbn; exact R)))).
    right; right; right; left. exists f', k. split; [exact Hin| exact Hx]. }
  (* [comment removed for export] *)
  assert (SEG : forall (m2 : mem) lv, munch [(e_f RT en + 32, e_f RT en + 36)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
            rw_cells asegs m2 (e_f RT en) (ff_cells hj lv j1 tav j2 (wz BM) j3) ->
               pem_com en Σ m2 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)]) /\ errst_at_rest (e_E RT en) [] m2
            /\ pem_frame en m2 j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ out_null RT en m2 /\ rw_cells asegs m2 namev [CB (Z.to_nat nn) bn]
            /\ mbio_rep (rt_live RT Σ) m2 KX hBv methX lenX maxX 0 /\ mbio_repx (rt_live RT Σ) m2 KY dBv BM (wz lenY) methY lenY maxY 0).
  { intros m2 lv MU2 WM2 MI2 FFC2.
    assert (PR2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(e_f RT en + 32, e_f RT en + 36)] m1 m2) by (intros a _ Ho; exact (MU2 a Ho)).
    assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)).
    { pose proof COM3 as (_ & _ & ST1 & _). eapply stk_munch; [exact ST1| exact MU2| exact WM2|]. intros x Hx. cbn. split; [clear - Hx FLO LOW; lia| exact I]. }
    split.
    { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m1 m2); [exact COM3| exact MU2| exact WM2| exact MI2| exact ST2|].
      apply Forall_cons; [| apply Forall_nil]. right; right. cbn [fst snd]. clear; lia. }
    split.
    { apply (errst_rest_agree m1 m2 _ _ REST1). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
      apply PR2; [apply (acl_live _ _ _ (e_E RT en) 904); [exact (ELV _ INE)| exact R]| exact (WL2 _ _ _ (ELV _ INE) R)]. }
    split; [exact (pem_frame_keep RT en m1 m2 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR1 PR2 PD TOP WS2)|].
    split.
    { destruct ON1 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 m2 off crem lrem _ _ _ COM3 WS2 WFR2 PR2) as AGP.
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m1 P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
      { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
      split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
    split.
    { eapply rw_cells_agree_nw; [exact NMC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. assert (Ha' : namev <= bv_unsigned a < namev + nn) by (clear - Ha NN; lia).
      apply PR2; [apply (acl_live _ _ _ namev nn); [exact (CLV _ HNM)| exact Ha']| exact (WL2 _ _ _ (CLV _ HNM) Ha')]. }
    split.
    { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX1| exact PR2| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
      intros [p n] x He Hx. exact (WL2 p n x (CLV _ ltac:(apply in_or_app; left; exact He)) Hx). }
    eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY1| exact PR2| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (WL2 p n x (CLV _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
  pose proof (rw_cells_bound asegs m1 namev _ NMC1) as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
  destruct (Z.eq_dec lenY 0) as [LY0 | LYNZ].
  - (* [comment removed for export] *)
    subst lenY.
    pose proof (tl_c1z_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz (e_f RT en)) (wz hBv)
                  (wz (shad (e_f RT en))) (wz namev) s11 y3 y4 y5 y6 F1 fc1 m1 (e_f RT en) BM hj lenv j1 tav j2 j3 w1 w2 flw _ _ SP0' SPH F0 FH MI1 FRF1 FFC1 BMC ACC1 BM8 B0 BH) as W.
    cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & FFC2) & Hc3'). clear Hc3 Hc2.
    destruct (SEG m2 _ MU2 WM2 MI2 FFC2) as (COM4 & REST2 & PFR2 & ON2 & NMC2 & MBX2 & MBY2). clear SEG.
    destruct MBX2 as [BMX MBX2]. destruct ON2 as (O1 & O2 & O3 & O4).
    assert (HP2 : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)]) ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent None ++ opt_ent (Some (namev, nn))) ++ [] ++ [])).
    { rewrite !app_nil_r. cbn [opt_ent app]. apply Permutation_refl. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ _ COM4 HP2) as COM5.
    refine (ENDP en Σ m2 off crem lrem [] [] j0 lH (loc_F RT en) endv x1 x2 gap hj (wz 0) j1 tav j2 (wz BM) j3 F1 fc1 eH eD (wz SITE_tl_ctrl) v0 v1 v2 (wz 0) (wz (e_f RT en + 32)) d2 d3 d4 d5 d6 d7 v3 v4 v5 v6
              None (Some (namev, nn)) 0 namev nn hBv dBv 0 KX KY BMX BM methX methY lenX maxX 0 0 maxY 0 (wz lenX) (wz 0)
              COM5 _ ltac:(clear - CR7; lia) PFR2 FFC2 eq_refl (conj eq_refl (conj (proj1 NN) (rw_cells_CB0 m2 namev NB1 ltac:(clear - NB2; lia)))) MBX2 MBY2 _ ltac:(cbn; clear - OFF; lia) T c3 Hc3' Hk).
    + split; [left; split; [reflexivity| exact REST2]|]. split; [apply Forall_nil|]. split; intros e [].
    + left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. exists (wz 0). exact O4.
  - (* [comment removed for export] *)
    pose proof (tl_c1n_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz (e_f RT en)) (wz hBv)
                  (wz (shad (e_f RT en))) (wz namev) s11 y3 y4 y5 y6 F1 fc1 m1 (e_f RT en) BM lenY hj lenv j1 tav j2 j3 w1 w2 flw _ _ SP0' SPH F0 FH MI1 FRF1 FFC1 BMC ACC1 BM8 B0 BH
                  ltac:(clear - LYNZ Y1 Y2 Y3; lia)) as W.
    cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & FFC2) & Hc3'). clear Hc3 Hc2.
    destruct (SEG m2 _ MU2 WM2 MI2 FFC2) as (COM4 & REST2 & PFR2 & ON2 & NMC2 & MBX2 & MBY2). clear SEG.
    (* [comment removed for export] *)
    eapply (pem_call_cnew RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_CN T en Σ m2 off crem lrem _ SITE_tl_cnew F1 fc1
              v0 v1 v2 (wz lenY) (wz (e_f RT en + 32)) d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz (e_f RT en + 64)) (wz (e_f RT en)) (wz hBv) (wz namev) s11 v3 v4 v5 v6 c3
              COM4 ltac:(clear - LRM; lia) ltac:(left; reflexivity) Hc3').
    clear Hc3'. intros Σ3 m3 F3 fc3 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c4 p COM6 LV3 FRS3 PR3 ZC P0 P16 PTOP Hc4.
    pose proof COM6 as (_ & MI3 & _).
    assert (PRL : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m2 m3).
    { intros a Ha Ho. apply (PR3 a Ha). cbn. split; [| exact I]. unfold lib_W, LIB_W in Ho. apply outside_app_l in Ho. cbn in Ho. unfold G_ALLOW_CUST. clear - Ho. lia. }
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ COM4) as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (LIN : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; right; exact He).
    pose proof (rest_keepL en Σ Σ m2 m3 off crem lrem _ COM4 REST2 PRL (ELV _ INE)) as REST3.
    pose proof (pem_frame_keep RT en m2 m3 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR2 PRL PD TOP HWS) as PFR3.
    pose proof (ff_keep m2 m3 (e_f RT en) _ _ _ _ hj (wz lenY) j1 tav j2 (wz BM) j3 FFC2 PRL INF HWFF) as FFC3.
    assert (ON3 : out_null RT en m3).
    { destruct ON2 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 m3 off crem lrem _ _ _ COM4 HWS HWFR PRL) as AGP.
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m2 P [C8 vv] -> rw_cells asegs m3 P [C8 vv]).
      { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
      split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
    assert (NMC3 : rw_cells asegs m3 namev [CB (Z.to_nat nn) bn]).
    { eapply rw_cells_agree_nw; [exact NMC2|]. intros a Ha.
      apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 m3 off crem lrem _ _ _ _ (namev, nn) COM4 HWL (fun e H => or_intror H) PRL HNM (CLV _ HNM)).
      cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha NN. lia. }
    assert (MBX3 : mbio_rep (rt_live RT Σ3) m3 KX hBv methX lenX maxX 0).
    { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX2| exact PRL| intros e He; split; [| apply LIN]; apply CLV; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ _ _ COM4 HWL (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; left; exact He) Hx). }
    assert (MBY3 : mbio_repx (rt_live RT Σ3) m3 KY dBv BM (wz lenY) methY lenY maxY 0).
    { eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY2| exact PRL| intros e He; split; [| apply LIN]; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ _ _ COM4 HWL (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) Hx). }
    clear COM4 REST2 PFR2 ON2 NMC2 MBX2 MBY2 PRL PR3 HWS HWFR HWFF HWF HWL HWP.
    (* [comment removed for export] *)
    pose proof (tl_c2_walk (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e1 e2 e3 e4 e5 e6 e7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz (e_f RT en + 64)) (wz (e_f RT en)) (wz hBv)
                  (wz (shad (e_f RT en))) (wz SHB) (wz namev) s11 z3 z4 z5 z6 F3 fc3 m3 p ltac:(clear - P0 PTOP; unfold ECTX, USTACK_TOP in PTOP; lia) MI3) as W.
    cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ3 _ _ c5 Hc5) as (ms5 & (-> & _) & Hc5'). clear Hc5 Hc4.
    assert (HP3 : Permutation ((p, ECTX) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)])) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (p, ECTX)])).
    { rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(namev, nn)]), (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(namev, nn); (p, ECTX)]).
      change [(namev, nn); (p, ECTX)] with ([(namev, nn)] ++ [(p, ECTX)]). rewrite (app_assoc (mbio_ent KX maxX ++ mbio_ent KY maxY) [(namev, nn)] [(p, ECTX)]).
      apply Permutation_cons_append. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ3 m3 off crem (lrem - 1) _ _ COM6 HP3) as COM7.
    exact (INIP en Σ3 m3 off crem (lrem - 1) j0 lH endv x1 x2 gap hj j1 tav j2 j3 F3 fc3 eH eD (wz SITE_tl_cnew) z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 (wz (e_f RT en)) (wz (e_flags RT en)) (wz (e_f RT en + 64)) (wz (e_f RT en)) s11 z3 z4 z5 z6
             p namev nn hBv dBv BM bn KX KY methX methY lenX maxX lenY maxY COM7 REST3 REM ltac:(clear - LRM; lia) PFR3 FFC3 ON3 P16 ZC NMA NN BNL NMC3 HIN MBX3 MBY3
             ltac:(clear - LYNZ Y1; lia) LSUM T c5 Hc5' Hk).
Qed.
End CTl.
