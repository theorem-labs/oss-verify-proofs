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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W1_grow Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_gg_gets : Z := 0x30c398.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gg_c0_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz SITE_gg_gets) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) c13 s5 (wz 255) a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz FZ_BIO_GETS) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GNG) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH MI FRE. unfold J_GNG, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  unfold SITE_gg_gets, FZ_BIO_GETS. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gg_c1_walk_pos : forall ra sp1 gp t0 t1 t2 s0 s1 k a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 < k < 2 ^ 31 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz k) (wz k) a2 (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GN) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gg_gets) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HK MI. unfold SITE_gg_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (SK : bv_signed (Z_to_bv 64 k) = k) by (rewrite zb_signed, EK; destruct (Z.ltb_spec k (2 ^ 63)); lia).
  assert (S0 : bv_signed z64 = 0) by reflexivity.
  zstep. zstep. zstep. if_true.
  unfold J_GN. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gg_c1_walk_zero : forall ra sp1 gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) (wz 0) a2 (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE1) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gg_gets) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_gg_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. assert (S0 : bv_signed z64 = 0) by reflexivity. if_false.
  unfold J_RAISE1. apply evt_done. split; [reflexivity| exact I].
Qed.

Section CGng.
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
Hypothesis C_BG : bio_gets_stmt RT.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_post := (pem_post RT libenv errst_live).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keep_g : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP W,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
  In (e_E RT en, 904) KEEP -> (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) -> errst_at_rest (e_E RT en) [] m'.
Proof using errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur KEEP W COM ER PR INK HO. eapply errst_rest_agree; [exact ER|]. intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)]. apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INK| exact R]| exact (HO _ R)].
Qed.

(* [comment removed for export] *)
Theorem GNG_proof : forall N,
  RAISE1_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS -> GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS (N - 1) ->
  GNG_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N RS1 GNP en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6
         LB1 hBv dBv bs KX KY methX methY maxX maxY.
  cbv zeta. intros MEAS COM REST REM LRM PFR FFC ON LBA LBS LBC MBX MBY MX0 MY0. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) COM
                ltac:(intros e [<-|He]; [left; split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity| cbn; clear; lia]| right; exact He])) as WOK.
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _ & _). unfold loc_E in FRE.
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite !map_app, !mbio_ent_fst in ND'. cbn [map fst app] in ND'. rewrite <- !app_assoc in ND'. cbn [app] in ND'.
  pose proof (nd_split _ _ ND') as (NDX & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY). apply List.NoDup_cons_iff in ND3. destruct ND3 as [NQL ND4]. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NQE ND5].
  assert (NXL : forall e, In e (mbio_ent KX maxX) -> ~ In e ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1; apply (DJX _ H1); [apply in_or_app; right; left; reflexivity|].
    apply in_or_app; right; right; right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NYL : forall e, In e (mbio_ent KY maxY) -> ~ In e ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1; apply (DJY _ H1); [left; reflexivity|].
    right; right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NEL : ~ In (e_E RT en, 904) ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros [X|X]; [injection X; intros _ EE; apply NQL; left; exact (eq_sym EE)|]. apply NQE. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  set (W := map rng ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))) in *.
  assert (OUTX : forall e x, In e (mbio_ent KX maxX) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; left; exact He) (NXL _ He) Hx). }
  assert (OUTY : forall e x, In e (mbio_ent KY maxY) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NYL _ He) Hx). }
  assert (OUTE : forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x).
  { intros x Hx. exact (HWL (e_E RT en) 904 x (ELV _ INE) NEL Hx). }
  assert (G255 : 255 < gr_n (0 + 255)) by (apply gr_n_gt; clear; lia).
  assert (GP0 : 0 <= grow_pot RT en 0 0) by (apply (grow_pot_nonneg RT en 0 0 0 0 off OFF); clear - G255 OFF; lia).
  assert (CR1 : 1 <= crem) by (clear - REM GP0 OFF BLT; unfold gn_need, C_END in REM; lia).
  (* [comment removed for export] *)
  pose proof (gg_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                (wz LIT_TAIL) s7 (wz (shad (e_f RT en))) (wz SHB) (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6 F fc m _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH MI FRE) as W0.
  cl_lift W0 HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1.
  eapply (pem_call_bgets RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BG T en Σ m off crem lrem _ LB1 bs SITE_gg_gets
            F fc u0 u1 u2 a3 b4 b5 b6 b7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) u3 u4 u5 u6 c1
            COM ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity) LBA LBS LBC
            CR1
            ltac:(unfold SITE_gg_gets; clear; lia) ltac:(reflexivity) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' PR LBS' LBC' ARMS Hc'.
  pose proof COM' as (_ & MI' & _).
  change ((LB1, LB1 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) with W in PR.
  (* [comment removed for export] *)
  assert (REST' : errst_at_rest (e_E RT en) [] m').
  { eapply (rest_keep_g en Σ m m'); [exact COM| exact REST| exact PR| rewrite LV'; exact (ELV _ INE)| exact OUTE]. }
  assert (PFR' : pem_frame en m' j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m m' _ _ _ j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap PFR PR PD TOP HWS).
  assert (FFC' : rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  assert (ON' : out_null RT en m').
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m' P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX' : mbio_rep (rt_live RT Σ') m' KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; rewrite LV'; split; apply CLV; apply in_or_app; left; exact He| exact OUTX]. }
  assert (MBY' : mbio_rep (rt_live RT Σ') m' KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; rewrite LV'; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He| exact OUTY]. }
  clear PFR FFC ON MBX MBY REST.
  destruct ARMS as [(-> & -> & OFE)|(KR & NULk & LFk & ->)].
  - (* [comment removed for export] *)
    pose proof (gg_c1_walk_zero (wz SITE_gg_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) b1 b2 b3 d4 d5 d6 d7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                  (wz LIT_TAIL) s7 (wz (shad (e_f RT en))) (wz SHB) (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) y3 y4 y5 y6 F' fc' m' MI') as W1.
    cl_lift W1 Hc' c2 Hc2. destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc'.
    refine (RS1 en Σ' m' off (crem - 1) lrem j0 lH (loc_F RT en) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_gg_gets) y0 y1 y2 (wz 0) (wz 0) b2 (wz 0) d4 d5 d6 d7
              (wz 6) s3 (wz LIT_BEGIN) (wz LIT_TAIL) s7 (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) y3 y4 y5 y6 LB1 hBv dBv bs' KX KY methX methY 0 maxX 0 maxY
              COM' REST' _ ltac:(clear - LRM; lia) PFR' FFC' ON' LBA LBS' LBC' MBX' MBY' T c2 Hc2' Hk).
    clear - REM GP0 OFF BLT. unfold gn_need, C_END in *. lia.
  - (* [comment removed for export] *)
    pose proof COM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OFF' & _).
    pose proof (gg_c1_walk_pos (wz SITE_gg_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) k b1 b2 b3 d4 d5 d6 d7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                  (wz LIT_TAIL) s7 (wz (shad (e_f RT en))) (wz SHB) (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) y3 y4 y5 y6 F' fc' m' ltac:(clear - KR; lia) MI') as W1.
    cl_lift W1 Hc' c2 Hc2. destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc'.
    refine (GNP en Σ' m' (off + k) (crem - 1) lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_gg_gets) y0 y1 y2 (wz k) b2 d4 d5 d6 d7 s3 s7 y3 y4 y5 y6
              LB1 hBv dBv k 0 bs' KX KY methX methY maxX maxY _ COM' REST' _ LRM PFR' FFC' ON' LBA LBS' LBC' ltac:(clear - KR; lia) NULk ltac:(clear; lia) MBX' MBY' MX0 MY0 T c2 Hc2' Hk).
    + clear - MEAS KR. lia.
    + clear - REM KR. unfold gn_need in *. lia.
Qed.
End CGng.
