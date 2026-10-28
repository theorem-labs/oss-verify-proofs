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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_ngets.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition SITE_g1_gets : Z := 0x30c768.   (* [comment removed for export] *)
Definition SITE_g2_gets : Z := 0x30c7c0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hg_a_walk : forall (J RA : Z) ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  (J = J_GETS1 /\ RA = SITE_g1_gets) \/ (J = J_GETS2 /\ RA = SITE_g2_gets) ->
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz RA) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) c13 s11 (wz 255) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FZ_BIO_GETS) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros HJ SP0 SPH MI FRE. unfold TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  destruct HJ as [[-> ->]|[-> ->]]; unfold J_GETS1, J_GETS2.
  all: zstep; zstep; zstep; zstep; unfold SITE_g1_gets, SITE_g2_gets, FZ_BIO_GETS; apply evt_done; do 12 eexists; split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma hg1_b_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (k : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= k <= 254 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 (if k =? 0 then wz 854 else s2) s3 s7 (wz k) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz (if k =? 0 then J_RAISE2 else J_HD)) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_g1_gets) fc None m (seg_rom asegs)).
Proof.
  intros until k. intros SP0 SPH HK MI. unfold SITE_g1_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  zstep. zstep. zstep.
  destruct (Z.eqb_spec k 0) as [-> | NZ].
  - replace (bv_lts Startup_glue.z64 (Z_to_bv 64 0)) with false by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Z.ltb_irrefl). cbv iota.
    zstep. zstep. zstep. unfold J_RAISE2. apply evt_done. split; [reflexivity| exact I].
  - replace (bv_lts Startup_glue.z64 (Z_to_bv 64 k)) with true by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Z.ltb_lt; lia). cbv iota.
    unfold J_HD. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma hg2_b_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (k got' LB2 tmp : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= k <= 254 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 24) (loc_H LB2 tmp) ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 (wz (if k =? 0 then 854 else tmp)) s3 (if k =? 0 then s4 else s7)
                                    (wz k) (if k =? 0 then s6 else wz got') s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz (if k =? 0 then J_RAISE2 else J_HD)) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 (wz got') s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_g2_gets) fc None m (seg_rom asegs)).
Proof.
  intros until tmp. intros SP0 SPH HK MI FRH. unfold SITE_g2_gets, TP_A, loc_H in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  zstep. zstep.
  destruct (Z.eqb_spec k 0) as [-> | NZ].
  - replace (bv_lts Startup_glue.z64 (Z_to_bv 64 0)) with false by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Z.ltb_irrefl). cbv iota.
    zstep. zstep. unfold J_RAISE2. apply evt_done. split; [reflexivity| exact I].
  - replace (bv_lts Startup_glue.z64 (Z_to_bv 64 k)) with true by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Z.ltb_lt; lia). cbv iota.
    zstep. zstep. zstep. unfold J_HD. apply evt_done. split; [reflexivity| exact I].
Qed.

Section CHdg.
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
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_BG : bio_gets_stmt RT.
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).
Local Notation rest_keepI := (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).

(* [comment removed for export] *)
Lemma hd_keepW : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP XL W j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 (hBv dBv namev nn : Z) (bn : list byte),
  pem_com en Σ m off crem lrem cur -> w_ok RT en Σ XL W -> rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' -> In (e_E RT en, 904) KEEP -> In (namev, nn) KEEP ->
  ~ In (e_E RT en, 904) XL -> In (namev, nn) cur -> ~ In (namev, nn) XL -> 1 <= nn ->
  errst_at_rest (e_E RT en) [] m -> pem_frame en m j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  out_null RT en m -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
     errst_at_rest (e_E RT en) [] m' /\ pem_frame en m' j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap /\ rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)
  /\ out_null RT en m' /\ rw_cells asegs m' namev [CB (Z.to_nat nn) bn].
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur KEEP XL W j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv namev nn bn COM WOK PR INKE INKN NEL HNB NNL NN REST PFR FFC ON NBC.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  split; [exact (rest_keepI en Σ m m' off crem lrem cur _ W COM REST PR INKE (fun x Hx => HWL (e_E RT en) 904 x (ELV _ INE) NEL Hx))|].
  split; [exact (pem_frame_keep RT en m m' _ _ _ j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap PFR PR PD TOP HWS)|].
  split; [exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF)|].
  split.
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m' P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  eapply (cells_keep m m' namev nn); [exact NBC| exact PR| exact INKN| clear; lia| cbn [cells_size csize]; clear - NN; lia|].
  cbn [cells_size csize]. intros x Hx. apply (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL (namev, nn) x HNB NNL). cbn [fst snd]. clear - Hx NN. lia.
Qed.


Lemma mbio_rep_bnd : forall live (m : mem) K BI meth len max off, mbio_rep live m K BI meth len max off -> 0 <= off <= len /\ len <= max < 2 ^ 31 - 1.
Proof.
  intros live m K BI meth len max off (BM & fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & X1 & X2 & X3 & _)). lia.
Qed.


(* [comment removed for export] *)
Lemma hg_call : forall T (en : pem_entry) Σ (m : mem) off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 RA (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word) c (LB2 namev nn hBv dBv : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
  let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
  pem_com en Σ m off crem lrem cur -> 1 <= crem -> errst_at_rest (e_E RT en) [] m -> pem_frame en m j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap ->
  rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m ->
  LB2 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB2 [CB 256 bs] -> 1 <= nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
  mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_GETS m F fc (wz RA) t0 t1 t2 (wz (e_BI RT en)) (wz LB2) (wz 255) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (k off' : Z) (bs' : list byte),
     pem_com en Σ' m' off' (crem - 1) lrem cur -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
     errst_at_rest (e_E RT en) [] m' -> pem_frame en m' j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap -> rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m' ->
     length bs' = 256%nat -> rw_cells asegs m' LB2 [CB 256 bs'] -> rw_cells asegs m' namev [CB (Z.to_nat nn) bn] ->
     mbio_rep (rt_live RT Σ') m' KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ') m' KY dBv methY lenY maxY 0 ->
     ((k = 0 /\ off' = off /\ off = e_blen RT en) \/ (1 <= k <= Z.min (e_blen RT en - off) 254 /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ (k < Z.min (e_blen RT en - off) 254 -> nth_error bs' (Z.to_nat (k - 1)) = Some (Z_to_bv 8 10)) /\ off' = off + k)) ->
     ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en RA m' F' fc' (wz RA) y0 y1 y2 (wz k) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP C_BG errst_fp_where errst_rest_agree libenv_agree libenv_fp_where.
  intros T en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 RA F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 c LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM CR1 REST PFR FFC ON AL16 LBS LBC NN NBC MBX MBY RR RE Hc Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HNB : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) COM
                ltac:(intros e [<-|He]; [left; split; [exact HLB| cbn; clear; lia]| right; exact He])) as WOK.
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite !map_app, !mbio_ent_fst in ND'. cbn [map fst app] in ND'. rewrite <- !app_assoc in ND'. cbn [app] in ND'.
  pose proof (nd_split _ _ ND') as (NDX & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY).
  apply List.NoDup_cons_iff in ND3. destruct ND3 as [NQL ND4]. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NQN ND5]. apply List.NoDup_cons_iff in ND5. destruct ND5 as [NQE _].
  assert (NXL : forall e, In e (mbio_ent KX maxX) -> ~ In e ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1; apply (DJX _ H1); [apply in_or_app; right; left; reflexivity|].
    apply in_or_app; right; right; right; right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NYL : forall e, In e (mbio_ent KY maxY) -> ~ In e ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1; apply (DJY _ H1); [left; reflexivity|].
    right; right; right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NNL : ~ In (namev, nn) ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros [X|X]; [injection X; intros _ EE; apply NQL; left; exact (eq_sym EE)|]. apply NQN. right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NEL : ~ In (e_E RT en, 904) ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros [X|X]; [injection X; intros _ EE; apply NQL; right; left; exact (eq_sym EE)|]. apply NQE. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  set (W := map rng ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))) in *.
  eapply (pem_call_bgets RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BG T en Σ m off crem lrem _ LB2 bs RA
            F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6 c COM HLB AL16 LBS LBC CR1 RR RE Hc).
  intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' PR LBS' LBC' ARMS Hc'.
  change ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) with W in PR. rewrite LV' in PR.
  destruct (hd_keepW en Σ m m' off crem lrem _ _ _ _ j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv namev nn bn COM WOK PR (ELV _ INE) (CLV _ HNB) NEL HNB NNL NN REST PFR FFC ON NBC)
    as (REST' & PFR' & FFC' & ON' & NBC').
  assert (MBX' : mbio_rep (rt_live RT Σ') m' KX hBv methX lenX maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; rewrite LV'; split; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; left; exact He) (NXL _ He) Hx). }
  assert (MBY' : mbio_rep (rt_live RT Σ') m' KY dBv methY lenY maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; rewrite LV'; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NYL _ He) Hx). }
  exact (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' REST' PFR' FFC' ON' LBS' LBC' NBC' MBX' MBY' ARMS Hc').
Qed.

(* [comment removed for export] *)
Lemma grow_pot_big : forall (en : pem_entry) lenX lenY maxX maxY off,
  e_boff RT en <= off <= e_blen RT en -> 0 <= lenX -> 0 <= lenY -> lenX + lenY <= 2 * (off - e_boff RT en) ->
  maxX <= gr_n (lenX + 255) -> maxY <= gr_n (lenY + 255) -> 630784 <= grow_pot RT en maxX maxY.
Proof.
  intros en lenX lenY maxX maxY off HO HX HY HS MX MY. unfold grow_pot, grow_cap, e_plen. unfold gr_n in *.
  Z.div_mod_to_equations. nia.
Qed.

Theorem GETS1_proof : forall N, HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS (N - 1) -> GETS1_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N HDP en Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp got partial bn bs KX KY methX methY lenX maxX lenY maxY.
  intros MEAS INV PARTIAL INVG. unfold pem_at, cps. intros T c HA Hk.
  pose proof INV as (COM & REST & REM & LRM & PFR & FFC & ON & AL16 & LBS & LBC & NAL & NNR & LBN & NBC & NIN & MBX & MBY & GOT & GLT & GE2 & ENDV & LSUM & MXB & MYB).
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBX) as (LX & _). pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBY) as (LY & _).
  pose proof (grow_pot_big en lenX lenY maxX maxY off OFF ltac:(clear - LX; lia) ltac:(clear - LY; lia) LSUM MXB MYB) as GP.
  assert (CR1 : 1 <= crem) by (clear - REM GP OFF; unfold hd_need, C_END in REM; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  pose proof (hg_a_walk J_GETS1 SITE_g1_gets xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 s4 s5 (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                t3 t4 t5 t6 F fc m _ _ _ _ _ _ _ _ _ _ _ _ _ _ (or_introl (conj eq_refl eq_refl)) SP0' SPH MI FRE) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1 HA.
  eapply (hg_call T en Σ m off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 SITE_g1_gets F fc u0 u1 u2 b3 b4 b5 b6 b7 (wz tmp) s3 s4 s5 (wz got) (wz partial) u3 u4 u5 u6 c1
            LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY COM CR1 REST PFR FFC ON AL16 LBS LBC ltac:(clear - NNR; lia) NBC MBX MBY
            ltac:(unfold SITE_g1_gets; clear; lia) eq_refl Hc1').
  clear Hc1' u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6.
  intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' REST' PFR' FFC' ON' LBS' LBC' NBC' MBX' MBY' ARMS Hc'.
  pose proof COM' as (_ & MI' & _).
  assert (KR : 0 <= k <= 254) by (clear - ARMS; lia).
  pose proof (hg1_b_walk (wz SITE_g1_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 b4 b5 b6 b7 (wz tmp) s3 s4 s5 (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB)
                (wz namev) (wz LB2) y3 y4 y5 y6 F' fc' m' k SP0' SPH KR MI') as W.
  cl_lift W Hc' c2 Hc2. destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc'.
  destruct ARMS as [(-> & -> & OFE)|(KR1 & NULk & LFk & ->)].
  - (* [comment removed for export] *)
    cbn [Z.eqb] in Hc2'.
    refine (H_R2 en Σ' m' off (crem - 1) lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_g1_gets) y0 y1 y2 (wz 0) b1 b2 b3 b4 b5 b6 b7
              s3 (wz partial) (wz 0) (wz got) (wz partial) y3 y4 y5 y6 LB2 namev nn hBv dBv 854 bn bs' KX KY methX methY lenX maxX lenY maxY
              COM' REST' _ ltac:(clear - LRM; lia) ltac:(clear; lia) PFR' FFC' ON' AL16 LBS' LBC' NAL NNR LBN NBC' MBX' MBY' T c2 Hc2' Hk).
    clear - REM GP OFF. unfold hd_need, C_END in *. lia.
  - (* [comment removed for export] *)
    replace (k =? 0) with false in Hc2' by (symmetry; apply Z.eqb_neq; clear - KR1; lia).
    refine (HDP en Σ' m' (off + k) (crem - 1) lrem j0 (wz partial) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_g1_gets) y0 y1 y2 (wz k) b1 b2 b3 b4 b5 b6 b7 s3 y3 y4 y5 y6
              LB2 namev nn hBv dBv tmp k got partial bn bs' KX KY methX methY lenX maxX lenY maxY ltac:(clear - MEAS KR1; lia) _ ltac:(clear - KR1; lia) NULk PARTIAL
              ltac:(intros A1 A2; apply LFk; clear - A1 A2 KR1; lia) ltac:(replace (off =? e_blen RT en) with false in INVG by (symmetry; apply Z.eqb_neq; clear - KR1; lia); clear - INVG; lia) T c2 Hc2' Hk).
    unfold hd_inv. cbv zeta.
    split; [exact COM'|]. split; [exact REST'|]. split; [clear - REM KR1; unfold hd_need in *; lia|]. split; [exact LRM|].
    split; [exact PFR'|]. split; [exact FFC'|]. split; [exact ON'|].
    split; [exact AL16|]. split; [exact LBS'|]. split; [exact LBC'|].
    split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC'|]. split; [exact NIN|].
    split; [exact MBX'|]. split; [exact MBY'|].
    split; [exact GOT|]. split; [exact GLT|]. split; [exact GE2|]. split; [exact ENDV|].
    split; [clear - LSUM KR1; lia|]. split; [exact MXB| exact MYB].
Qed.

Theorem GETS2_proof : forall N, HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS (N - 1) -> GETS2_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N HDP en Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp got got' partial bn bs KX KY methX methY lenX maxX lenY maxY.
  intros MEAS INV PARTIAL GOT0 INVG. unfold pem_at, cps. intros T c HA Hk.
  pose proof INV as (COM & REST & REM & LRM & PFR & FFC & ON & AL16 & LBS & LBC & NAL & NNR & LBN & NBC & NIN & MBX & MBY & GOT & GLT & GE2 & ENDV & LSUM & MXB & MYB).
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBX) as (LX & _). pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBY) as (LY & _).
  pose proof (grow_pot_big en lenX lenY maxX maxY off OFF ltac:(clear - LX; lia) ltac:(clear - LY; lia) LSUM MXB MYB) as GP.
  assert (CR1 : 1 <= crem) by (clear - REM GP OFF; unfold hd_need, C_END in REM; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  pose proof (hg_a_walk J_GETS2 SITE_g2_gets xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz got') s3 s4 s5 (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                t3 t4 t5 t6 F fc m _ _ _ _ _ _ _ _ _ _ _ _ _ _ (or_intror (conj eq_refl eq_refl)) SP0' SPH MI FRE) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1 HA.
  eapply (hg_call T en Σ m off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 SITE_g2_gets F fc u0 u1 u2 b3 b4 b5 b6 b7 (wz got') s3 s4 s5 (wz got) (wz partial) u3 u4 u5 u6 c1
            LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY COM CR1 REST PFR FFC ON AL16 LBS LBC ltac:(clear - NNR; lia) NBC MBX MBY
            ltac:(unfold SITE_g2_gets; clear; lia) eq_refl Hc1').
  clear Hc1' u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6.
  intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' REST' PFR' FFC' ON' LBS' LBC' NBC' MBX' MBY' ARMS Hc'.
  pose proof COM' as (_ & MI' & _). pose proof PFR' as (_ & FRH' & _).
  assert (KR : 0 <= k <= 254) by (clear - ARMS; lia).
  pose proof (hg2_b_walk (wz SITE_g2_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB)
                (wz namev) (wz LB2) y3 y4 y5 y6 F' fc' m' k got' LB2 tmp SP0' SPH KR MI' FRH') as W.
  cl_lift W Hc' c2 Hc2. destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc'.
  destruct ARMS as [(-> & -> & OFE)|(KR1 & NULk & LFk & ->)].
  - (* [comment removed for export] *)
    cbn [Z.eqb] in Hc2'.
    refine (H_R2 en Σ' m' off (crem - 1) lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_g2_gets) y0 y1 y2 (wz 0) b1 b2 b3 b4 b5 b6 b7
              s3 s4 (wz 0) (wz got) (wz partial) y3 y4 y5 y6 LB2 namev nn hBv dBv 854 bn bs' KX KY methX methY lenX maxX lenY maxY
              COM' REST' _ ltac:(clear - LRM; lia) ltac:(clear; lia) PFR' FFC' ON' AL16 LBS' LBC' NAL NNR LBN NBC' MBX' MBY' T c2 Hc2' Hk).
    clear - REM GP OFF. unfold hd_need, C_END in *. lia.
  - (* [comment removed for export] *)
    replace (k =? 0) with false in Hc2' by (symmetry; apply Z.eqb_neq; clear - KR1; lia).
    refine (HDP en Σ' m' (off + k) (crem - 1) lrem j0 (wz partial) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_g2_gets) y0 y1 y2 (wz k) b1 b2 b3 b4 b5 b6 b7 s3 y3 y4 y5 y6
              LB2 namev nn hBv dBv tmp k got' partial bn bs' KX KY methX methY lenX maxX lenY maxY ltac:(clear - MEAS KR1; lia) _ ltac:(clear - KR1; lia) NULk PARTIAL
              ltac:(intros A1 A2; apply LFk; clear - A1 A2 KR1; lia) ltac:(replace (off =? e_blen RT en) with false in INVG by (symmetry; apply Z.eqb_neq; clear - KR1; lia); clear - INVG; lia) T c2 Hc2' Hk).
    unfold hd_inv. cbv zeta.
    split; [exact COM'|]. split; [exact REST'|]. split; [clear - REM KR1; unfold hd_need in *; lia|]. split; [exact LRM|].
    split; [exact PFR'|]. split; [exact FFC'|]. split; [exact ON'|].
    split; [exact AL16|]. split; [exact LBS'|]. split; [exact LBC'|].
    split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC'|]. split; [exact NIN|].
    split; [exact MBX'|]. split; [exact MBY'|].
    split; [exact GOT|]. split; [exact GLT|]. split; [exact GE2|]. split; [exact ENDV|].
    split; [clear - LSUM KR1; lia|]. split; [exact MXB| exact MYB].
Qed.
End CHdg.
