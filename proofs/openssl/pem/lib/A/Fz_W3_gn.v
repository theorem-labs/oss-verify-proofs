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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W3_gnlem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import IcptSpec Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W1_grow Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_lits Fz_W3_gnlem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_gn_san : Z := 0x30c34c.    (* [comment removed for export] *)
Definition SITE_gn_snc1 : Z := 0x30c364.   (* [comment removed for export] *)
Definition SITE_gn_snc2 : Z := 0x30c384.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gn_c0_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz SITE_gn_san) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 s1 s5 a1 s10 a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz FZ_SANITIZE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GN) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold J_GN, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  unfold SITE_gn_san, FZ_SANITIZE. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz SITE_gn_snc1) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 s1 s5 s4 (wz 11) a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 a0 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz e_strncmp) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gn_san) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_gn_san, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold SITE_gn_snc1, e_strncmp. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c2_walk_ne : forall ra sp1 gp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned (Z_to_bv 64 r) <> 0 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GNG) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gn_snc1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HR MI. unfold SITE_gn_snc1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_true.
  unfold J_GNG. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c2_walk_lt : forall ra sp1 gp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 len' s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned (Z_to_bv 64 r) = 0 -> 1 <= len' < 6 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 6) s3 s4 s5 s6 (wz len') s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GNG) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 6) s3 s4 s5 s6 (wz len') s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gn_snc1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HR HL MI. unfold SITE_gn_snc1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (S6 : bv_signed (Z_to_bv 64 6) = 6) by reflexivity.
  assert (SL : bv_signed (Z_to_bv 64 len') = len') by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb_spec len' (2 ^ 63)); lia).
  zstep. if_false. zstep. if_true.
  unfold J_GNG. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c2_walk_go : forall ra sp1 gp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 len' s8 s9 s10 LB1 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned (Z_to_bv 64 r) = 0 -> 6 <= len' <= 255 -> 0x10000 <= LB1 -> LB1 + 256 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz SITE_gn_snc2) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 s1 (wz (LB1 + len' - 6)) s6 (wz 6) a3 a4' a5' a6' a7' (wz 6) (wz (LB1 + len' - 6)) s4 s5 s6 (wz len') s8 s9 s10 (wz (LB1 - 6)) t3' t4' t5' t6')
               F (wz e_strncmp) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 6) s3 s4 s5 s6 (wz len') s8 s9 s10 (wz (LB1 - 6)) t3 t4 t5 t6) F (wz SITE_gn_snc1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HR HL HLB1 HLB2 MI. unfold SITE_gn_snc1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (S6 : bv_signed (Z_to_bv 64 6) = 6) by reflexivity.
  assert (SL : bv_signed (Z_to_bv 64 len') = len') by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb_spec len' (2 ^ 63)); lia).
  assert (EL : bv_unsigned (Z_to_bv 64 len') = len') by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 (LB1 - 6)) = LB1 - 6) by (apply unsigned_lit; lia).
  zstep. if_false. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  replace (LB1 - 6 + len') with (LB1 + len' - 6) by lia.
  unfold SITE_gn_snc2, e_strncmp. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c3_walk_eq : forall ra sp1 gp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned (Z_to_bv 64 r) = 0 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_NAME) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gn_snc2) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HR MI. unfold SITE_gn_snc2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_true.
  unfold J_NAME. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma gn_c3_walk_ne : forall ra sp1 gp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned (Z_to_bv 64 r) <> 0 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GNG) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_gn_snc2) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HR MI. unfold SITE_gn_snc2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_false.
  unfold J_GNG. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma land_lnot4_bound : forall f, 0 <= f < 256 -> 0 <= Z.land f (Z.lnot 4) < 256.
Proof.
  intros f Hf. pose proof (proj2 (Z.land_nonneg f (Z.lnot 4)) (or_introl (proj1 Hf))) as H1.
  assert (H4 : 0 <= 4) by lia. pose proof (proj2 (Z.land_nonneg f 4) (or_intror H4)) as H2. rewrite <- Z.sub_land_same_l in H1 |- *. lia.
Qed.

Section CGn.
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
Hypothesis C_SAN : sanitize_line_stmt RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis GO_begin : GOBJ LIT_BEGIN 12.
Hypothesis GO_tail : GOBJ LIT_TAIL 7.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_post := (pem_post RT libenv errst_live).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keep_n : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP W,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
  In (e_E RT en, 904) KEEP -> (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) -> errst_at_rest (e_E RT en) [] m'.
Proof using errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur KEEP W COM ER PR INK HO. eapply errst_rest_agree; [exact ER|]. intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)]. apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INK| exact R]| exact (HO _ R)].
Qed.

(* [comment removed for export] *)
Lemma gn_keep : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur W j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv KX KY methX methY maxX maxY,
  pem_com en Σ m off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
  (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x) -> (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside W x) ->
  (forall x, e_f RT en <= x < e_f RT en + 120 -> outside W x) ->
  (forall e x, In e (mbio_ent KX maxX) -> fst e <= x < fst e + snd e -> outside W x) -> (forall e x, In e (mbio_ent KY maxY) -> fst e <= x < fst e + snd e -> outside W x) ->
  (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) ->
  (forall e, In e (mbio_ent KX maxX) -> In e cur) -> (forall e, In e (mbio_ent KY maxY) -> In e cur) ->
  errst_at_rest (e_E RT en) [] m -> pem_frame en m j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  out_null RT en m -> mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 ->
     errst_at_rest (e_E RT en) [] m' /\ pem_frame en m' j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap /\ rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)
  /\ out_null RT en m' /\ mbio_rep (rt_live RT Σ) m' KX hBv methX 0 maxX 0 /\ mbio_rep (rt_live RT Σ) m' KY dBv methY 0 maxY 0.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur W j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv KX KY methX methY maxX maxY
         COM PR HWS HWFR HWFF OUTX OUTY OUTE CX CY REST PFR FFC ON MBX MBY.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  split; [exact (rest_keep_n en Σ m m' off crem lrem cur _ W COM REST PR (ELV _ INE) OUTE)|].
  split; [exact (pem_frame_keep RT en m m' _ _ _ j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap PFR PR PD TOP HWS)|].
  split; [exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF)|].
  split.
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m' P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  split; [eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; apply CLV; exact (CX _ He)| exact OUTX]|].
  eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply CLV; exact (CY _ He)| exact OUTY].
Qed.

(* [comment removed for export] *)
Theorem GN1_proof : forall N,
  NAME_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS -> GNG_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N ->
  GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N NAMEP GNGP en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a2 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6
         LB1 hBv dBv len fcall bs KX KY methX methY maxX maxY.
  cbv zeta. intros MEAS COM REST REM LRM PFR FFC ON LBA LBS LBC LEN NULk FC MBX MBY MX0 MY0. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  set (fl := Z.land (e_flags RT en) (Z.lnot 4)) in *. pose proof (land_lnot4_bound (e_flags RT en) FLR) as FLB. change (Z.land (e_flags RT en) (Z.lnot 4)) with fl in FLB.
  assert (INL : In (LB1, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (CX : forall e, In e (mbio_ent KX maxX) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (intros e He; apply in_or_app; left; exact He).
  assert (CY : forall e, In e (mbio_ent KY maxY) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (intros e He; apply in_or_app; right; apply in_or_app; left; exact He).
  (* [comment removed for export] *)
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB1, 256) COM INL ltac:(cbn; clear; lia)) as (INLB & LBP & LBLO & LBHI & _). cbn [fst snd] in LBP, LBLO, LBHI.
  specialize (LBHI ltac:(clear; lia)).
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite !map_app, !mbio_ent_fst in ND'. cbn [map fst app] in ND'. rewrite <- !app_assoc in ND'. cbn [app] in ND'.
  pose proof (nd_split _ _ ND') as (NDX & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY). apply List.NoDup_cons_iff in ND3. destruct ND3 as [NQL ND4].
  assert (NXL : forall e, In e (mbio_ent KX maxX) -> ~ In e [(LB1, 256)]).
  { intros e He [<-|[]]. pose proof (in_map fst _ _ He) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; right; left; reflexivity. }
  assert (NYL : forall e, In e (mbio_ent KY maxY) -> ~ In e [(LB1, 256)]).
  { intros e He [<-|[]]. pose proof (in_map fst _ _ He) as H1. rewrite mbio_ent_fst in H1. apply (DJY _ H1). left; reflexivity. }
  assert (NEL : ~ In (e_E RT en, 904) [(LB1, 256)]) by (intros [X|[]]; injection X; intros _ EE; apply NQL; left; exact (eq_sym EE)).
  (* [comment removed for export] *)
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ [(LB1, 256)] COM ltac:(intros e [<-|[]]; left; split; [exact INL| cbn; clear; lia])) as WOK1.
  pose proof WOK1 as (HWS1 & HWFR1 & HWFF1 & HWF1 & HWL1 & HWP1).
  set (W1 := map rng [(LB1, 256)]) in *.
  assert (OUTX1 : forall e x, In e (mbio_ent KX maxX) -> fst e <= x < fst e + snd e -> outside W1 x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W1 COM HWL1 e x (CX _ He) (NXL _ He) Hx). }
  assert (OUTY1 : forall e x, In e (mbio_ent KY maxY) -> fst e <= x < fst e + snd e -> outside W1 x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W1 COM HWL1 e x (CY _ He) (NYL _ He) Hx). }
  assert (OUTE1 : forall x, e_E RT en <= x < e_E RT en + 904 -> outside W1 x) by (intros x Hx; exact (HWL1 (e_E RT en) 904 x (ELV _ INE) NEL Hx)).
  (* [comment removed for export] *)
  pose proof (gn_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 (wz len) a2 (wz fcall) a4 a5 a6 a7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                (wz LIT_TAIL) s7 (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) t3 t4 t5 t6 F fc m MI) as W0.
  cl_lift W0 HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1.
  eapply (pem_call_san RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_SAN T en Σ m off crem lrem _ LB1 len fl fcall bs SITE_gn_san
            F fc u0 u1 u2 b4 b5 b6 b7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 (wz fl) (wz (LB1 - 6)) u3 u4 u5 u6 c1
            COM INL LBA LBS LBC NULk LEN ltac:(clear - FLB; lia) ltac:(clear - FC; lia) ltac:(unfold SITE_gn_san; clear; lia) ltac:(reflexivity) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m1 F1 fc1 y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c1' len' bs' COM1 PR1 LEN' LENLF LBS1 LBC1 NL1 NUL1 Hc1.
  pose proof COM1 as (_ & MI1 & _).
  destruct (gn_keep en Σ m m1 off crem lrem _ W1 j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv KX KY methX methY maxX maxY
              COM PR1 HWS1 HWFR1 HWFF1 OUTX1 OUTY1 OUTE1 CX CY REST PFR FFC ON MBX MBY) as (REST1 & PFR1 & FFC1 & ON1 & MBX1 & MBY1).
  clear PR1 REST PFR FFC ON MBX MBY LBC.
  (* [comment removed for export] *)
  pose proof (gn_c1_walk (wz SITE_gn_san) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) (wz len') b1 b2 b3 d4 d5 d6 d7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                (wz LIT_TAIL) s7 (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) y3 y4 y5 y6 F1 fc1 m1 SP0' SPH MI1) as W0.
  cl_lift W0 Hc1 c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc2'). clear Hc2 Hc1.
  pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as BSL. cbn [cells_bytes cbytes] in BSL. rewrite app_nil_r in BSL.
  pose proof (strncmp_sz_bounds 11 bs' (pem_begin_str ++ [Z_to_bv 8 0]) ltac:(clear; lia)) as SZ1.
  assert (OK1 : strncmp_ok 11 bs' (pem_begin_str ++ [Z_to_bv 8 0])).
  { split; [rewrite LBS1; clear - SZ1; lia| rewrite app_length, pem_begin_len; cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SZ1; lia]. }
  assert (CK1a : checked_src RT Σ m1 (wz (e_sp1 RT en)) (e_lo RT en) LB1 (strncmp_sz 11 bs' (pem_begin_str ++ [Z_to_bv 8 0]))).
  { eapply (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ LB1 256); [exact COM1| exact INL| clear; lia| clear; lia| clear - SZ1; lia| clear - SZ1; lia]. }
  assert (CK1b : checked_src RT Σ m1 (wz (e_sp1 RT en)) (e_lo RT en) LIT_BEGIN (strncmp_sz 11 bs' (pem_begin_str ++ [Z_to_bv 8 0]))).
  { split; [| left; clear - SZ1 HLOS; unfold LIT_BEGIN; lia]. intros _. split.
    - pose proof COM1 as (ART1 & _). apply (afp_acc_global RT GOBJ AFP Σ m1 LIT_BEGIN 12 LIT_BEGIN _ ART1 GO_begin); clear - SZ1; lia.
    - right; right; right. unfold LIT_BEGIN, SEGTOP_A. clear - SZ1. lia. }
  eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m1 off crem lrem _ LB1 LIT_BEGIN 11 bs' (pem_begin_str ++ [Z_to_bv 8 0])
            SITE_gn_snc1 F1 fc1 u0 u1 u2 b3 b4 b5 b6 b7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) (wz len') (wz fl) (wz (LB1 - 6)) u3 u4 u5 u6 c2
            COM1 ltac:(clear; lia) BSL (pem_begin_bytes m1 MI1) OK1 CK1a CK1b ltac:(unfold SITE_gn_snc1; clear; lia) ltac:(reflexivity) Hc2').
  clear Hc2' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c2' COM2 PR2 MI2 Hc2.
  destruct (gn_keep en Σ m1 m2 off crem lrem _ [] j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv KX KY methX methY maxX maxY
              COM1 PR2 ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) CX CY
              REST1 PFR1 FFC1 ON1 MBX1 MBY1) as (REST2 & PFR2 & FFC2 & ON2 & MBX2 & MBY2).
  assert (LBC2 : rw_cells asegs m2 LB1 [CB 256 bs']).
  { eapply rw_cells_agree_nw; [exact LBC1|]. intros a Ha. apply PR2; [| exact I]. apply (acl_live _ _ _ LB1 256); [exact INLB| cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia]. }
  clear PR2 REST1 PFR1 FFC1 ON1 MBX1 MBY1 LBC1.
  set (r1 := strncmp_res 11 bs' (pem_begin_str ++ [Z_to_bv 8 0])) in *.
  destruct (Z.eq_dec r1 0) as [R1Z|R1NZ].
  2: { (* [comment removed for export] *)
    assert (RR : bv_unsigned (Z_to_bv 64 r1) <> 0) by (intros X; apply R1NZ; exact (proj1 (strncmp_reg _ _ _) X)).
    pose proof (gn_c2_walk_ne (wz SITE_gn_snc1) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) r1 e1 e2 e3 e4 e5 e6 e7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1)
                  (wz LIT_TAIL) (wz len') (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) z3 z4 z5 z6 F2 fc2 m2 RR MI2) as W0.
    cl_lift W0 Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2.
    exact (GNGP en Σ m2 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_gn_snc1) z0 z1 z2 (wz r1) e1 e2 e3 e4 e5 e6 e7 s3 (wz len') z3 z4 z5 z6
             LB1 hBv dBv bs' KX KY methX methY maxX maxY MEAS COM2 REST2 REM LRM PFR2 FFC2 ON2 LBA LBS1 LBC2 MBX2 MBY2 MX0 MY0 T c3 Hc3' Hk). }
  assert (RR : bv_unsigned (Z_to_bv 64 r1) = 0) by (rewrite R1Z; reflexivity).
  pose proof (gn_begin_prefix bs' [] ltac:(rewrite LBS1; clear; lia) R1Z) as PFX1.
  destruct (Z_lt_dec len' 6) as [L6|L6].
  { (* [comment removed for export] *)
    pose proof (gn_c2_walk_lt (wz SITE_gn_snc1) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) r1 e1 e2 e3 e4 e5 e6 e7 s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL)
                  len' (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) z3 z4 z5 z6 F2 fc2 m2 RR ltac:(clear - L6 LEN'; lia) MI2) as W0.
    cl_lift W0 Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2.
    exact (GNGP en Σ m2 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_gn_snc1) z0 z1 z2 (wz r1) e1 e2 e3 e4 e5 e6 e7 s3 (wz len') z3 z4 z5 z6
             LB1 hBv dBv bs' KX KY methX methY maxX maxY MEAS COM2 REST2 REM LRM PFR2 FFC2 ON2 LBA LBS1 LBC2 MBX2 MBY2 MX0 MY0 T c3 Hc3' Hk). }
  (* [comment removed for export] *)
  pose proof (gn_c2_walk_go (wz SITE_gn_snc1) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) r1 e1 e2 e3 e4 e5 e6 e7 s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL)
                len' (wz (shad (e_f RT en))) (wz SHB) (wz fl) LB1 z3 z4 z5 z6 F2 fc2 m2 RR ltac:(clear - L6 LEN' LEN; lia) ltac:(clear - LBHI; lia) ltac:(clear - LBLO HLO SPH; unfold e_sp1 in *; lia) MI2) as W0.
  cl_lift W0 Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc3'). clear Hc3 Hc2.
  pose proof (rw_cells_bytes_at _ _ _ _ LBC2) as BSL2. cbn [cells_bytes cbytes] in BSL2. rewrite app_nil_r in BSL2.
  assert (SFX : bytes_at asegs m2 (LB1 + len' - 6) (skipn (Z.to_nat (len' - 6)) bs')).
  { pose proof BSL2 as X. rewrite <- (firstn_skipn (Z.to_nat (len' - 6)) bs') in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X].
    rewrite firstn_length_le in X by (rewrite LBS1; clear - LEN LEN' L6; lia). replace (LB1 + Z.of_nat (Z.to_nat (len' - 6))) with (LB1 + len' - 6) in X by (clear - L6; lia). exact X. }
  assert (SFL : length (skipn (Z.to_nat (len' - 6)) bs') = (256 - Z.to_nat (len' - 6))%nat) by (rewrite skipn_length, LBS1; reflexivity).
  pose proof (strncmp_sz_bounds 6 (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0]) ltac:(clear; lia)) as SZ2.
  assert (OK2 : strncmp_ok 6 (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0])).
  { split; [rewrite SFL; clear - SZ2 LEN LEN' L6; lia| rewrite app_length, pem_tail6_len; cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SZ2; lia]. }
  assert (CK2a : checked_src RT Σ m2 (wz (e_sp1 RT en)) (e_lo RT en) (LB1 + len' - 6) (strncmp_sz 6 (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0]))).
  { eapply (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ LB1 256); [exact COM2| exact INL| clear; lia| clear - L6; lia| clear - SZ2 LEN LEN'; lia| clear - SZ2; lia]. }
  assert (CK2b : checked_src RT Σ m2 (wz (e_sp1 RT en)) (e_lo RT en) LIT_TAIL (strncmp_sz 6 (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0]))).
  { split; [| left; clear - SZ2 HLOS; unfold LIT_TAIL; lia]. intros _. split.
    - pose proof COM2 as (ART2 & _). apply (afp_acc_global RT GOBJ AFP Σ m2 LIT_TAIL 7 LIT_TAIL _ ART2 GO_tail); clear - SZ2; lia.
    - right; right; right. unfold LIT_TAIL, SEGTOP_A. clear - SZ2. lia. }
  eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m2 off crem lrem _ (LB1 + len' - 6) LIT_TAIL 6
            (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0])
            SITE_gn_snc2 F2 fc2 u0 u1 u2 e3 b4 b5 b6 b7 (wz 6) (wz (LB1 + len' - 6)) (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) (wz len') (wz fl) (wz (LB1 - 6)) u3 u4 u5 u6 c3
            COM2 ltac:(clear; lia) SFX (pem_tail6_bytes m2 MI2) OK2 CK2a CK2b ltac:(unfold SITE_gn_snc2; clear; lia) ltac:(reflexivity) Hc3').
  clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m3 F3 fc3 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c3' COM3 PR3 MI3 Hc3.
  destruct (gn_keep en Σ m2 m3 off crem lrem _ [] j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv KX KY methX methY maxX maxY
              COM2 PR3 ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) ltac:(intros; exact I) CX CY
              REST2 PFR2 FFC2 ON2 MBX2 MBY2) as (REST3 & PFR3 & FFC3 & ON3 & MBX3 & MBY3).
  assert (LBC3 : rw_cells asegs m3 LB1 [CB 256 bs']).
  { eapply rw_cells_agree_nw; [exact LBC2|]. intros a Ha. apply PR3; [| exact I]. apply (acl_live _ _ _ LB1 256); [exact INLB| cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia]. }
  clear PR3 REST2 PFR2 FFC2 ON2 MBX2 MBY2 LBC2.
  set (r2 := strncmp_res 6 (skipn (Z.to_nat (len' - 6)) bs') (pem_tail6_str ++ [Z_to_bv 8 0])) in *.
  destruct (Z.eq_dec r2 0) as [R2Z|R2NZ].
  - (* [comment removed for export] *)
    assert (RR2 : bv_unsigned (Z_to_bv 64 r2) = 0) by (rewrite R2Z; reflexivity).
    pose proof (gn_tail_prefix (skipn (Z.to_nat (len' - 6)) bs') [] ltac:(rewrite SFL; clear - LEN LEN' L6; lia) R2Z) as PFX2.
    pose proof (pem_begin_tail_17 bs' len' ltac:(clear - L6; lia) ltac:(rewrite LBS1; clear; lia) PFX1 PFX2) as L17.
    pose proof (gn_c3_walk_eq (wz SITE_gn_snc2) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en)) r2 g1 g2 g3 g4 g5 g6 g7 (wz 6) (wz (LB1 + len' - 6)) (wz LIT_BEGIN) (wz LB1)
                  (wz LIT_TAIL) (wz len') (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) w3 w4 w5 w6 F3 fc3 m3 RR2 MI3) as W0.
    cl_lift W0 Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (-> & _) & Hc4'). clear Hc4 Hc3.
    exact (NAMEP en Σ m3 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_gn_snc2) w0 w1 w2 (wz r2) g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6
             LB1 hBv dBv len' bs' KX KY methX methY maxX maxY COM3 REST3 REM LRM PFR3 FFC3 ON3 LBA LBS1 LBC3 ltac:(clear - L17 LEN LEN'; lia) NL1 NUL1 MBX3 MBY3 MX0 MY0 T c4 Hc4' Hk).
  - (* [comment removed for export] *)
    assert (RR2 : bv_unsigned (Z_to_bv 64 r2) <> 0) by (intros X; apply R2NZ; exact (proj1 (strncmp_reg _ _ _) X)).
    pose proof (gn_c3_walk_ne (wz SITE_gn_snc2) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en)) r2 g1 g2 g3 g4 g5 g6 g7 (wz 6) (wz (LB1 + len' - 6)) (wz LIT_BEGIN) (wz LB1)
                  (wz LIT_TAIL) (wz len') (wz (shad (e_f RT en))) (wz SHB) (wz fl) (wz (LB1 - 6)) w3 w4 w5 w6 F3 fc3 m3 RR2 MI3) as W0.
    cl_lift W0 Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (-> & _) & Hc4'). clear Hc4 Hc3.
    exact (GNGP en Σ m3 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_gn_snc2) w0 w1 w2 (wz r2) g1 g2 g3 g4 g5 g6 g7 (wz (LB1 + len' - 6)) (wz len') w3 w4 w5 w6
             LB1 hBv dBv bs' KX KY methX methY maxX maxY MEAS COM3 REST3 REM LRM PFR3 FFC3 ON3 LBA LBS1 LBC3 MBX3 MBY3 MX0 MY0 T c4 Hc4' Hk).
Qed.
End CGn.
