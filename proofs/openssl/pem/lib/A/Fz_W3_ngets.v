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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_ng_gets : Z := 0x30c5f0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ng1_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz SITE_ng_gets) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) c13 s11 (wz 255) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FZ_BIO_GETS) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_NGETS) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH MI FRE. unfold J_NGETS, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  unfold SITE_ng_gets, FZ_BIO_GETS. apply evt_done. do 12 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma ng2_walk0 : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 854) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_ng_gets) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_ng_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. if_true.
  unfold J_RAISE2. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Definition ng2_post (sp1 : Z) (gp s0 s3 s8 s9 s10 c4 : word) (F : bvmap 5 word) (fc : bv 32) (k LB2 : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 c4 s3 (wz 0) (wz k) (wz 0) (wz 0) s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz J_HD) fc None m' (seg_rom asegs)
    /\ munch [(sp1 + 24, sp1 + 80); (sp1 + 104, sp1 + 112)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (sp1 + 24) [C8 (wz (Z.land (LB2 + 253) 7)); C8 (wz (Z.land LB2 7)); C8 c4; C8 (wz (shad (LB2 + 253))); C8 (wz (LB2 + 253)); C8 (wz (shad LB2)); C8 (wz LIT_ENDSTR)]
    /\ rw_cells asegs m' (sp1 + 104) [C8 (wz 0)].
Lemma ng2_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (k LB2 : Z) (endv : word)
    (hh : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 1 <= k <= 254 -> 0 < LB2 -> LB2 + 256 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 24) [CB 56 hh] -> rw_cells asegs m (sp1 + 104) [C8 endv] ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (ng2_post sp1 gp s0 s3 s8 (wz SHB) s10 c4 F fc k LB2 m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_ng_gets) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH HK HL0 HLH MI FRH FR104 FRE. unfold SITE_ng_gets, TP_A, SHB in *.
  pose proof (munch_refl [(sp1 + 24, sp1 + 80); (sp1 + 104, sp1 + 112)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB2) = LB2) by (apply unsigned_lit; lia).
  zstep. zstep.
  replace (negb (bv_lts Startup_glue.z64 (Z_to_bv 64 k))) with false by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Bool.negb_false_iff; apply Z.ltb_lt; lia). cbv iota.
  do 24 (zstep; lfix).
  unfold ng2_post, J_HD. apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *. unfold shad, SHB. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mbio_ent_len0 : forall live (m : mem) K BI meth len off, mbio_rep live m K BI meth len 0 off -> length (mbio_ent K 0) = 4%nat.
Proof.
  intros live m K BI meth len off (BM & fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MT)).
  unfold mbio_ent. destruct (k_d K) as [d|]; [destruct MT as (junk & _ & POS & _); exfalso; clear - POS; lia| rewrite app_nil_r; reflexivity].
Qed.

Section CNgets.
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
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_BG : bio_gets_stmt RT.
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_HD : forall N, HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
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
Lemma stk_win_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur (W : list (Z * Z)),
  pem_com en Σ m off crem lrem cur -> (forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W x) ->
     (forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> outside W x)
  /\ (forall x, e_f RT en <= x < e_f RT en + 128 -> outside W x)
  /\ (forall P x, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> P <= x < P + 8 -> outside W x).
Proof using AF AFP.
  intros en Σ m off crem lrem cur W COM HW.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  split. { intros p n x Hin Hx. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & R & _). apply HW. left. clear - R Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia. }
  split. { intros x Hx. pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & R & _). change (fs_size 1) with 128 in R. apply HW. left.
           clear - R Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia. }
  intros P x HP Hx. assert (HL : pp_loc (e_frames RT en) (e_m RT en) USTACK_TOP P) by exact (proj2 (proj1 (Forall_forall _ _) OUTS P HP)).
  destruct HL as [[H1 H2]|(f & k & Hin & H1 & H2 & _)].
  - exfalso. clear - H1 H2. unfold USTACK_TOP in *. lia.
  - assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin). pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & R & _).
    apply HW. left. clear - R H1 H2 Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
Qed.

Theorem NGETS_proof : NGETS_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6
         LB2 namev nn hBv dBv bn junk KX KY methX methY maxX maxY.
  cbv zeta. intros COM ER0 REM LRM PFR FFC ON AL16 LBS LBC NAL NNR LBN NBC NIN MBX MBY MX0 MY0. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HNB : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) COM
                ltac:(intros e [<-|He]; [left; split; [exact HLB| cbn; clear; lia]| right; exact He])) as WOK.
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
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
  assert (OUTX : forall e x, In e (mbio_ent KX maxX) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; left; exact He) (NXL _ He) Hx). }
  assert (OUTY : forall e x, In e (mbio_ent KY maxY) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NYL _ He) Hx). }
  assert (OUTN : forall x, namev <= x < namev + nn -> outside W x).
  { intros x Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL (namev, nn) x HNB NNL Hx). }
  assert (OUTE : forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x).
  { intros x Hx. exact (HWL (e_E RT en) 904 x (ELV _ INE) NEL Hx). }
  assert (G255 : 255 < gr_n (0 + 255)) by (apply gr_n_gt; clear; lia).
  assert (GP0 : 0 <= grow_pot RT en 0 0) by (apply (grow_pot_nonneg RT en 0 0 0 0 off OFF); clear - G255 OFF; lia).
  assert (CR1 : 1 <= crem) by (clear - REM GP0 OFF BLT; unfold gn_need, C_END in REM; lia).
  (* [comment removed for export] *)
  pose proof (ng1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                t3 t4 t5 t6 F fc m _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH MI FRE) as W0.
  cl_lift W0 HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1.
  eapply (pem_call_bgets RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BG T en Σ m off crem lrem _ LB2 junk SITE_ng_gets
            F fc u0 u1 u2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) u3 u4 u5 u6 c1
            COM HLB AL16 LBS LBC CR1 ltac:(unfold SITE_ng_gets; clear; lia) ltac:(reflexivity) Hc1').
  clear Hc1' u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' k off' bs' COM' LV' FRS' PR LBS' LBC' ARMS Hc'.
  pose proof COM' as (ART' & MI' & ST' & _ & _ & _ & LOW' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OFF' & _).
  change ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) with W in PR.
  assert (INF' : In (e_f RT en, 1%nat) (rt_frames RT Σ')) by (rewrite FRS'; exact INF).
  (* [comment removed for export] *)
  assert (REST' : errst_at_rest (e_E RT en) [] m').
  { eapply (rest_keep_n en Σ m m'); [exact COM| exact ER0| exact PR| rewrite LV'; exact (ELV _ INE)| exact OUTE]. }
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
  assert (NBC' : rw_cells asegs m' namev [CB (Z.to_nat nn) bn]).
  { eapply (cells_keep m m' namev nn); [exact NBC| exact PR| rewrite LV'; exact (CLV _ HNB)| clear; lia| cbn [cells_size csize]; clear - NNR; lia|].
    cbn [cells_size csize]. intros x Hx. apply OUTN. clear - Hx NNR. lia. }
  clear PFR FFC ON MBX MBY NBC ER0.
  destruct ARMS as [(-> & -> & OFE)|(KR & NULk & LFk & ->)].
  - (* [comment removed for export] *)
    pose proof (ng2_walk0 (wz SITE_ng_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 d4 d5 d6 d7 s2 s3 s4 s5
                  s6 s7 (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) y3 y4 y5 y6 F' fc' m' MI') as W1.
    cl_lift W1 Hc' c2 Hc2. destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc'.
    refine (H_R2 en Σ' m' off (crem - 1) lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' (wz SITE_ng_gets) y0 y1 y2 (wz 0) b1 b2 b3 d4 d5 d6 d7
              s3 s4 s5 s6 s7 y3 y4 y5 y6 LB2 namev nn hBv dBv 854 bn bs' KX KY methX methY 0 maxX 0 maxY
              COM' REST' _ ltac:(clear - LRM; lia) ltac:(clear; lia) PFR' FFC' ON' AL16 LBS' LBC' NAL NNR LBN NBC' MBX' MBY' T c2 Hc2' Hk).
    clear - REM OFF. unfold gn_need, C_END, grow_pot, grow_cap, e_plen in *. pose proof (gr_n_gt (2 * (e_blen RT en - e_boff RT en) + 8) ltac:(lia)) as G1. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ' m' (off + k) (crem - 1) lrem _ (LB2, 256) COM' HLB ltac:(cbn; lia)) as (INL & L0 & LLO & LHI & LNAC). cbn [fst snd] in L0, LLO, LHI, LNAC.
    pose proof PFR' as (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE' & FR224 & FRG). unfold loc_E in FRE'.
    pose proof (rw_cells_blur m' (e_sp1 RT en + 24) lH [] ltac:(rewrite app_nil_r; exact FRH)) as FRHB.
    replace (cells_size lH) with 56%nat in FRHB by (clear - SZH; lia).
    pose proof (ng2_walk (wz SITE_ng_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 d4 d5 d6 d7 s2 s3 s4 s5
                  s6 s7 (wz (shad (e_f RT en))) (wz namev) y3 y4 y5 y6 F' fc' m' k LB2 endv (cells_bytes lH) _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  SP0' SPH ltac:(clear - KR; lia) L0 ltac:(clear - LLO HLO; lia) MI' FRHB FR104 FRE') as W1.
    cl_lift W1 Hc' c2 Hc2.
    destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (ra' & e0 & e1 & e2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & e3 & e4 & e5 & e6 & m2 & -> & MU2 & WM2 & MI2 & FRH2 & FR1042) & Hc2'). clear Hc2 Hc'.
    (* [comment removed for export] *)
    set (W2 := [(e_sp1 RT en + 24, e_sp1 RT en + 80); (e_sp1 RT en + 104, e_sp1 RT en + 112)]) in *.
    assert (HW2 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W2 x) by (intros x Hx; subst W2; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
    destruct (stk_win_facts en Σ' m' (off + k) (crem - 1) lrem _ W2 COM' HW2) as (W2L & W2F & W2O).
    assert (KP : forall A cs, rw_cells asegs m' A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W2 x) -> rw_cells asegs m2 A cs).
    { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU2. exact (HO _ Ha). }
    assert (PR2 : rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ') (e_sp1 RT en) W2 m' m2) by (intros a _ Ho; exact (MU2 a Ho)).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ' m' (off + k) (crem - 1) lrem _ COM') as [ELV' CLV'].
    assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)).
    { eapply stk_munch; [exact ST'| exact MU2| exact WM2|]. intros x Hx. apply HW2. left. clear - Hx. lia. }
    assert (COM2 : pem_com en Σ' m2 (off + k) (crem - 1) lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])).
    { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ' m' m2); [exact COM'| exact MU2| exact WM2| exact MI2| exact ST2|].
      subst W2. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; left; cbn [fst snd]; unfold e_sp1 in *; clear - PD; lia. }
    assert (REST2 : errst_at_rest (e_E RT en) [] m2).
    { eapply (rest_keep_n en Σ' m' m2); [exact COM'| exact REST'| exact PR2| exact (ELV' _ INE)| intros x Hx; exact (W2L _ _ x (ELV' _ INE) Hx)]. }
    assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
    { apply (KP _ _ FFC'). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W2F. clear - Hx. lia. }
    assert (ON2 : out_null RT en m2).
    { destruct ON' as (O1 & O2 & O3 & O4).
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m' P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
      { intros P vv HPP C. apply (KP _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W2O P x HPP). clear - Hx. lia. }
      split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
    assert (MBX2 : mbio_rep (rt_live RT Σ') m2 KX hBv methX 0 maxX 0).
    { eapply (mbio_rep_keep (rt_live RT Σ')); [exact MBX'| exact PR2| intros e He; split; apply CLV'; apply in_or_app; left; exact He|].
      intros [p n] x He Hx. exact (W2L p n x (CLV' _ ltac:(apply in_or_app; left; exact He)) Hx). }
    assert (MBY2 : mbio_rep (rt_live RT Σ') m2 KY dBv methY 0 maxY 0).
    { eapply (mbio_rep_keep (rt_live RT Σ')); [exact MBY'| exact PR2| intros e He; split; apply CLV'; apply in_or_app; right; apply in_or_app; left; exact He|].
      intros [p n] x He Hx. exact (W2L p n x (CLV' _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
    assert (LBC2 : rw_cells asegs m2 LB2 [CB 256 bs']).
    { apply (KP _ _ LBC'). cbn [cells_size csize]. intros x Hx. apply (W2L LB2 256 x (CLV' _ HLB)). clear - Hx. lia. }
    assert (NBC2 : rw_cells asegs m2 namev [CB (Z.to_nat nn) bn]).
    { apply (KP _ _ NBC'). cbn [cells_size csize]. intros x Hx. apply (W2L namev nn x (CLV' _ HNB)). clear - Hx NNR. lia. }
    assert (PFR2 : pem_frame en m2 j0 (loc_H LB2 hBv) (loc_F RT en) (wz 0) hBv dBv x1 x2 gap).
    { split; [apply (KP _ _ FR0); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      split; [unfold loc_H; exact FRH2|]. split; [reflexivity|].
      split; [apply (KP _ _ FRF); rewrite SZF; intros x Hx; subst W2; cbn; clear - Hx; lia|]. split; [exact SZF|].
      split; [exact FR1042|].
      split; [apply (KP _ _ FRE'); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      split; [apply (KP _ _ FR224); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      apply (KP _ _ FRG). cbn [cells_size csize]. intros x Hx. subst W2. cbn. clear - Hx PD. lia. }
    clear COM' REST' PFR' FFC' ON' MBX' MBY' LBC' NBC' FR0 FRH FRF FR104 FRE' FR224 FRG FRHB KP.
    refine (H_HD (e_blen RT en - (off + k)) en Σ' m2 (off + k) (crem - 1) lrem j0 (wz 0) (wz 0) x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' ra' e0 e1 e2 g0 g1 g2 g3 g4 g5 g6 g7 s3 e3 e4 e5 e6
              LB2 namev nn hBv dBv hBv k 0 0 bn bs' KX KY methX methY 0 maxX 0 maxY ltac:(clear; lia) _ ltac:(clear - KR; lia) NULk ltac:(clear; lia)
              ltac:(intros A1 A2; apply LFk; clear - A1 A2 KR; lia) ltac:(clear - OFF; lia) T c2 Hc2' Hk).
    unfold hd_inv. cbv zeta.
    split; [exact COM2|]. split; [exact REST2|]. split; [subst maxX maxY; unfold hd_need, gn_need in *; clear - REM KR; lia|].
    split; [pose proof MBX2 as MBXz; pose proof MBY2 as MBYz; rewrite MX0 in MBXz |- *; rewrite MY0 in MBYz |- *; rewrite (mbio_ent_len0 _ _ _ _ _ _ _ MBXz), (mbio_ent_len0 _ _ _ _ _ _ _ MBYz); clear - LRM; cbn; lia|].
    split; [exact PFR2|]. split; [exact FFC2|]. split; [exact ON2|].
    split; [exact AL16|]. split; [exact LBS'|]. split; [exact LBC2|].
    split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC2|]. split; [exact NIN|].
    split; [exact MBX2|]. split; [exact MBY2|].
    split; [clear; lia|]. split; [intros _; repeat split; try reflexivity; exact MY0|]. split; [intros X; exfalso; clear - X; lia|]. split; [left; reflexivity|].
    split; [clear - OFF KR; lia|]. subst maxX maxY. split; (eapply Z.le_trans; [| apply Z.lt_le_incl, gr_n_gt; clear; lia]); clear; lia.
Qed.
End CNgets.
