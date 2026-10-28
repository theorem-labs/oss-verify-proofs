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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_endl Fz_W3_ngets Fz_W3_hd1 Fz_W3_hdg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition SITE_hd2_san : Z := 0x30c6e4.    (* [comment removed for export] *)
Definition SITE_hd2_snc : Z := 0x30c718.    (* [comment removed for export] *)
Definition SITE_hd2_blank : Z := 0x30c790.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hd2_a_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len LB2 : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_hd2_san) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz LB2) (wz len) a2 (wz 0) a4 a5 a6 a7 s2 s3 s4 (wz len) s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6)
                               F (wz FZ_SANITIZE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz len) s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz J_HD2) fc None m (seg_rom asegs)).
Proof.
  intros until LB2. intros MI. unfold J_HD2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  unfold SITE_hd2_san, FZ_SANITIZE. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Definition hd2_b_post (sp1 : Z) (gp s0 s2 s4 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (len' LB2 : Z) (b0 : byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (bv_unsigned b0 = 10 /\
     ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz len') s4 s5 s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_hd2_blank) fc None m (seg_rom asegs))
    \/ (bv_unsigned b0 <> 10 /\
     ms = MS (mkR (wz SITE_hd2_snc) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz LB2) (wz LIT_ENDSTR) (wz 9) a3 a4 a5 a6 a7 s2 (wz len') s4 s5 s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6)
             F (wz e_icpt_strncmp) fc None m (seg_rom asegs)).
Lemma hd2_b_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len' LB2 tmp : Z) (b0 : byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 1 <= len' <= 255 -> 0 < LB2 -> LB2 + 256 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 24) (loc_H LB2 tmp) ->
  ro_cells asegs m (shad LB2) [C1 (Z_to_bv 8 0)] ->
  ov_read_bytes asegs m (Z_to_bv 64 LB2) 1%nat = Some [b0] ->
  evt asegs (hd2_b_post sp1 gp s0 s2 s4 s5 s6 s7 s8 s9 s10 F fc len' LB2 b0 m)
    (MS (mkR (wz SITE_hd2_san) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz len') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_hd2_san) fc None m (seg_rom asegs)).
Proof.
  intros until b0. intros SP0 SPH LEN HL0 HLH MI FRH ROsh RD. unfold SITE_hd2_san, TP_A, loc_H in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB2) = LB2) by (apply unsigned_lit; lia).
  pose proof (bv_unsigned_in_range _ b0) as BR. change (bv_modulus 8) with 256 in BR.
  zstep. zstep. cbv beta. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. zstep. if_false.
  zstep. zstep. zstep. if_cases K; zify_cond K.
  - unfold hd2_b_post, SITE_hd2_blank. apply evt_done. do 16 eexists. left. split; [exact K| reflexivity].
  - zstep. zstep. zstep. zstep. zstep.
    unfold hd2_b_post, SITE_hd2_snc, e_icpt_strncmp, LIT_ENDSTR. apply evt_done. do 16 eexists. right. split; [exact K| reflexivity].
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

(* [comment removed for export] *)
Lemma hd2_c_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (r : Z),
  -1 <= r <= 1 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz (if r =? 0 then J_ENDLINE else J_PUTS)) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd2_snc) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros RR MI. unfold SITE_hd2_snc, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (Hr : r = 0 \/ r = 1 \/ r = -1) by lia. clear RR. destruct Hr as [-> |[-> | ->]].
  all: zstep; th_if_lit; unfold J_ENDLINE, J_PUTS; cbn [Z.eqb Pos.eqb]; apply evt_done; split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma hd2_k1_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (got : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => exists a0', ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0' a1 a2 a3 a4 a5 a6 a7 (wz got) s3 (wz 1) s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz J_GETS2) fc None m (seg_rom asegs))
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz 1) s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd2_blank) fc None m (seg_rom asegs)).
Proof.
  intros until got. intros MI. unfold SITE_hd2_blank, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. th_if_lit. zstep. zstep.
  unfold J_GETS2. apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hd2_k0_post (sp1 : Z) (gp s0 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (got LB2 dBv : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 (if got =? 2 then wz 883 else wz 2) s3 (wz 0) s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz (if got =? 2 then J_RAISE2 else J_GETS2)) fc None m' (seg_rom asegs)
    /\ munch [(sp1 + 40, sp1 + 48)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' (sp1 + 24) (loc_H LB2 dBv).
Lemma hd2_k0_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (got LB2 tmp : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word) (dBv : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= got <= 2 -> c5 = wz dBv -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 24) (loc_H LB2 tmp) ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (hd2_k0_post sp1 gp s0 s3 s5 s7 s8 s9 s10 s11 F fc got LB2 dBv m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz 0) s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd2_blank) fc None m (seg_rom asegs)).
Proof.
  intros until dBv. intros SP0 SPH GOT -> MI FRH FRE. unfold SITE_hd2_blank, TP_A, loc_H in *.
  pose proof (munch_refl [(sp1 + 40, sp1 + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 got) = got) by (apply unsigned_lit; lia).
  zstep. zstep. th_if_lit. zstep. zstep. zstep. lfix.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *) zstep. zstep. replace got with 2 by lia. unfold hd2_k0_post, J_RAISE2. cbn [Z.eqb Pos.eqb]. apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
  - unfold hd2_k0_post, J_GETS2. replace (got =? 2) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CHd2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_SAN : sanitize_line_stmt RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis GO_end : GOBJ LIT_ENDSTR LIT_ENDSTR_SZ.
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
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).
Local Notation hd_keepI := (hd_keepW RT AF GOBJ AFP libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).
Local Notation icpt_keepI := (icpt_keep RT AF GOBJ AFP libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).
Local Notation rest_keepI := (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).
Local Notation stk_winI := (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS).

Lemma land_lnot4_bound : forall f, 0 <= f < 256 -> 0 <= Z.land f (Z.lnot 4) < 256.
Proof.
  intros f Hf. pose proof (proj2 (Z.land_nonneg f (Z.lnot 4)) (or_introl (proj1 Hf))) as H1.
  assert (H4 : 0 <= 4) by lia. pose proof (proj2 (Z.land_nonneg f 4) (or_intror H4)) as H2. rewrite <- Z.sub_land_same_l in H1 |- *. lia.
Qed.

Theorem HD2_proof : forall N,
  ENDLINE_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N -> GETS2_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N ->
  PUTS_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N -> HD2_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N ENDLP G2P PUTSP en Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp len got prev partial mask bn bs KX KY methX methY lenX maxX lenY maxY.
  intros MEAS INV LEN NULk PREV PARTIAL MASK LFH INVW. unfold pem_at, cps. intros T c HA Hk.
  pose proof INV as (COM & REST & REM & LRM & PFR & FFC & ON & AL16 & LBS & LBC & NAL & NNR & LBN & NBC & NIN & MBX & MBY & GOT & GLT & GE2 & ENDV & LSUM & MXB & MYB).
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HNB : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB2, 256) COM HLB ltac:(cbn; lia)) as (INL & L0 & LLO & LHI & LNAC). cbn [fst snd] in L0, LLO, LHI, LNAC.
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite !map_app, !mbio_ent_fst in ND'. cbn [map fst app] in ND'. rewrite <- !app_assoc in ND'. cbn [app] in ND'.
  pose proof (nd_split _ _ ND') as (NDX & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY).
  apply List.NoDup_cons_iff in ND3. destruct ND3 as [NQL ND4]. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NQN _].
  assert (NXL : forall e, In e (mbio_ent KX maxX) -> ~ In e [(LB2, 256)]).
  { intros e He [<-|[]]. pose proof (in_map fst _ _ He) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; right; left; reflexivity. }
  assert (NYL : forall e, In e (mbio_ent KY maxY) -> ~ In e [(LB2, 256)]).
  { intros e He [<-|[]]. pose proof (in_map fst _ _ He) as H1. rewrite mbio_ent_fst in H1. apply (DJY _ H1). left; reflexivity. }
  assert (NNL : ~ In (namev, nn) [(LB2, 256)]) by (intros [X|[]]; injection X; intros _ EE; apply NQL; left; exact (eq_sym EE)).
  assert (NEL : ~ In (e_E RT en, 904) [(LB2, 256)]) by (intros [X|[]]; injection X; intros _ EE; apply NQL; right; left; exact (eq_sym EE)).
  assert (MB8 : 0 <= mask < 2 ^ 32) by (destruct MASK as [-> | ->]; [clear - FLR; lia| pose proof (land_lnot4_bound _ FLR); clear - H; lia]).
  (* [comment removed for export] *)
  pose proof (hd2_a_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 (wz mask) a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev)
                t3 t4 t5 t6 F fc m len LB2 MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1 HA.
  eapply (pem_call_san RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_SAN T en Σ m off crem lrem _ LB2 len mask 0 bs SITE_hd2_san F fc
            t0 t1 t2 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz len) (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6 c1
            COM HLB AL16 LBS LBC NULk LEN MB8 ltac:(clear; lia) ltac:(unfold SITE_hd2_san; clear; lia) eq_refl Hc1').
  clear Hc1'. intros m1 F1 fc1 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 len' bs' COM1 PR1 LEN' LEN2 LBS1 LBC1 NL1 NUL1 Hc2.
  pose proof COM1 as (ART1 & MI1 & _).
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ [(LB2, 256)] COM ltac:(intros e [<-|[]]; left; split; [exact HLB| cbn; clear; lia])) as WOK.
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP). cbn [map rng fst snd] in HWL.
  destruct (hd_keepI en Σ m m1 off crem lrem _ _ _ _ j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv namev nn bn COM WOK PR1 (ELV _ INE) (CLV _ HNB) NEL HNB NNL ltac:(clear - NNR; lia) REST PFR FFC ON NBC)
    as (REST1 & PFR1 & FFC1 & ON1 & NBC1).
  assert (MBX1 : mbio_rep (rt_live RT Σ) m1 KX hBv methX lenX maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR1| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL e x ltac:(apply in_or_app; left; exact He) (NXL _ He) Hx). }
  assert (MBY1 : mbio_rep (rt_live RT Σ) m1 KY dBv methY lenY maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR1| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NYL _ He) Hx). }
  clear REST PFR FFC ON NBC MBX MBY LBC PR1 WOK HWS HWFR HWFF HWF HWL HWP.
  pose proof PFR1 as (_ & FRH1 & _ & _ & _ & _ & FRE1 & _).
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ m1 LB2 256 ART1 INL) as [_ LACC1].
  assert (ROsh : ro_cells asegs m1 (shad LB2) [C1 (Z_to_bv 8 0)]).
  { unfold shad, SHB. apply (acc_shadow0 m1 LB2 256 LB2 LACC1); clear - AL16 L0; [Z.div_mod_to_equations; lia| lia| lia|]. rewrite Z.sub_diag. cbn. lia. }
  destruct (nth_error bs' 0%nat) as [b0|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; rewrite LBS1 in Hb; clear - Hb; lia].
  pose proof (u8arr_read asegs m1 LB2 bs' 0 b0 (Z_to_bv 64 LB2) (u8arr_of_rw_cells _ _ _ _ _ LBC1) Hb ltac:(clear; lia) ltac:(symmetry; rewrite Z.add_0_r; apply wa_of_Z_to_bv; clear - L0 LLO HLO SPH; lia)) as RD.
  pose proof (hd2_b_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 b4 b5 b6 b7 (wz tmp) s3 (wz prev) (wz len) (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev)
                y3 y4 y5 y6 F1 fc1 m1 len' LB2 tmp b0 SP0' SPH ltac:(clear - LEN LEN'; lia) L0 ltac:(clear - LLO HLO; lia) MI1 FRH1 ROsh RD) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (ra' & z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & [[B0 ->]|[NB0 ->]]) & Hc3'); clear Hc3 Hc2 RD ROsh.
  - (* [comment removed for export] *)
    destruct (Z.eq_dec prev 0) as [P0|P1].
    + (* [comment removed for export] *)
      subst prev.
      pose proof (hd2_k0_walk ra' (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e0 e1 e2 e3 e4 e5 e6 e7 (wz tmp) (wz len') (wz len) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                    z3 z4 z5 z6 F1 fc1 m1 got LB2 tmp _ _ _ _ _ _ _ _ _ _ _ _ _ _ dBv SP0' SPH GOT eq_refl MI1 FRH1 ltac:(unfold loc_E in FRE1; exact FRE1)) as W.
      cl_lift W Hc3' c4 Hc4. destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (ra'' & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & FRH2) & Hc4'). clear Hc4 Hc3'.
      (* [comment removed for export] *)
      set (W2 := [(e_sp1 RT en + 40, e_sp1 RT en + 48)]) in *.
      assert (HW2 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W2 x) by (intros x Hx; subst W2; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
      destruct (stk_winI en Σ m1 off crem lrem _ W2 COM1 HW2) as (W2L & W2F & W2O).
      assert (KP : forall A cs, rw_cells asegs m1 A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W2 x) -> rw_cells asegs m2 A cs).
      { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU2. exact (HO _ Ha). }
      assert (PR2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) W2 m1 m2) by (intros a _ Ho; exact (MU2 a Ho)).
      pose proof COM1 as (_ & _ & ST1 & _).
      assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)).
      { eapply stk_munch; [exact ST1| exact MU2| exact WM2|]. intros x Hx. apply HW2. left. clear - Hx. lia. }
      assert (COM2 : pem_com en Σ m2 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])).
      { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m1 m2); [exact COM1| exact MU2| exact WM2| exact MI2| exact ST2|].
        subst W2. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold e_sp1 in *. clear - PD. lia. }
      assert (REST2 : errst_at_rest (e_E RT en) [] m2).
      { eapply (rest_keepI en Σ m1 m2); [exact COM1| exact REST1| exact PR2| exact (ELV _ INE)| intros x Hx; exact (W2L _ _ x (ELV _ INE) Hx)]. }
      assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
      { apply (KP _ _ FFC1). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W2F. clear - Hx. lia. }
      assert (ON2 : out_null RT en m2).
      { destruct ON1 as (O1 & O2 & O3 & O4).
        assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m1 P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
        { intros P vv HPP C. apply (KP _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W2O P x HPP). clear - Hx. lia. }
        split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|].
        split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
      assert (MBX2 : mbio_rep (rt_live RT Σ) m2 KX hBv methX lenX maxX 0).
      { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX1| exact PR2| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
        intros [p n] x He Hx. exact (W2L p n x (CLV _ ltac:(apply in_or_app; left; exact He)) Hx). }
      assert (MBY2 : mbio_rep (rt_live RT Σ) m2 KY dBv methY lenY maxY 0).
      { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY1| exact PR2| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
        intros [p n] x He Hx. exact (W2L p n x (CLV _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
      assert (LBC2 : rw_cells asegs m2 LB2 [CB 256 bs']).
      { apply (KP _ _ LBC1). cbn [cells_size csize]. intros x Hx. apply (W2L LB2 256 x (CLV _ HLB)). clear - Hx. lia. }
      assert (NBC2 : rw_cells asegs m2 namev [CB (Z.to_nat nn) bn]).
      { apply (KP _ _ NBC1). cbn [cells_size csize]. intros x Hx. apply (W2L namev nn x (CLV _ HNB)). clear - Hx NNR. lia. }
      assert (PFR2 : pem_frame en m2 j0 (loc_H LB2 dBv) (loc_F RT en) endv hBv dBv x1 x2 gap).
      { pose proof PFR1 as (FR0 & _ & _ & FRF & SZF & FR104 & FRE1' & FR224 & FRG).
        split; [apply (KP _ _ FR0); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
        split; [exact FRH2|]. split; [reflexivity|].
        split; [apply (KP _ _ FRF); rewrite SZF; intros x Hx; subst W2; cbn; clear - Hx; lia|]. split; [exact SZF|].
        split; [apply (KP _ _ FR104); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
        split; [apply (KP _ _ FRE1'); unfold loc_E; cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
        split; [apply (KP _ _ FR224); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
        apply (KP _ _ FRG). cbn [cells_size csize]. intros x Hx. subst W2. cbn. clear - Hx PD. lia. }
      clear COM1 REST1 PFR1 FFC1 ON1 MBX1 MBY1 LBC1 NBC1 FRH1 FRE1 KP MU2 WM2 MI1 ST1 ST2.
      destruct (Z.eqb_spec got 2) as [G2|GN2].
      * (* [comment removed for export] *)
        refine (H_R2 en Σ m2 off crem lrem j0 (loc_H LB2 dBv) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F1 fc1 ra'' w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7
                  (wz len') (wz 0) (wz len) (wz got) (wz partial) w3 w4 w5 w6 LB2 namev nn hBv dBv 883 bn bs' KX KY methX methY lenX maxX lenY maxY
                  COM2 REST2 _ ltac:(clear - LRM; lia) ltac:(clear; lia) PFR2 FFC2 ON2 AL16 LBS1 LBC2 NAL NNR LBN NBC2 MBX2 MBY2 T c4 Hc4' Hk).
        pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBX2) as (LX & _). pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBY2) as (LY & _).
        pose proof (grow_pot_nonneg RT en lenX lenY maxX maxY off OFF ltac:(clear - LX; lia) ltac:(clear - LY; lia) LSUM MXB MYB) as GP. clear - REM GP OFF. unfold hd_need, C_END in *. lia.
      * (* [comment removed for export] *)
        refine (G2P en Σ m2 off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F1 fc1 ra'' w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7 (wz len') (wz 0) (wz len) w3 w4 w5 w6
                  LB2 namev nn hBv dBv dBv got 2 partial bn bs' KX KY methX methY lenX maxX lenY maxY MEAS _ PARTIAL GOT ltac:(clear - INVW LEN; destruct (off =? e_blen RT en); lia) T c4 Hc4' Hk).
        unfold hd_inv. cbv zeta.
        split; [exact COM2|]. split; [exact REST2|]. split; [clear - REM; lia|]. split; [exact LRM|].
        split; [exact PFR2|]. split; [exact FFC2|]. split; [exact ON2|].
        split; [exact AL16|]. split; [exact LBS1|]. split; [exact LBC2|].
        split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC2|]. split; [exact NIN|].
        split; [exact MBX2|]. split; [exact MBY2|].
        split; [clear; lia|]. split; [intros X; exfalso; clear - X; lia|]. split; [intros _; reflexivity|]. split; [exact ENDV|].
        split; [exact LSUM|]. split; [exact MXB| exact MYB].
    + (* [comment removed for export] *)
      assert (P1' : prev = 1) by (clear - PREV P1; lia). subst prev.
      pose proof (hd2_k1_walk ra' (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e0 e1 e2 e3 e4 e5 e6 e7 (wz tmp) (wz len') (wz len) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                    z3 z4 z5 z6 F1 fc1 m1 got MI1) as W.
      cl_lift W Hc3' c4 Hc4. destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (a0'' & ->) & Hc4'). clear Hc4 Hc3'.
      refine (G2P en Σ m1 off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F1 fc1 ra' z0 z1 z2 a0'' e1 e2 e3 e4 e5 e6 e7 (wz len') (wz 1) (wz len) z3 z4 z5 z6
                LB2 namev nn hBv dBv tmp got got partial bn bs' KX KY methX methY lenX maxX lenY maxY MEAS _ PARTIAL GOT ltac:(clear - INVW LEN; destruct (off =? e_blen RT en); lia) T c4 Hc4' Hk).
      unfold hd_inv. cbv zeta.
      split; [exact COM1|]. split; [exact REST1|]. split; [clear - REM; lia|]. split; [exact LRM|].
      split; [exact PFR1|]. split; [exact FFC1|]. split; [exact ON1|].
      split; [exact AL16|]. split; [exact LBS1|]. split; [exact LBC1|].
      split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC1|]. split; [exact NIN|].
      split; [exact MBX1|]. split; [exact MBY1|].
      split; [exact GOT|]. split; [exact GLT|]. split; [exact GE2|]. split; [exact ENDV|].
      split; [exact LSUM|]. split; [exact MXB| exact MYB].
  - (* [comment removed for export] *)
    pose proof (strncmp_sz_range 9 bs' (pem_end_str ++ [Z_to_bv 8 0]) ltac:(clear; lia)) as SZ.
    assert (B1 : bytes_at asegs m1 LB2 bs') by (pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as B; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
    assert (OK : strncmp_ok 9 bs' (pem_end_str ++ [Z_to_bv 8 0])) by (unfold strncmp_ok; rewrite LBS1, length_app, pem_end_len; cbn [length]; clear - SZ; lia).
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ LB2 256 LB2 (strncmp_sz 9 bs' (pem_end_str ++ [Z_to_bv 8 0])) COM1 HLB
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SZ; lia) ltac:(clear - SZ; lia)) as CK1.
    assert (CK2 : checked_src RT Σ m1 (wz (e_sp1 RT en)) (e_lo RT en) LIT_ENDSTR (strncmp_sz 9 bs' (pem_end_str ++ [Z_to_bv 8 0]))).
    { split; [| left; unfold LIT_ENDSTR; clear - HLOS SZ; lia]. intros _. split.
      - exact (afp_acc_global RT GOBJ AFP Σ m1 LIT_ENDSTR LIT_ENDSTR_SZ LIT_ENDSTR (strncmp_sz 9 bs' (pem_end_str ++ [Z_to_bv 8 0])) ART1 GO_end ltac:(clear; lia) ltac:(unfold LIT_ENDSTR_SZ; clear - SZ; lia)).
      - right; right; right. unfold LIT_ENDSTR, SEGTOP_A. clear - SZ. lia. }
    eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m1 off crem lrem _ LB2 LIT_ENDSTR 9 bs' (pem_end_str ++ [Z_to_bv 8 0])
              SITE_hd2_snc F1 fc1 z0 z1 z2 e3 e4 e5 e6 e7 (wz tmp) (wz len') (wz prev) (wz len) (wz got) (wz partial) (wz namev) (wz LB2) z3 z4 z5 z6 c3
              COM1 ltac:(clear; lia) B1 (pem_end_bytes m1 MI1) OK CK1 CK2 ltac:(unfold SITE_hd2_snc; clear; lia) eq_refl Hc3').
    clear Hc3'. intros m2 F2 fc2 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c4 COM2 PR2 MI2 Hc4.
    destruct (icpt_keepI en Σ m1 m2 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv bn bs' KX KY methX methY lenX maxX lenY maxY
                COM1 PR2 REST1 PFR1 FFC1 ON1 LBC1 ltac:(clear - NNR; lia) NBC1 MBX1 MBY1) as (REST2 & PFR2 & FFC2 & ON2 & LBC2 & NBC2 & MBX2 & MBY2).
    clear COM1 MI1 REST1 PFR1 FFC1 ON1 LBC1 NBC1 MBX1 MBY1 PR2 B1 OK CK1 CK2 ART1 FRH1 FRE1.
    pose proof (strncmp_res_range 9 bs' (pem_end_str ++ [Z_to_bv 8 0])) as RR.
    set (r := strncmp_res 9 bs' (pem_end_str ++ [Z_to_bv 8 0])) in *.
    pose proof (hd2_c_walk (wz SITE_hd2_snc) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 (wz tmp) (wz len') (wz prev) (wz len)
                  (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) w3 w4 w5 w6 F2 fc2 m2 r ltac:(clear - RR; lia) MI2) as W.
    cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (-> & _) & Hc5'). clear Hc5 Hc4.
    assert (HDI2 : hd_inv RT libenv errst_at_rest FZ_SITES FZ_CALLS en Σ m2 off crem lrem 0 j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs' KX KY methX methY lenX maxX lenY maxY got).
    { unfold hd_inv. cbv zeta.
      split; [exact COM2|]. split; [exact REST2|]. split; [exact REM|]. split; [exact LRM|].
      split; [exact PFR2|]. split; [exact FFC2|]. split; [exact ON2|].
      split; [exact AL16|]. split; [exact LBS1|]. split; [exact LBC2|].
      split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC2|]. split; [exact NIN|].
      split; [exact MBX2|]. split; [exact MBY2|].
      split; [exact GOT|]. split; [exact GLT|]. split; [exact GE2|]. split; [exact ENDV|].
      split; [exact LSUM|]. split; [exact MXB| exact MYB]. }
    destruct (r =? 0) eqn:ER.
    + (* [comment removed for export] *)
      exact (ENDLP en Σ m2 off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_hd2_snc) w0 w1 w2 (wz r) g1 g2 g3 g4 g5 g6 g7 (wz tmp) (wz len') (wz prev) (wz len) (wz partial) w3 w4 w5 w6
               LB2 namev nn hBv dBv tmp len' got prev bn bs' KX KY methX methY lenX maxX lenY maxY HDI2 ltac:(clear - LEN LEN'; lia) NUL1 PREV ltac:(clear - INVW LEN; lia) T c5 Hc5' Hk).
    + (* [comment removed for export] *)
      exact (PUTSP en Σ m2 off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_hd2_snc) w0 w1 w2 (wz r) g1 g2 g3 g4 g5 g6 g7 (wz len) w3 w4 w5 w6
               LB2 namev nn hBv dBv tmp len len' got prev partial bn bs' KX KY methX methY lenX maxX lenY maxY MEAS HDI2 ltac:(clear - LEN LEN'; lia) NL1 NUL1 PREV PARTIAL
               LEN ltac:(clear - LEN'; lia) ltac:(intros A1 A2; apply LEN2; exact (LFH A1 A2)) INVW T c5 Hc5' Hk).
Qed.
End CHd2.
