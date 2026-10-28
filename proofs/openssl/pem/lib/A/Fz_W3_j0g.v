(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_ngets Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma land_m5_lnot4 : forall fl, 0 <= fl < 256 -> Z.land fl 18446744073709551611 = Z.land fl (Z.lnot 4).
Proof.
  intros fl Hf. change 18446744073709551611 with ((Z.lnot 4) mod 2 ^ 64). rewrite land_mod_pow2_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition j0g_post (sp1 : Z) (ra gp t0 t1 t2 s0 a4 a5 a6 a7 s3 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (len LB1 f fl : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (a0' a2' : word) (m' : mem),
    ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0' (wz len) a2' (wz 1) a4 a5 a6 a7 (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 s8 s9
                 (wz (Z.land fl (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6) F (wz J_GN) fc None m' (seg_rom asegs)
    /\ munch [(sp1 + 80, sp1 + 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (sp1 + 80) [C8 (wz (f + 48)); C8 (wz (f + 32)); C8 (wz (f + 64))].

(* [comment removed for export] *)
Lemma j0g_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len LB1 f fl : Z)
    (lf : list byte) (c0 c1 c2 c3 c4 c5 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 < 2 ^ 47 -> 0 <= fl < 256 -> 16 <= LB1 -> LB1 + 256 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [CB 24 lf] ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (wz f); C8 (wz fl); C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (j0g_post sp1 ra gp t0 t1 t2 s0 a4 a5 a6 a7 s3 s7 s8 s9 t3 t4 t5 t6 F fc len LB1 f fl m)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz LB1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_J0G) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH F0 FH FL L16 LH MI FRF FRE. unfold J_J0G, TP_A in *.
  pose proof (munch_refl [(sp1 + 80, sp1 + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB1) = LB1) by (apply unsigned_lit; lia).
  do 17 (zstep; lfix).
  unfold j0g_post, J_GN, TP_A, LIT_BEGIN, LIT_TAIL. apply evt_done. do 3 eexists.
  split. { rewrite land_m5_lnot4 by lia. replace (LB1 + -6) with (LB1 - 6) by lia. reflexivity. }
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CJ0g.
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
Hypothesis H_GN : forall N, GN_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Theorem J0G_proof : J0G_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s10 s11 t3 t4 t5 t6
         LB1 hBv dBv len bs KX KY methX methY maxX maxY.
  cbv zeta. intros COM ER0 REM LRM PFR FFC ON AL16 LBS LBC LEN NUL MBX MBY MX0 MY0. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB1, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (FH : e_f RT en + 128 < 2 ^ 47) by (clear - FTOP; unfold USTACK_TOP in FTOP; lia).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB1, 256) COM HLB ltac:(cbn; lia)) as (INL & L0 & LLO & LHI & LNAC). cbn [fst snd] in L0, LLO, LHI, LNAC.
  assert (L16 : 16 <= LB1) by (clear - L0 AL16; Z.div_mod_to_equations; lia).
  assert (LH : LB1 + 256 <= 2 ^ 47) by (clear - LLO HLO SPH; lia).
  pose proof PFR as (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG).
  pose proof (rw_cells_blur m (e_sp1 RT en + 80) lF [] ltac:(rewrite app_nil_r; exact FRF)) as FRFB.
  replace (cells_size lF) with 24%nat in FRFB by (clear - SZF; lia).
  pose proof FRE as FRE'. unfold loc_E in FRE'.
  pose proof (j0g_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6
                F fc m len LB1 (e_f RT en) (e_flags RT en) (cells_bytes lF) _ _ _ _ _ _ _ _ _ _ _ _
                SP0' SPH F0 FH FLR L16 LH MI FRFB FRE') as W1.
  cl_lift W1 HA c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a0' & a2' & m2 & -> & MU2 & WM2 & MI2 & FRF2) & Hc2'). clear Hc2 HA.
  (* [comment removed for export] *)
  set (W2 := [(e_sp1 RT en + 80, e_sp1 RT en + 104)]) in *.
  assert (HW2 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W2 x) by (intros x Hx; subst W2; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
  destruct (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ W2 COM HW2) as (W2L & W2F & W2O).
  assert (KP : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W2 x) -> rw_cells asegs m2 A cs).
  { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU2. exact (HO _ Ha). }
  assert (PR2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) W2 m m2) by (intros a _ Ho; exact (MU2 a Ho)).
  assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)).
  { eapply stk_munch; [exact ST| exact MU2| exact WM2|]. intros x Hx. apply HW2. left. clear - Hx. lia. }
  assert (COM2 : pem_com en Σ m2 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])).
  { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m m2); [exact COM| exact MU2| exact WM2| exact MI2| exact ST2|].
    subst W2. apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd]; unfold e_sp1 in *; clear - PD; lia. }
  assert (REST2 : errst_at_rest (e_E RT en) [] m2).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ m m2); [exact COM| exact ER0| exact PR2| exact (ELV _ INE)| intros x Hx; exact (W2L _ _ x (ELV _ INE) Hx)]. }
  assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { apply (KP _ _ FFC). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W2F. clear - Hx. lia. }
  assert (ON2 : out_null RT en m2).
  { destruct ON as (O1 & O2 & O3 & O4).
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
    { intros P vv HPP C. apply (KP _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W2O P x HPP). clear - Hx. lia. }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX2 : mbio_rep (rt_live RT Σ) m2 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR2| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W2L p n x (CLV _ ltac:(apply in_or_app; left; exact He)) Hx). }
  assert (MBY2 : mbio_rep (rt_live RT Σ) m2 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR2| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W2L p n x (CLV _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
  assert (LBC2 : rw_cells asegs m2 LB1 [CB 256 bs]).
  { apply (KP _ _ LBC). cbn [cells_size csize]. intros x Hx. apply (W2L LB1 256 x (CLV _ HLB)). clear - Hx. lia. }
  assert (PFR2 : pem_frame en m2 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap).
  { split; [apply (KP _ _ FR0); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
    split; [apply (KP _ _ FRH); rewrite SZH; intros x Hx; subst W2; cbn; clear - Hx; lia|]. split; [exact SZH|].
    split; [unfold loc_F; exact FRF2|]. split; [reflexivity|].
    split; [apply (KP _ _ FR104); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
    split; [apply (KP _ _ FRE); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
    split; [apply (KP _ _ FR224); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
    apply (KP _ _ FRG). cbn [cells_size csize]. intros x Hx. subst W2. cbn. clear - Hx PD. lia. }
  clear COM ER0 PFR FFC ON MBX MBY LBC FR0 FRH FRF FR104 FRE FRE' FR224 FRG FRFB KP.
  refine (H_GN (e_blen RT en - off) en Σ m2 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0' a2' a4 a5 a6 a7 (wz dBv) (wz hBv) t3 t4 t5 t6
            LB1 hBv dBv len 1 bs KX KY methX methY maxX maxY ltac:(clear; lia) COM2 REST2 REM LRM PFR2 FFC2 ON2 AL16 LBS LBC2 LEN NUL ltac:(clear; lia)
            MBX2 MBY2 MX0 MY0 T c2 Hc2' Hk).
Qed.
End CJ0g.
