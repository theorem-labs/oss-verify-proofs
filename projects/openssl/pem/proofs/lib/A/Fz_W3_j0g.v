(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall Bytes.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_ngets Fz_ukit.
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
Definition j0g_post (sp1 : Z) (ra gp t0 t1 t2 s0 a4 a5 a6 a7 s3 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (len LB1 f fl : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m',
    ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (LIT_BEGIN + 1964)) (wz len) (wz (LIT_TAIL + 1940)) (wz 1) a4 a5 a6 a7
                 (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 s8 s9 (wz (Z.land fl (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6)
            F (wz J_GN) fc None m' (seg_rom asegs)
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
  intros until c13. intros SP_LO SP_HI F_LO F_HI FL_RNG LB_LO LB_HI INV0 SLOT_F SLOT_E.
  unfold J_J0G.
  pose proof (munch_refl [(sp1 + 80, sp1 + 104)] m) as MUNCHED. pose proof (wmono_refl asegs m) as WMONO.
  do 17 zstep.
  rewrite (land_m5_lnot4 fl FL_RNG).
  apply evt_done. unfold j0g_post.
  refine (ex_intro _ m0 (conj _ (conj MUNCHED (conj WMONO (conj INV0 SLOT_F))))).
  reflexivity.
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
         LB1 hBv dBv len bs KX KY methX methY maxX maxY cur
         COM REST NEED LIVE_ROOM FRM FAKE ONULL LB_AL BS_LEN BUF LEN_RNG NUL_AT REP_X REP_Y MAXX0 MAXY0.
  pose proof COM as (_ & INV0 & STK0 & PD_CASES & _ & PL_TOP & _ & LO_ROOM & LO_MIN & _ & _ & _ & _ & E_LIVE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F_POS & _ & F_TOP & _ & _ & _ & _ & _ & FLAGS & _ & _ & _ & MSTAB).
  unfold RT_STACK, PEM_CALLEE_STACK in LO_ROOM. unfold USTACK_TOP in PL_TOP, F_TOP.
  assert (LB_OWNED : In (LB1, 256) cur) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  destruct (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur (LB1, 256) COM LB_OWNED ltac:(cbn; lia))
    as (_ & _ & LB_BELOW & LB_HIGH & _).
  cbn [fst snd] in LB_BELOW, LB_HIGH. specialize (LB_HIGH ltac:(lia)).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as (ENTRY_IN_NOW & CUR_IN_NOW).
  destruct FRM as (SL_J0 & SL_H & SZ_H & SL_F & SZ_F & SL_END & SL_E & SL_X & SL_GAP).
  destruct (rw_cells_forget asegs m (e_sp1 RT en + 80) lF SL_F) as (lfj & SL_F_RAW).
  replace (cells_size lF) with 24%nat in SL_F_RAW by lia.
  pose proof SL_E as SL_E_FLAT. unfold loc_E in SL_E_FLAT.
  assert (SP1_LO : 0 <= e_sp1 RT en) by lia.
  assert (SP1_HI : e_sp1 RT en + 368 <= 2 ^ 47) by (unfold e_sp1; lia).
  assert (FRAME_ROOM : e_sp1 RT en + 104 <= e_PL RT en - 104) by (unfold e_sp1; lia).
  assert (F_HI : e_f RT en + 128 < 2 ^ 47) by lia.
  pose proof (j0g_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB)
                s10 s11 t3 t4 t5 t6 F fc m len LB1 (e_f RT en) (e_flags RT en) lfj _ _ _ _ _ _ _ _ _ _ _ _
                SP1_LO SP1_HI F_POS F_HI FLAGS ltac:(lia) ltac:(lia) INV0 SL_F_RAW SL_E_FLAT) as WALK.
  unfold pem_at, cps. intros T c START KONT.
  refine (asta_evt' RT AF Σ (e_PMc RT en) _
            (j0g_post (e_sp1 RT en) xra (e_gp RT en) t0 t1 t2 (e_sp RT en) a4 a5 a6 a7 (wz dBv) (wz hBv) (wz (shad (e_f RT en))) (wz SHB)
                      t3 t4 t5 t6 F fc len LB1 (e_f RT en) (e_flags RT en) m)
            MSTAB _ T c START _).
  { intros ms <-. exact WALK. }
  intros c1 AT_GN.
  destruct (ASTA_unpack RT Σ _ _ c1 AT_GN) as (ms1 & ARRIVED & AT_GN1).
  destruct ARRIVED as (m1 & -> & MUNCHED & WMONO & INV1 & SL_F1).
  assert (NOT_HIT : forall x, ~ (e_sp1 RT en + 80 <= x < e_sp1 RT en + 104) -> outside [(e_sp1 RT en + 80, e_sp1 RT en + 104)] x)
    by (intros x MISS; cbn [outside]; split; [exact MISS | exact I]).
  assert (CARRY : forall A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n ->
                    (forall x, A <= x < A + n -> outside [(e_sp1 RT en + 80, e_sp1 RT en + 104)] x) ->
                    rw_cells asegs m1 A cs).
  { intros A cs n CELLS SIZE AWAY. subst n. apply (rw_cells_agree asegs m m1 A cs CELLS); [|exact WMONO].
    exact (agree_of_munch _ m m1 _ MUNCHED AWAY). }
  destruct (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur [(e_sp1 RT en + 80, e_sp1 RT en + 104)] COM
              ltac:(intros x SIDE; apply NOT_HIT; lia)) as (LIVE_AWAY & FAKE_AWAY & PTR_AWAY).
  assert (COM1 : pem_com en Σ m1 off crem lrem cur).
  { apply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m m1 off crem lrem cur _ COM MUNCHED WMONO INV1).
    - apply (stk_munch _ m m1 _ _ STK0 MUNCHED WMONO). intros x BELOW. apply NOT_HIT. lia.
    - constructor; [|constructor]. unfold seg_ok. left. cbn [fst snd]. lia. }
  assert (REST1 : errst_at_rest (e_E RT en) [] m1).
  { apply (errst_rest_agree m m1 (e_E RT en) [] REST). apply (agree_of_munch _ m m1 _ MUNCHED).
    intros x FP. destruct (errst_fp_where _ _ _ FP) as [IN_E | (p & n & NONE & _)]; [|destruct NONE].
    exact (LIVE_AWAY _ _ x (ENTRY_IN_NOW _ E_LIVE) IN_E). }
  assert (FRM1 : pem_frame en m1 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap).
  { refine (conj (CARRY _ _ 24 SL_J0 eq_refl _) (conj (CARRY _ _ 56 SL_H SZ_H _) (conj SZ_H (conj SL_F1 (conj eq_refl
           (conj (CARRY _ _ 8 SL_END eq_refl _) (conj (CARRY _ _ 112 SL_E eq_refl _) (conj (CARRY _ _ 24 SL_X eq_refl _)
           (CARRY _ _ (e_pd RT en) SL_GAP ltac:(cbn [cells_size csize]; lia) _))))))))); intros x RNG; apply NOT_HIT; lia. }
  assert (FAKE1 : rw_cells asegs m1 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { apply (CARRY _ _ 120 FAKE eq_refl). intros x RNG. apply FAKE_AWAY. lia. }
  assert (ONULL1 : out_null RT en m1).
  { destruct ONULL as (P_N & P_H & P_D & P_L).
    assert (PTR_CELL : forall P, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] ->
                         rw_cells asegs m P [C8 (wz 0)] -> rw_cells asegs m1 P [C8 (wz 0)]).
    { intros P WHICH CELL. apply (CARRY P _ 8 CELL eq_refl). intros x RNG. exact (PTR_AWAY P x WHICH RNG). }
    exact (conj (PTR_CELL _ (or_introl eq_refl) P_N) (conj (PTR_CELL _ (or_intror (or_introl eq_refl)) P_H)
           (conj (PTR_CELL _ (or_intror (or_intror (or_introl eq_refl))) P_D) (PTR_CELL _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) P_L)))). }
  assert (BUF1 : rw_cells asegs m1 LB1 [CB 256 bs]).
  { apply (CARRY _ _ 256 BUF eq_refl). intros x RNG. exact (LIVE_AWAY LB1 256 x (CUR_IN_NOW _ LB_OWNED) RNG). }
  assert (BIO_AWAY : forall K mx, (forall e, In e (mbio_ent K mx) -> In e (rt_live RT Σ)) ->
                       forall x, mbio_fp K mx x -> outside [(e_sp1 RT en + 80, e_sp1 RT en + 104)] x).
  { intros K mx ENTS x ((p, n) & ENT & RNG). exact (LIVE_AWAY p n x (ENTS _ ENT) RNG). }
  assert (REP_X1 : mbio_rep (rt_live RT Σ) m1 KX hBv methX 0 maxX 0).
  { apply (mbio_rep_agree _ m m1 _ _ _ _ _ _ REP_X). apply (agree_of_munch _ m m1 _ MUNCHED).
    apply BIO_AWAY. intros e ENT. exact (mbio_rep_ents _ _ _ _ _ _ _ _ e REP_X ENT). }
  assert (REP_Y1 : mbio_rep (rt_live RT Σ) m1 KY dBv methY 0 maxY 0).
  { apply (mbio_rep_agree _ m m1 _ _ _ _ _ _ REP_Y). apply (agree_of_munch _ m m1 _ MUNCHED).
    apply BIO_AWAY. intros e ENT. exact (mbio_rep_ents _ _ _ _ _ _ _ _ e REP_Y ENT). }
  exact (H_GN (e_blen RT en - off) en Σ m1 off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2
              (wz (LIT_BEGIN + 1964)) (wz (LIT_TAIL + 1940)) a4 a5 a6 a7 (wz dBv) (wz hBv) t3 t4 t5 t6 LB1 hBv dBv len 1 bs KX KY methX methY maxX maxY
              (Z.le_refl _) COM1 REST1 NEED LIVE_ROOM FRM1 FAKE1 ONULL1 LB_AL BS_LEN BUF1 LEN_RNG NUL_AT ltac:(lia) REP_X1 REP_Y1 MAXX0 MAXY0
              T c1 AT_GN1 KONT).
Qed.
End CJ0g.
