(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_atomic Fz_T_once Fz_T_lock Fz_T_local Fz_T_initthread Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_I1_efirst Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_ibasew Fz_I3_ibase Fz_I3_fullw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section ICFull.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_IB : ibase_stmt RT.
Hypothesis C_LS : loadstr_stmt RT GOBJ.
Hypothesis GO_optsdone : GOBJ G_IC_OPTSDONE 8.

Definition ICF_SITES : list (Z * Z) := IB_SITES ++ LS_SITES.
Definition ICF_CALLS : list (Z * Z) := (ONCE_RET_INIT, e_ibase) :: (ONCE_RET_INIT, e_loadstr) :: IB_CALLS ++ LS_CALLS.
(* [comment removed for export] *)
Definition ICF_W (j1 : Z) : list (Z * Z) :=
  [(G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4); (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (TP_A + -96, TP_A + -88)] ++ IB_W j1 (j1 + 1) ++ LS_W (j1 + 2).

(* [comment removed for export] *)
Definition init_crypto_full_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (lb : byte) (canary : word) (nk j1 : Z)
         (w e sh kold oldcb lk0 h0 f0 r0 r1 o1 o2 kold1 kold2 : word) (ib u b0 : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 OPT_LOAD_STRINGS ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 1072 <= bv_unsigned sp ->
  cg_has (rt_cg RT Σ) ICF_SITES ICF_CALLS ->
  (length (rt_frames RT Σ) + 2 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4329 < LIVE_MAX -> 41 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 z64] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 z64] -> rw_cells asegs m G_LS_ONCE [C4 z64] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  rw_cells asegs m G_IC_OPTS_LOCK [C8 o1] -> rw_cells asegs m G_IC_INIT_LOCK [C8 o2] ->
  rw_cells asegs m DTOR_KEY [C4 kold1] -> rw_cells asegs m G_IC_IICL_KEY [C4 kold2] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j1) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j1 = nk /\ w = z64) \/ (j1 = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> j1 + 2 < 128 ->
  rw_cells asegs m (KEYS + 8 * (j1 + 1)) [C8 z64] ->
  rw_cells asegs m G_IC_BASE_INITED [C1 b0] -> rw_cells asegs m G_IC_BASE_RET [C4 r0] ->
  rw_cells asegs m G_LS_RET [C4 r1] -> rw_cells asegs m ERRNO_A [C4 e] ->
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m (KEYS + 8 * (j1 + 2)) [C8 z64] -> rw_cells asegs m (TSD_MAIN + 8 * (j1 + 2)) [C8 z64] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_init_crypto m)))
    (fun c => exists (Σ' : rts RT) (p1 p2 MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
            /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (ICF_W j1) m m'
            /\ cl_env m' lb' canary
            /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]
            /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 2)]
            /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
            /\ rw_cells asegs m' G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ rw_cells asegs m' G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)]
            /\ rw_cells asegs m' p1 (mutex_cells z64 z64) /\ rw_cells asegs m' p2 (mutex_cells z64 z64)
            /\ rw_cells asegs m' DTOR_KEY [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m' G_IC_IICL_KEY [C4 (Z_to_bv 64 (j1 + 1))]
            /\ rw_cells asegs m' (KEYS + 8 * j1) [C8 (Z_to_bv 64 0x1f3fb8)] /\ rw_cells asegs m' (KEYS + 8 * (j1 + 1)) [C8 (Z_to_bv 64 0x529678)]
            /\ rw_cells asegs m' G_IC_BASE_INITED [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
            /\ rw_cells asegs m' ERRNO_A [C4 (sx32 e)]
            /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
            /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 (j1 + 2))] /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 (j1 + 2))]
            /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK_CLEAN)]
            /\ rw_cells asegs m' (TP_A + -150) [C1 u'] /\ rw_cells asegs m' (TSD_MAIN + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]
            /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
            /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 z64 (Z_to_bv 64 P))
            /\ rw_cells asegs m' P [C8 z64; CB 120 (zeros 120)]
            /\ err_statics m' pk lh /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks'
            /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)]) c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ)
       /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 41 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < p1 /\ p1 mod 16 = 0 /\ p1 + 40 < USTACK_TOP /\ 0 < p2 /\ p2 mod 16 = 0 /\ p2 + 40 < USTACK_TOP
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
       /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).

Theorem init_crypto_full_cps : init_crypto_full_stmt.
Proof.
  unfold init_crypto_full_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo lb canary nk j1 w e sh kold oldcb lk0 h0 f0 r0 r1 o1 o2 kold1 kold2 ib u b0
    fdP mstP tpV a0V artA invA callA roomA cgA frA lvA crA posA envA
    cStop cDone cBonce cLsonce cCb cOlk cIlk cDkey cIkey cNext nkR cKlk cK1 cKnk j1Alt j1Top cK2
    cBinit cBret cLsret cErr cMko cMki cMkk cT150 cK3 cTsd3 cEo cEl cEh cEf.
  intros T c atEntry finish.
  subst a0.
  destruct callA as (stkA & loWin & loRoom & spCap & spAl).
  set (U := bv_unsigned sp) in *.
  pose proof (af_sp0_win RT AF Σ m artA) as sp0W.
  pose proof (af_client_consts RT AF Σ m artA) as (_ & shbA & _ & uarA & utA).
  assert (padR : U mod 32 = 0 \/ U mod 32 = 16) by (clear - spAl; Z.div_mod_to_equations; lia).
  remember (U mod 32) as pad eqn:padE.
  assert (loHi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (spHi : U <= 2 ^ 47) by (unfold USTACK_TOP in spCap; lia).
  pose proof (icb_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad OPT_LOAD_STRINGS
                padR (eq_sym padE) ltac:(unfold OPT_LOAD_STRINGS; lia) stkA ltac:(unfold RT_STACK in *; lia) loHi spHi utA shbA uarA invA) as walk0.
  clear padE.
  cl_lift walk0 atEntry c1 at1.
  destruct (ASTA_unpack RT Σ PMc _ c1 at1) as (ms1 & (a1x & a2x & m1 & -> & mu1 & wm1 & inv1 & save1 & padStk1 & lowStk1) & at1'). clear at1.
  assert (eF1 : bv_unsigned (Z_to_bv 64 (U + -96 - pad)) = U + -96 - pad) by (apply unsigned_lit; unfold RT_STACK in *; lia).
  assert (art1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (U - 96) artA ltac:(unfold STACK_WIN, RT_STACK in *; lia)); [|exact wm1].
    intros x xOut. apply mu1. cbn [outside]. split; [|exact I]. intros xIn. apply xOut. left. unfold USTACK_TOP in *; lia. }
  assert (call1 : call_ok RT Σ m1 (Z_to_bv 64 (U + -96 - pad)) lo).
  { unfold call_ok. rewrite eF1. split; [exact lowStk1|]. split; [exact loWin|]. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. clear - spAl padR. Z.div_mod_to_equations; lia. }
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 (U + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (U + -96 - pad)) (Z_to_bv 64 64)
           a1x a2x a3 a4 a5 a6 a7 s2 (Z_to_bv 64 OPT_LOAD_STRINGS) a1 s5 s6 s7 (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6 F fc m1 lo
           fdP mstP (or_introl eq_refl) tpV ltac:(lia) ltac:(lia) art1 inv1 call1 T c1 at1').
  intros c2 (Σ1 & f & at2 & frS1 & lvS1 & sp0S1 & crS1 & fPos & fAl & fTop & cgS1).
  destruct (ASTA_unpack RT Σ1 PMc _ c2 at2) as (ms2 & (m2 & ret2 & (art2 & inv2 & wm2 & stk2) & pres2 & wrF & wrSh) & at2'). clear at2.
  destruct ret2 as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & Fb & fcb & ->).
  rewrite (ret_pc_even SITE_icb_smalloc) in at2' by (unfold SITE_icb_smalloc; lia).

  change (bv_unsigned sp) with U in mu1, save1, padStk1, lowStk1.
  rewrite eF1 in stk2, pres2.
  assert (fIn1 : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite frS1; left; reflexivity).
  pose proof (af_frames_align RT AF Σ1 m2 f 0 art2 fIn1) as (_ & fSeg).
  pose proof (af_frames_range RT AF Σ1 m2 f 0 art2 fIn1) as (_ & fWin & _ & _).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0 art2 fIn1) as fShRange.
  change (fs_size 0) with 64 in fWin, fShRange, wrF, wrSh, fTop.
  rewrite sp0S1 in fWin.
  pose proof (af_client_consts RT AF Σ1 m2 art2) as (_ & shb2 & _ & _ & ut2).
  assert (stOut1 : forall x, client_static x -> x < U - 96 - pad - 160).
  { intros x (xIn & _). destruct xIn as (lo' & hi' & inL & xR). unfold CLIENT_STATIC in inL. cbn [In] in inL.
    unfold RT_STACK, STACK_WIN in *. destruct inL as [E|[E|[E|[]]]]; injection E as <- <-; lia. }
  (* static cells of m reach m2 unchanged *)
  assert (keep2 : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x) ->
            rw_cells asegs m2 A cs).
  { intros A cs cellsA stA.
    apply (rw_cells_agree asegs m1 m2 A cs); [| | exact wm2].
    - apply (rw_cells_agree asegs m m1 A cs cellsA); [| exact wm1].
      intros x xR. apply mu1. cbn [outside]. split; [| exact I]. pose proof (stOut1 _ (stA _ xR)). lia.
    - intros x xR. apply pres2. right; left. exact (stA _ xR). }
  assert (env2 : cl_env m2 lb canary).
  { apply (cl_env_pres (rt_live RT Σ) (rt_frames RT Σ) (U + -96 - pad) m1 m2 lb canary); [| exact pres2].
    apply (cl_env_seg [(U - 96, U)] m m1 lb canary envA mu1). cl_fp_lia. }
  assert (save2 : rw_cells asegs m2 (U + -96) [C8 (Z_to_bv 64 0); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ save1); [| exact wm2]. intros x xR. apply pres2. left. cbn [cells_size csize Nat.add] in xR.
    unfold USTACK_TOP in *. lia. }
  assert (padStk2 : stk asegs m2 (U + -96 - pad) (U + -96)).
  { apply (stk_agree asegs m1 m2 _ _ padStk1); [| exact wm2]. intros x xR. apply pres2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 wrF ltac:(lia)) as (fj & frm2).
  destruct (wr_at_rw_CB m2 (shad f) 8 wrSh ltac:(lia)) as (sj & shd2).
  unfold shad, SHB in shd2. cbn [Z.to_nat Pos.to_nat] in frm2, shd2.
  assert (od2 : rw_cells asegs m2 G_IC_OPTSDONE [C8 (Z_to_bv 64 0)])
    by (apply keep2; [exact cDone | intros x xR; cbn [cells_size csize Nat.add] in xR; apply client_static_intro; unfold G_IC_OPTSDONE in *; lia]).
  assert (stop2 : rw_cells asegs m2 G_IC_STOPPED [C1 (Z_to_bv 8 0)])
    by (apply keep2; [exact cStop | intros x xR; cbn [cells_size csize Nat.add] in xR; apply client_static_intro; unfold G_IC_STOPPED in *; lia]).
  assert (bonce2 : rw_cells asegs m2 G_IC_BASE_ONCE [C4 (Z_to_bv 64 0)])
    by (apply keep2; [exact cBonce | intros x xR; cbn [cells_size csize Nat.add] in xR; apply client_static_intro; unfold G_IC_BASE_ONCE in *; lia]).
  assert (cb2 : rw_cells asegs m2 (12205808 + -96) [C8 oldcb])
    by (apply keep2; [exact cCb | intros x xR; cbn [cells_size csize Nat.add] in xR; apply client_static_intro; lia]).
  pose proof (afp_acc_global RT GOBJ AFP Σ1 m2 G_IC_OPTSDONE 8 G_IC_OPTSDONE 8 art2 GO_optsdone ltac:(lia) ltac:(lia)) as odAcc2.
  pose proof (cl_env_ssp m2 lb canary ut2 env2) as ssp2.
  pose proof (if_w1 sp gp tp t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b s2 a1 s5 s6 s7 s9 s10 s11 t3b t4b t5b t6b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
                Fb fcb m2 f lo pad fj sj oldcb canary padR fPos fAl fSeg ltac:(unfold STACK_WIN in *; lia) ltac:(destruct fShRange; [left|right]; lia)
                ltac:(unfold RT_STACK in *; lia) loHi spHi tpV ut2 shb2 save2 padStk2 stk2 frm2 shd2 stop2 od2 odAcc2 bonce2 ssp2 cb2 inv2) as walk1.
  cl_lift walk1 at2' c3 at3.
  destruct (ASTA_unpack RT Σ1 PMc _ c3 at3)
    as (ms3 & (a0c & a1c & a2c & a3c & j8 & rj & fa & fb & m3 & -> & mu3 & wm3 & inv3 & save3 & frm3 & shd3 & od3 & odAcc3 & bonce3 & cb3 & full3 & ret3 & link3 & ssp3 & padStk3 & lowStk3) & at3').
  clear at3.

  change (bv_unsigned sp) with U in mu3, save3, cb3, full3, ret3, link3, padStk3, lowStk3, at3'.
  assert (eSI : bv_unsigned (Z_to_bv 64 (U + -96 - pad + -128)) = U + -96 - pad + -128)
    by (apply unsigned_lit; unfold RT_STACK in *; lia).
  assert (art3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (U + -96 - pad + -128) art2 ltac:(rewrite sp0S1; unfold STACK_WIN, RT_STACK in *; lia)); [|exact wm3].
    intros x xOut. apply mu3. cbn [outside].
    assert (inF : f <= bv_unsigned x < f + 56 -> in_fframe (rt_frames RT Σ1) (bv_unsigned x))
      by (intros xR; exists f, 0%nat; split; [exact fIn1 | change (fs_size 0) with 64; lia]).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ I)))))); intros xIn; apply xOut.
    - right; right; right; left. apply inF. lia.
    - right; right; right; left. apply inF. lia.
    - right; right; right; right. exists f, 0%nat. split; [exact fIn1|]. unfold shad, SHB. change (fs_size 0) with 64.
      clear - xIn fPos. Z.div_mod_to_equations. lia.
    - left. unfold USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. unfold G_IC_BASE_ONCE in *. lia.
    - right; left. apply client_static_intro. lia. }
  assert (shOut : forall x, client_static x -> x < f / 8 + 2147450880 /\ x < f).
  { intros x (xIn & _). destruct xIn as (lo' & hi' & inL & xR). unfold CLIENT_STATIC in inL. cbn [In] in inL.
    unfold SEGTOP_A in fSeg. assert (0 <= f / 8) by (apply Z.div_pos; lia).
    destruct inL as [E|[E|[E|[]]]]; injection E as <- <-; lia. }
  assert (keep3 : forall A cs, rw_cells asegs m A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x /\ ~ (G_IC_BASE_ONCE <= x < G_IC_BASE_ONCE + 4) /\ ~ (12205712 <= x < 12205720)) ->
            rw_cells asegs m3 A cs).
  { intros A cs cellsA stA. apply (rw_cells_agree asegs m2 m3 A cs); [| | exact wm3].
    - apply keep2; [exact cellsA|]. intros x xR. exact (proj1 (stA _ xR)).
    - intros x xR. destruct (stA _ xR) as (xSt & xNotB & xNotC). pose proof (shOut _ xSt) as (xLtSh & xLtF).
      pose proof (stOut1 _ xSt). apply mu3. cbn [outside]. repeat split; try exact I; lia. }
  assert (knk3 : ro_cells asegs m3 (12340824 + 8 * nk) [C8 w]).
  { apply (ro_cells_agree asegs m2 m3 _ _); [apply (ro_cells_agree asegs m1 m2 _ _); [apply (ro_cells_agree asegs m m1 _ _ cKnk) |] |].
    - intros x xR. cbn [cells_size csize Nat.add] in xR. apply mu1. cbn [outside]. split; [unfold RT_STACK in *; lia | exact I].
    - intros x xR. cbn [cells_size csize Nat.add] in xR. apply pres2. right; left. apply client_static_intro. lia.
    - intros x xR. cbn [cells_size csize Nat.add] in xR. pose proof (shOut (bv_unsigned x)) as sx.
      assert (xSt : client_static (bv_unsigned x)) by (apply client_static_intro; lia).
      specialize (sx xSt). apply mu3. cbn [outside]. unfold G_IC_BASE_ONCE, RT_STACK in *. repeat split; try exact I; lia. }
  assert (j1Pos : 0 <= j1) by (destruct j1Alt as [(-> & _)|(-> & _)]; [lia | apply Z.mod_pos_bound; lia]).
  assert (ibCells3 : rw_cells asegs m3 G_IC_OPTS_LOCK [C8 o1] /\ rw_cells asegs m3 G_IC_INIT_LOCK [C8 o2]
            /\ rw_cells asegs m3 5938976 [C4 kold1] /\ rw_cells asegs m3 G_IC_IICL_KEY [C4 kold2]
            /\ rw_cells asegs m3 12341848 [C4 (Z_to_bv 64 nk)] /\ rw_cells asegs m3 12341856 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 sh]
            /\ rw_cells asegs m3 (12340824 + 8 * j1) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m3 (12340824 + 8 * (j1 + 1)) [C8 (Z_to_bv 64 0)]
            /\ rw_cells asegs m3 G_IC_BASE_INITED [C1 b0] /\ rw_cells asegs m3 G_IC_BASE_RET [C4 r0]).
  { repeat match goal with |- _ /\ _ => split end; (apply keep3; [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_IC_BASE_ONCE in *;
      (split; [apply client_static_intro; lia | split; lia]). }
  destruct ibCells3 as (olk3 & ilk3 & dkey3 & ikey3 & next3 & klk3 & kj1_3 & kj2_3 & binit3 & bret3).
  assert (env3 : cl_env m3 lb canary).
  { apply (cl_env_seg _ m2 m3 lb canary env2 mu3). unfold G_IC_BASE_ONCE. unfold SEGTOP_A in fSeg.
    assert (0 <= f / 8) by (apply Z.div_pos; lia). cl_fp_lia. }
  assert (call3 : call_ok RT Σ1 m3 (Z_to_bv 64 (U + -96 - pad + -128)) lo).
  { unfold call_ok. rewrite eSI, sp0S1. split; [exact lowStk3|]. split; [exact loWin|]. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. clear - spAl padR. Z.div_mod_to_equations; lia. }
  assert (ctx3 : cg_ctx (rt_cg RT Σ1) e_ibase [bv_unsigned (Z_to_bv 64 ONCE_RET_INIT)]).
  { rewrite unsigned_lit by (unfold ONCE_RET_INIT; lia). split; [| exact I]. rewrite cgS1.
    apply (cg_has_call _ ICF_SITES ICF_CALLS _ _ cgA). left. reflexivity. }
  assert (uw3 : uw_chain m3 (Z_to_bv 64 (U + -96 - pad + -128)) (Z_to_bv 64 G_IC_BASE_ONCE) []).
  { cbn [uw_chain]. left. rewrite eSI, unsigned_lit by (unfold G_IC_BASE_ONCE; lia). unfold G_IC_BASE_ONCE, RT_STACK in *. lia. }
  assert (cgIB : cg_has (rt_cg RT Σ1) IB_SITES IB_CALLS).
  { rewrite cgS1. apply (cg_has_sub _ ICF_SITES ICF_CALLS _ _ cgA).
    - unfold ICF_SITES. apply incl_appl, incl_refl.
    - unfold ICF_CALLS. do 2 apply incl_tl. apply incl_appl, incl_refl. }
  apply (C_IB Σ1 PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (U + -96 - pad + -128)) gp tp t0b t1b t2b (Z_to_bv 64 G_IC_BASE_ONCE) (Z_to_bv 64 e_ibase)
           a0c a1c a2c a3c a4b a5b a6b a7b (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1)
           (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3b t4b t5b t6b Fb fcb m3 lo [] lb canary nk j1 (j1 + 1)
           o1 o2 sh kold1 kold2 w r0 b0 fdP mstP tpV art3 inv3 call3 ltac:(rewrite eSI; unfold RT_STACK in *; lia) ctx3 uw3 cgIB
           ltac:(rewrite frS1; cbn [length]; lia) ltac:(rewrite lvS1; lia) ltac:(rewrite crS1; lia) env3
           olk3 ilk3 dkey3 ikey3 next3 nkR klk3 kj1_3 knk3 j1Alt ltac:(rewrite Z.mod_small; lia) kj2_3 binit3 bret3 T c3 at3').
  intros c4 (Σ2 & p1 & p2 & at4 & lvS2 & frS2 & sp0S2 & crS2 & cgS2 & p1Pos & p1Al & p1Top & p2Pos & p2Al & p2Top).
  destruct (ASTA_unpack RT Σ2 PMc _ c4 at4)
    as (ms4 & (m4 & ret4 & (art4 & inv4 & wm4 & stk4) & pres4 & env4 & olk4 & ilk4 & mtx1 & mtx2 & dkey4 & ikey4 & next4 & klk4 & kj1_4 & kj2_4 & binit4 & bret4) & at4').
  clear at4.
  destruct ret4 as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & Fd & fcd & ->).
  rewrite (ret_pc_even ONCE_RET_INIT) in at4' by (unfold ONCE_RET_INIT; lia).

  rewrite eSI in stk4, pres4.
  pose proof (af_client_consts RT AF Σ2 m4 art4) as (_ & shb4 & _ & _ & ut4).
  assert (keep4 : forall A cs, rw_cells asegs m3 A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
               aclient (rt_live RT Σ1) (rt_frames RT Σ1) (U + -96 - pad + -128) x /\ outside (IB_W j1 (j1 + 1)) x) ->
            rw_cells asegs m4 A cs).
  { intros A cs cellsA keepA. apply (rw_cells_agree asegs m3 m4 A cs cellsA); [| exact wm4].
    intros x xR. destruct (keepA _ xR) as (xCl & xOut). exact (pres4 x xCl xOut). }
  assert (lsonce3 : rw_cells asegs m3 G_LS_ONCE [C4 (Z_to_bv 64 0)])
    by (apply keep3; [exact cLsonce | intros x xR; cbn [cells_size csize Nat.add] in xR; unfold G_LS_ONCE, G_IC_BASE_ONCE in *;
                      split; [apply client_static_intro; lia | split; lia]]).
  assert (stat4 : rw_cells asegs m4 G_IC_BASE_ONCE [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m4 (12205808 + -96) [C8 (Z_to_bv 64 (U + -96 - pad + -128))]
            /\ rw_cells asegs m4 G_LS_ONCE [C4 (Z_to_bv 64 0)]).
  { repeat match goal with |- _ /\ _ => split end; (apply keep4; [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold IB_W, Fz_M_malloc.G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_IC_BASE_ONCE, G_LS_ONCE in *;
      (split; [right; left; apply client_static_intro; lia | cbn [outside]; repeat split; try exact I; lia]). }
  destruct stat4 as (bonce4 & cb4 & lsonce4).
  assert (frame4 : rw_cells asegs m4 (U + -96 - pad + -128)
                     (once_full_cells G_IC_BASE_ONCE oldcb canary s6 (Z_to_bv 64 (f + 32)) a1 (Z_to_bv 64 OPT_LOAD_STRINGS)
                        (Z_to_bv 64 f) (Z_to_bv 64 (U + -96 - pad)) (Z_to_bv 64 (U + -96 - pad)))
            /\ rw_cells asegs m4 (U + -96 - pad + -32) [CB 8 rj; C8 (Z_to_bv 64 RUN_ONCE_RET)]
            /\ rw_cells asegs m4 (U + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ibase)]).
  { repeat match goal with |- _ /\ _ => split end; (apply keep4; [assumption|]); intros x xR; unfold once_full_cells in xR; cbn [cells_size csize Nat.add] in xR;
      unfold USTACK_TOP, RT_STACK, IB_W, Fz_M_malloc.G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET in *;
      (split; [left; unfold USTACK_TOP; lia | cbn [outside]; repeat split; try exact I; lia]). }
  destruct frame4 as (full4 & ret4 & link4).
  pose proof (cl_env_ssp m4 (Z_to_bv 8 1) canary ut4 env4) as ssp4.
  pose proof (if_w2 sp gp tp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d a1 s6 s10 s11 t3d t4d t5d t6d Fd fcd m4 f lo pad rj oldcb canary
                (Z_to_bv 64 (U + -96 - pad + -128)) padR fPos ltac:(unfold STACK_WIN in *; lia) ltac:(unfold RT_STACK in *; lia) loHi spHi tpV ut4
                bonce4 ssp4 cb4 full4 ret4 link4 stk4 bret4 lsonce4 inv4) as walk2.
  cl_lift walk2 at4' c5 at5.
  destruct (ASTA_unpack RT Σ2 PMc _ c5 at5)
    as (ms5 & (a0e & a1e & a2e & a3e & rj5 & m5 & -> & mu5 & wm5 & inv5 & bonce5 & lsrun5 & cb5 & full5 & ret5 & link5 & ssp5 & lowStk5) & at5').
  clear at5.
  change (bv_unsigned sp) with U in mu5, cb5, full5, ret5, link5, lowStk5, at5'.
  assert (art5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 (U + -96 - pad + -160) art4 ltac:(rewrite sp0S2, sp0S1; unfold STACK_WIN, RT_STACK in *; lia)); [|exact wm5].
    intros x xOut. apply mu5. cbn [outside]. unfold G_IC_BASE_ONCE, G_LS_ONCE.
    refine (conj _ (conj _ (conj _ (conj _ I)))); intros xIn; apply xOut.
    - left. unfold USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia. }

  assert (call5 : call_ok RT Σ2 m5 (Z_to_bv 64 (U + -96 - pad + -128)) lo).
  { unfold call_ok. rewrite eSI, sp0S2, sp0S1. split; [exact lowStk5|]. split; [exact loWin|]. split; [unfold RT_STACK in *; lia|].
    split; [unfold USTACK_TOP in *; lia|]. clear - spAl padR. Z.div_mod_to_equations; lia. }
  assert (ctx5 : cg_ctx (rt_cg RT Σ2) e_loadstr [bv_unsigned (Z_to_bv 64 ONCE_RET_INIT)]).
  { rewrite unsigned_lit by (unfold ONCE_RET_INIT; lia). split; [| exact I]. rewrite cgS2, cgS1.
    apply (cg_has_call _ ICF_SITES ICF_CALLS _ _ cgA). right; left. reflexivity. }
  assert (uw5 : uw_chain m5 (Z_to_bv 64 (U + -96 - pad + -128)) (Z_to_bv 64 G_LS_ONCE) []).
  { cbn [uw_chain]. left. rewrite eSI, unsigned_lit by (unfold G_LS_ONCE; lia). unfold G_LS_ONCE, RT_STACK in *. lia. }
  assert (cgLS : cg_has (rt_cg RT Σ2) LS_SITES LS_CALLS).
  { rewrite cgS2, cgS1. apply (cg_has_sub _ ICF_SITES ICF_CALLS _ _ cgA).
    - unfold ICF_SITES. apply incl_appr, incl_refl.
    - unfold ICF_CALLS. do 2 apply incl_tl. apply incl_appr, incl_refl. }
  assert (env5 : cl_env m5 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m4 m5 _ canary env4 mu5). unfold G_IC_BASE_ONCE, G_LS_ONCE. cl_fp_lia. }
  assert (pos2 : Forall (fun x => 0 < snd x) (rt_live RT Σ2)) by (rewrite lvS2, lvS1; repeat constructor; cbn [snd]; lia || exact posA).
  assert (keep5 : forall A cs, rw_cells asegs m A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
               client_static x /\ outside [(G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4); (12205712, 12205720)] x
               /\ outside (IB_W j1 (j1 + 1)) x) ->
            rw_cells asegs m5 A cs).
  { intros A cs cellsA stA. apply (rw_cells_agree asegs m4 m5 A cs); [| | exact wm5].
    - apply keep4; [apply keep3; [exact cellsA|] |].
      + intros x xR. destruct (stA _ xR) as (xSt & (xB & xL & xC & _) & _). split; [exact xSt|]. split; assumption.
      + intros x xR. destruct (stA _ xR) as (xSt & _ & xIb). split; [right; left; exact xSt | exact xIb].
    - intros x xR. destruct (stA _ xR) as (xSt & (xB & xL & xC & _) & _). pose proof (stOut1 _ xSt).
      apply mu5. cbn [outside]. repeat split; try exact I; try assumption. lia. }
  assert (err5 : rw_cells asegs m5 12205644 [C4 e]).
  { apply keep5; [exact cErr|]. intros x xR. cbn [cells_size csize Nat.add] in xR.
    unfold IB_W, Fz_M_malloc.G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_IC_BASE_ONCE, G_LS_ONCE in *.
    split; [apply client_static_intro; lia|]. cbn [outside]. repeat split; try exact I; lia. }
  clear j1Alt.
  assert (munchKeep : forall (W : list (Z * Z)) (ma mb : mem) A cs, munch W ma mb -> rw_cells asegs ma A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs mb A cs).
  { intros W ma mb A cs muAB cellsA outA. apply (rw_cells_agree_nw asegs ma mb A cs cellsA).
    intros x xR. exact (muAB x (outA _ xR)). }
  assert (fromM5 : rw_cells asegs m5 G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m5 G_IC_OPTSDONE [C8 (Z_to_bv 64 0)]
            /\ rw_cells asegs m5 12186880 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m5 12186944 [C1 ib] /\ rw_cells asegs m5 12186912 [C4 kold]
            /\ rw_cells asegs m5 (12205808 + -150) [C1 u]
            /\ rw_cells asegs m5 (12340824 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m5 (12341912 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 0)]
            /\ rw_cells asegs m5 G_ERR_ONCE [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m5 G_ERR_LOCK [C8 lk0]
            /\ rw_cells asegs m5 G_ERR_HASH [C8 h0] /\ rw_cells asegs m5 G_ERR_FLAG [C4 f0] /\ rw_cells asegs m5 G_LS_RET [C4 r1]).
  { repeat match goal with |- _ /\ _ => split end; (apply keep5; [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold IB_W, Fz_M_malloc.G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_IC_BASE_ONCE, G_LS_ONCE,
        G_IC_STOPPED, G_IC_OPTSDONE, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in xR |- *;
      (split; [apply client_static_intro; lia | cbn [outside]; repeat split; try exact I; lia]). }
  destruct fromM5 as (stop5 & od5 & mko5 & mki5 & mkk5 & t150_5 & k3_5 & tsd3_5 & eo5 & el5 & eh5 & ef5 & lsret5).
  assert (fromM4 : rw_cells asegs m5 G_IC_BASE_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m5 12341848 [C4 (Z_to_bv 64 (j1 + 1))]
            /\ rw_cells asegs m5 12341856 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 sh]
            /\ rw_cells asegs m5 (12340824 + 8 * (j1 + 1)) [C8 (Z_to_bv 64 5412472)]).
  { repeat match goal with |- _ /\ _ => split end; (apply (munchKeep _ m4 m5 _ _ mu5); [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold G_IC_BASE_RET, G_IC_BASE_ONCE, G_LS_ONCE, RT_STACK in *; cbn [outside]; repeat split; try exact I; lia. }
  destruct fromM4 as (bret5 & next5 & klk5 & k2_5).
  pose proof (wg_rw_ro m5 _ _ k2_5) as knk5.
  apply (C_LS Σ2 PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (U + -96 - pad + -128)) gp tp t0d t1d t2d (Z_to_bv 64 G_LS_ONCE) (Z_to_bv 64 e_loadstr)
           a0e a1e a2e a3e a4d a5d a6d a7d (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1)
           (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3d t4d t5d t6d Fd fcd m5 lo [] (Z_to_bv 8 1) canary (j1 + 1) (j1 + 2)
           e (Z_to_bv 64 0) sh kold (Z_to_bv 64 5412472) (Z_to_bv 64 (U + -96 - pad + -128)) lk0 h0 f0 r1 ib u
           fdP mstP tpV art5 inv5 call5 ltac:(rewrite eSI; unfold RT_STACK in *; lia) ctx5 uw5 cgLS
           ltac:(rewrite frS2, frS1; cbn [length]; lia) ltac:(rewrite lvS2, lvS1; cbn [length]; lia) ltac:(rewrite crS2, crS1; lia) pos2 env5
           stop5 od5 bonce5 bret5 err5 mko5 mki5 mkk5 cb5 t150_5 next5 ltac:(lia) klk5 k3_5 knk5
           ltac:(right; split; [rewrite Z.mod_small; lia | rewrite unsigned_lit; lia]) ltac:(lia) tsd3_5 eo5 el5 eh5 ef5 lsret5 T c5 at5').
  intros c6 (Σ3 & MK & SA & P & pk & lh & B & L' & g' & bks' & lb' & u' & at6 & perm3 & lenL & items & frS3 & sp0S3 & crS3 & cgS3
             & mkPos & mkAl & mkTop & saPos & saAl & saTop & pPos & pAl & pTop & pkPos & pkAl & pkTop).
  destruct (ASTA_unpack RT Σ3 PMc _ c6 at6)
    as (ms6 & (m6 & v6 & ret6 & (art6 & inv6 & stk6) & pres6 & env6 & stop6 & od6 & bonce6 & bret6 & errno6 & mko6 & mki6 & mkk6 & next6 & klk6
               & k3_6 & cb6 & t150_6 & tsd6 & mkc6 & sac6 & pc6 & errSt6 & pkm6 & lh6 & lsret6) & at6').
  clear at6.
  destruct ret6 as (t0g & t1g & t2g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t3g & t4g & t5g & t6g & Fg & fcg & ->).
  rewrite (ret_pc_even ONCE_RET_INIT) in at6' by (unfold ONCE_RET_INIT; lia).
  rewrite eSI in stk6, pres6.

  assert (frS3f : rt_frames RT Σ3 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite frS3, frS2; exact frS1).
  assert (sp0S3f : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite sp0S3, sp0S2; exact sp0S1).
  assert (fIn3 : In (f, 0%nat) (rt_frames RT Σ3)) by (rewrite frS3f; left; reflexivity).
  assert (liveUp : forall y, In y (rt_live RT Σ2) -> In y (rt_live RT Σ3)).
  { intros y yIn. apply (Permutation_in _ (Permutation_sym perm3)). apply in_or_app. right. do 4 right. exact yIn. }
  assert (heap3 : forall p n, In (p, n) (rt_live RT Σ3) ->
            0 < p /\ p + n <= lo /\ (p + n <= 0x10000 \/ SEGTOP_A <= p) /\ (f + 64 <= p \/ p + n <= f)
            /\ (p + n <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= p)).
  { intros p n pnIn.
    pose proof (af_live_range RT AF Σ3 m6 p n art6 pnIn) as (pPos' & pTop' & pSide).
    pose proof (af_frames_range RT AF Σ3 m6 f 0 art6 fIn3) as (_ & _ & _ & fApart).
    pose proof (af_fshadow_apart RT AF Σ3 m6 f 0 art6 fIn3) as (shApart & _).
    specialize (fApart p n pnIn). specialize (shApart p n pnIn).
    change (fs_size 0) with 64 in fApart, shApart. unfold shad, SHB in shApart. rewrite sp0S3f in pTop'.
    assert (eDiv : (f + 64) / 8 = f / 8 + 8) by (rewrite <- Z.div_add by lia; f_equal; lia).
    rewrite eDiv in shApart. split; [exact pPos'|]. split; [lia|]. split; [exact pSide|]. split; [exact fApart|]. lia. }
  assert (presKeep : forall L Fr s (W : list (Z * Z)) (ma mb : mem) A cs, rt_pres_fp L Fr s W ma mb -> rw_cells asegs ma A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient L Fr s x /\ outside W x) -> rw_cells asegs mb A cs).
  { intros L Fr s W ma mb A cs presAB cellsA inA. apply (rw_cells_agree_nw asegs ma mb A cs cellsA).
    intros x xR. exact (presAB x (proj1 (inA _ xR)) (proj2 (inA _ xR))). }
  assert (ibStat6 : rw_cells asegs m6 G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ rw_cells asegs m6 G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)]
            /\ rw_cells asegs m6 5938976 [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m6 G_IC_IICL_KEY [C4 (Z_to_bv 64 (j1 + 1))]
            /\ rw_cells asegs m6 (12340824 + 8 * j1) [C8 (Z_to_bv 64 2047928)]
            /\ rw_cells asegs m6 (12340824 + 8 * (j1 + 1)) [C8 (Z_to_bv 64 5412472)]
            /\ rw_cells asegs m6 G_IC_BASE_INITED [C1 (Z_to_bv 8 1)]
            /\ rw_cells asegs m6 G_LS_ONCE [C4 (Z_to_bv 64 1)]).
  { repeat match goal with |- _ /\ _ => split end;
      (apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [try (apply (munchKeep _ m4 m5 _ _ mu5); [assumption|]) ; try assumption |]);
      intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold LS_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_ONCE, G_LS_ONCE, G_ALLOW_CUST,
        G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET, RT_STACK in *;
      try (split; [right; left; apply client_static_intro; lia|]); cbn [outside]; repeat split; try exact I; lia. }
  destruct ibStat6 as (olk6 & ilk6 & dkey6 & ikey6 & kj1_6 & kj2_6 & binit6 & lsrun6).

  assert (fDiv : (f + 64) / 8 = f / 8 + 8) by (rewrite <- Z.div_add by lia; f_equal; lia).
  assert (fDivPos : 0 <= f / 8) by (apply Z.div_pos; lia).
  unfold SEGTOP_A in fSeg.
  assert (inF1 : forall x, f <= x < f + 56 -> in_fframe (rt_frames RT Σ1) x)
    by (intros x xR; exists f, 0%nat; split; [exact fIn1 | change (fs_size 0) with 64; lia]).
  assert (inSh1 : forall x, f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8 -> in_fframe_shadow (rt_frames RT Σ1) x)
    by (intros x xR; exists f, 0%nat; split; [exact fIn1 | unfold shad, SHB; change (fs_size 0) with 64; rewrite fDiv; lia]).
  (* the stack-malloc frame, its shadow, the saved registers and the pad, from m3 to m6 *)
  assert (frm6 : rw_cells asegs m6 f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 ICF_DESCR); C8 (Z_to_bv 64 ICF_PC); CB 8 fa; C8 (Z_to_bv 64 0); CB 16 fb]).
  { apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [apply (munchKeep _ m4 m5 _ _ mu5); [apply (presKeep _ _ _ _ m3 m4 _ _ pres4); [exact frm3|]|]|];
      intros x xR; cbn [cells_size csize Nat.add] in xR.
    - split; [right; right; right; left; apply inF1; lia|].
      unfold IB_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
    - unfold G_IC_BASE_ONCE, G_LS_ONCE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia.
    - split; [right; right; right; left; rewrite frS2; apply inF1; lia|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (shd6 : rw_cells asegs m6 (f / 8 + 2147450880)
                   [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
                    C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]).
  { apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [apply (munchKeep _ m4 m5 _ _ mu5); [apply (presKeep _ _ _ _ m3 m4 _ _ pres4); [exact shd3|]|]|];
      intros x xR; cbn [cells_size csize Nat.add] in xR.
    - split; [right; right; right; right; apply inSh1; lia|].
      unfold IB_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
    - unfold G_IC_BASE_ONCE, G_LS_ONCE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia.
    - split; [right; right; right; right; rewrite frS2; apply inSh1; lia|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (save6 : rw_cells asegs m6 (U + -96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [apply (munchKeep _ m4 m5 _ _ mu5); [apply (presKeep _ _ _ _ m3 m4 _ _ pres4); [exact save3|]|]|];
      intros x xR; cbn [cells_size csize Nat.add] in xR; unfold USTACK_TOP, RT_STACK, STACK_WIN in *.
    - split; [left; unfold USTACK_TOP; lia|].
      unfold IB_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
    - unfold G_IC_BASE_ONCE, G_LS_ONCE. cbn [outside]. repeat split; try exact I; lia.
    - split; [left; unfold USTACK_TOP; lia|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (padStk6 : stk asegs m6 (U + -96 - pad) (U + -96)).
  { apply (stk_agree_nw asegs m5 m6 _ _); [apply (stk_agree_nw asegs m4 m5 _ _); [apply (stk_agree_nw asegs m3 m4 _ _ padStk3)|]|];
      intros a aR; cbv beta in aR; unfold USTACK_TOP, RT_STACK, STACK_WIN in *.
    - apply pres4; [left; unfold USTACK_TOP; lia|].
      unfold IB_W, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
    - apply mu5. unfold G_IC_BASE_ONCE, G_LS_ONCE. cbn [outside]. repeat split; try exact I; lia.
    - apply pres6; [left; unfold USTACK_TOP; lia|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  assert (once6 : rw_cells asegs m6 (U + -96 - pad + -128)
                    (once_full_cells G_LS_ONCE oldcb canary (Z_to_bv 64 1) (Z_to_bv 64 (f + 32)) a1 (Z_to_bv 64 OPT_LOAD_STRINGS)
                       (Z_to_bv 64 f) (Z_to_bv 64 (U + -96 - pad)) (Z_to_bv 64 (U + -96 - pad)))
            /\ rw_cells asegs m6 (U + -96 - pad + -32) [CB 8 rj5; C8 (Z_to_bv 64 RUN_ONCE_RET)]
            /\ rw_cells asegs m6 (U + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ls)]).
  { repeat match goal with |- _ /\ _ => split end; (apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [assumption|]);
      intros x xR; unfold once_full_cells in xR; cbn [cells_size csize Nat.add] in xR; unfold USTACK_TOP, RT_STACK, STACK_WIN in *;
      (split; [left; unfold USTACK_TOP; lia|]);
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET; cbn [outside]; repeat split; try exact I; lia. }
  destruct once6 as (full6 & ret6c & link6).

  pose proof (heap3 p1 40 (liveUp _ ltac:(rewrite lvS2; right; left; reflexivity))) as (p1Lo & p1Hi & p1Side & _).
  pose proof (heap3 p2 40 (liveUp _ ltac:(rewrite lvS2; left; reflexivity))) as (p2Lo & p2Hi & p2Side & _).
  unfold SEGTOP_A in p1Side, p2Side.
  assert (mtx6 : rw_cells asegs m6 p1 (mutex_cells z64 z64) /\ rw_cells asegs m6 p2 (mutex_cells z64 z64)).
  { split; (apply (presKeep _ _ _ _ m5 m6 _ _ pres6); [apply (munchKeep _ m4 m5 _ _ mu5); [assumption|]|]);
      intros x xR; unfold mutex_cells in xR; cbn [cells_size csize Nat.add] in xR.
    - unfold G_IC_BASE_ONCE, G_LS_ONCE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia.
    - split; [right; right; left; exists p1, 40; split; [rewrite lvS2; right; left; reflexivity | lia]|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia.
    - unfold G_IC_BASE_ONCE, G_LS_ONCE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia.
    - split; [right; right; left; exists p2, 40; split; [rewrite lvS2; left; reflexivity | lia]|].
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET. cbn [outside]. repeat split; try exact I; lia. }
  destruct mtx6 as (mtx1_6 & mtx2_6).
  pose proof (af_client_consts RT AF Σ3 m6 art6) as (_ & shb6 & _ & _ & ut6).
  pose proof (cl_env_ssp m6 lb' canary ut6 env6) as ssp6.
  pose proof (afp_acc_global RT GOBJ AFP Σ3 m6 G_IC_OPTSDONE 8 G_IC_OPTSDONE 8 art6 GO_optsdone ltac:(lia) ltac:(lia)) as odAcc6.
  pose proof (proj1 (proj1 (rw_cells_app m6 f [C8 (Z_to_bv 64 1102416563)]
                              [C8 (Z_to_bv 64 ICF_DESCR); C8 (Z_to_bv 64 ICF_PC); CB 8 fa; C8 (Z_to_bv 64 0); CB 16 fb]) frm6)) as magic6.
  pose proof (proj2 (proj1 (rw_cells_app m6 f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 ICF_DESCR); C8 (Z_to_bv 64 ICF_PC); CB 8 fa]
                              [C8 (Z_to_bv 64 0); CB 16 fb]) frm6)) as tail6.
  pose proof (proj1 (proj1 (rw_cells_app m6 _ [C8 (Z_to_bv 64 0)] [CB 16 fb]) tail6)) as opts6.
  cbn [cells_size csize Nat.add] in opts6. change (Z.of_nat 32) with 32 in opts6.
  pose proof (if_w3 sp gp tp t0g t1g t2g v6 a1g a2g a3g a4g a5g a6g a7g a1 s10 s11 t3g t4g t5g t6g Fg fcg m6 f lo pad p1 rj5 oldcb canary
                (Z_to_bv 64 (U + -96 - pad + -128)) (Z_to_bv 64 1102416563) (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13))
                padR fPos fAl fSeg ltac:(unfold STACK_WIN in *; lia) ltac:(destruct fShRange; [left|right]; lia)
                ltac:(unfold RT_STACK in *; lia) loHi spHi tpV ut6 shb6 lsrun6 ssp6 cb6 full6 ret6c link6 stk6 lsret6 olk6
                ltac:(unfold USTACK_TOP in *; lia) od6 odAcc6 opts6 shd6 magic6 inv6) as walk3.
  clear fShRange p1Side p2Side.
  cl_lift walk3 at6' c7 at7.
  destruct (ASTA_unpack RT Σ3 PMc _ c7 at7)
    as (ms7 & (a0h & a1h & a2h & a3h & a4h & m7 & -> & mu7 & wm7 & inv7 & lsonce7 & cb7 & ssp7 & od7 & opts7 & magic7 & shd7 & lowStk7) & at7').
  clear at7.
  change (bv_unsigned sp) with U in mu7, lowStk7, at7'.

  assert (art7 : ART RT Σ3 m7).
  { apply (af_frame RT AF Σ3 m6 m7 (U + -96 - pad + -160) art6 ltac:(rewrite sp0S3f; unfold STACK_WIN, RT_STACK in *; lia)); [|exact wm7].
    intros a notCl. apply mu7. cbn [outside].
    assert (inF3 : f <= bv_unsigned a < f + 56 -> in_fframe (rt_frames RT Σ3) (bv_unsigned a))
      by (intros aR; exists f, 0%nat; split; [exact fIn3 | change (fs_size 0) with 64; lia]).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ I))))))); intros aIn; apply notCl.
    - left. unfold USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. unfold G_LS_ONCE in aIn. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. unfold G_IC_OPTSDONE in aIn. lia.
    - right; right; right; left. apply inF3. lia.
    - right; right; right; left. apply inF3. lia.
    - right; right; right; right. exists f, 0%nat. split; [exact fIn3|]. unfold shad, SHB. change (fs_size 0) with 64. rewrite fDiv. lia. }
  destruct (af_frame_release RT AF Σ3 m7 f 0 (rt_frames RT Σ) art7 frS3f) as (Σ4 & fl & flOn & flApart & flPos & flTop & slotRo & release).
  change (f + fs_size 0 - 8) with (f + 64 - 8) in slotRo. replace (f + 64 - 8) with (f + 56) in slotRo by lia.
  rewrite sp0S3f in flTop.
  assert (save7 : rw_cells asegs m7 (U + -96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (munchKeep _ m6 m7 _ _ mu7 save6). intros x xR. cbn [cells_size csize Nat.add] in xR.
    unfold G_LS_ONCE, G_IC_OPTSDONE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia. }
  assert (padStk7 : stk asegs m7 (U + -96 - pad) (U + -96)).
  { apply (stk_agree_nw asegs m6 m7 _ _ padStk6). intros a aR. cbv beta in aR. apply mu7.
    unfold G_LS_ONCE, G_IC_OPTSDONE, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (icb_s2_walk (Z_to_bv 64 SITE_icf_or) ra sp gp tp t0g t1g t2g a0h a1h a2h a3h a4h a5g a6g a7g
                (Z_to_bv 64 OPT_LOAD_STRINGS) a1 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) s10 s11 t3g t4g t5g t6g
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 Fg fcg m7 f fl lo pad j8
                padR ltac:(unfold RT_STACK in *; lia) loHi spHi fPos ltac:(unfold STACK_WIN in *; lia) flPos ltac:(unfold STACK_WIN in *; lia)
                lowStk7 padStk7 save7 slotRo flOn inv7) as walk4.
  unfold SITE_icb_release in walk4.
  cl_lift walk4 at7' c8 at8.
  destruct (ASTA_unpack RT Σ3 PMc _ c8 at8)
    as (ms8 & (t0i & t1i & t2i & a1i & a2i & a3i & a4i & a5i & a6i & a7i & t3i & t4i & t5i & t6i & m8 & -> & mu8 & wm8 & inv8 & stk8 & flOff) & at8').
  clear at8.
  destruct (release m8 mu8 wm8 flOff) as (art8 & frS4 & lvS4 & sp0S4 & crS4 & alS4 & amS4 & cgS4).
  pose proof (ASTA_switch RT Σ3 Σ4 PMc _ c8 at8' alS4 amS4) as at8''. clear at8'.

  assert (statOut : forall x, client_static x ->
            outside [(G_LS_ONCE, G_LS_ONCE + 4); (12205712, 12205720); (G_IC_OPTSDONE, G_IC_OPTSDONE + 8)] x ->
            outside [(U + -96 - pad + -160, U + -96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (12205808 + -96, 12205808 + -88);
                     (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] x
            /\ outside [(fl, fl + 1)] x).
  { intros x xSt (nLs & nCb & nOd & _). pose proof (shOut x xSt) as (xBelowSh & xBelowF). pose proof (stOut1 x xSt) as xBelowStk.
    split.
    - cbn [outside]. repeat split; try exact I; try assumption; lia.
    - cbn [outside]. split; [|exact I]. intros xIn. apply flApart. replace fl with x by lia. right; left. exact xSt. }
  assert (heapOut : forall p n x, In (p, n) (rt_live RT Σ3) -> p <= x < p + n ->
            outside [(U + -96 - pad + -160, U + -96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (12205808 + -96, 12205808 + -88);
                     (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] x
            /\ outside [(fl, fl + 1)] x).
  { intros p n x pIn xR. pose proof (heap3 p n pIn) as (hPos & hLo & hSide & hF & hSh). split.
    - unfold G_LS_ONCE, G_IC_OPTSDONE, SEGTOP_A, STACK_WIN, RT_STACK in *. cbn [outside]. repeat split; try exact I; lia.
    - cbn [outside]. split; [|exact I]. intros xIn. apply flApart. replace fl with x by lia.
      right; right; left. exists p, n. split; [exact pIn | exact xR]. }
  assert (keep68 : forall A cs, rw_cells asegs m6 A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
               outside [(U + -96 - pad + -160, U + -96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (12205808 + -96, 12205808 + -88);
                        (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] x
               /\ outside [(fl, fl + 1)] x) ->
            rw_cells asegs m8 A cs).
  { intros A cs cellsA outA. apply (munchKeep _ m7 m8 _ _ mu8); [apply (munchKeep _ m6 m7 _ _ mu7 cellsA)|];
      intros x xR; exact (proj1 (outA _ xR)) || exact (proj2 (outA _ xR)). }
  assert (stat8 : rw_cells asegs m8 G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m8 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]
            /\ rw_cells asegs m8 G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ rw_cells asegs m8 G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)]
            /\ rw_cells asegs m8 5938976 [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m8 G_IC_IICL_KEY [C4 (Z_to_bv 64 (j1 + 1))]
            /\ rw_cells asegs m8 (12340824 + 8 * j1) [C8 (Z_to_bv 64 2047928)]
            /\ rw_cells asegs m8 (12340824 + 8 * (j1 + 1)) [C8 (Z_to_bv 64 5412472)]
            /\ rw_cells asegs m8 G_IC_BASE_INITED [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m8 G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
            /\ rw_cells asegs m8 12205644 [C4 (sx32 e)] /\ rw_cells asegs m8 12186880 [C4 (Z_to_bv 64 2)]
            /\ rw_cells asegs m8 12186944 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m8 12186912 [C4 (Z_to_bv 64 (j1 + 2))]
            /\ rw_cells asegs m8 12341848 [C4 (Z_to_bv 64 (j1 + 2))]
            /\ rw_cells asegs m8 12341856 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 sh]
            /\ rw_cells asegs m8 (12340824 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 2058716)]
            /\ rw_cells asegs m8 (12205808 + -150) [C1 u'] /\ rw_cells asegs m8 (12341912 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]
            /\ rw_cells asegs m8 G_LS_RET [C4 (Z_to_bv 64 1)]).
  { repeat match goal with |- _ /\ _ => split end; (apply keep68; [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      unfold G_IC_STOPPED, G_IC_BASE_ONCE, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_LS_RET,
        G_LS_ONCE, G_IC_OPTSDONE in xR |- *;
      (apply statOut; [apply client_static_intro; lia | unfold G_LS_ONCE, G_IC_OPTSDONE; cbn [outside]; repeat split; try exact I; lia]). }
  destruct stat8 as (stop8 & bonce8 & olk8 & ilk8 & dkey8 & ikey8 & kj1_8 & kj2_8 & binit8 & bret8 & errno8 & mko8 & mki8 & mkk8 & next8 & klk8
                     & k3_8 & t150_8 & tsd8 & lsret8).
  assert (errSt8 : err_statics m8 pk lh).
  { destruct errSt6 as (eOnce & eFlag & eLock & eHash). unfold err_statics, G_ERR_ONCE, G_ERR_FLAG, G_ERR_LOCK, G_ERR_HASH in *.
    refine (conj _ (conj _ (conj _ _))); (apply keep68; [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      (apply statOut; [apply client_static_intro; lia | unfold G_LS_ONCE, G_IC_OPTSDONE; cbn [outside]; repeat split; try exact I; lia]). }
  assert (in3 : forall q, In q (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ2) -> In q (rt_live RT Σ3))
    by (intros q qIn; exact (Permutation_in _ (Permutation_sym perm3) qIn)).
  assert (heap8 : rw_cells asegs m8 p1 (mutex_cells z64 z64) /\ rw_cells asegs m8 p2 (mutex_cells z64 z64)
            /\ rw_cells asegs m8 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
            /\ rw_cells asegs m8 SA (sa_hdr (Z_to_bv 64 1) z64 z64 z64 (Z_to_bv 64 P))
            /\ rw_cells asegs m8 P [C8 z64; CB 120 (zeros 120)] /\ rw_cells asegs m8 pk (mutex_cells z64 z64)).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); (apply keep68; [assumption|]); intros x xR;
      unfold mutex_cells, sa_hdr in xR; cbn [cells_size csize Nat.add] in xR.
    - apply (heapOut p1 40); [apply liveUp; rewrite lvS2; right; left; reflexivity | lia].
    - apply (heapOut p2 40); [apply liveUp; rewrite lvS2; left; reflexivity | lia].
    - apply (heapOut MK 72); [apply in3; apply in_or_app; right; do 3 right; left; reflexivity | lia].
    - apply (heapOut SA 32); [apply in3; apply in_or_app; right; do 2 right; left; reflexivity | lia].
    - apply (heapOut P 128); [apply in3; apply in_or_app; right; right; left; reflexivity | lia].
    - apply (heapOut pk 40); [apply in3; apply in_or_app; right; left; reflexivity | lia]. }
  destruct heap8 as (mtx1_8 & mtx2_8 & mkc8 & sac8 & pc8 & pkm8).
  assert (late8 : rw_cells asegs m8 G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)] /\ rw_cells asegs m8 G_LS_ONCE [C4 (Z_to_bv 64 2)]
            /\ rw_cells asegs m8 (12205808 + -96) [C8 oldcb]).
  { repeat match goal with |- _ /\ _ => split end; (apply (munchKeep _ m7 m8 _ _ mu8); [assumption|]); intros x xR; cbn [cells_size csize Nat.add] in xR;
      cbn [outside]; (split; [|exact I]); intros xIn; apply flApart; replace fl with x by lia; right; left; apply client_static_intro;
      unfold G_IC_OPTSDONE, G_LS_ONCE in xR; lia. }
  destruct late8 as (od8 & lsonce8 & cb8).
  assert (lh8 : lh_repE GOBJ m8 L' lh B g' bks').
  { destruct lh6 as (lhRep & lhPerm & lhAl). split; [| split; [exact lhPerm | exact lhAl]].
    apply (lh_rep_agree asegs _ _ m6 m8 _ _ _ _ _ _ _ _ _ _ lhRep); [| intros q A0 n0 nm0 _ own; exact own].
    intros a aR fpA.
    assert (ownIn : exists q k, In (q, k) L' /\ q <= a < q + k).
    { destruct fpA as [R|[R|(p0 & A0 & inBk & R)]].
      - exists lh, 104. split; [| exact R]. apply (Permutation_in _ (Permutation_sym lhPerm)). left. reflexivity.
      - exists B, (8 * g_na g'). split; [| exact R]. apply (Permutation_in _ (Permutation_sym lhPerm)). right. left. reflexivity.
      - exists A0, 24. split; [| exact R]. apply (Permutation_in _ (Permutation_sym lhPerm)). right. right.
        apply in_map_iff. exists (p0, A0). split; [reflexivity | exact inBk]. }
    destruct ownIn as (q & k & qIn & qR).
    destruct (heapOut q k a (in3 _ (in_or_app _ _ _ (or_introl qIn))) qR) as (o7 & o8).
    split.
    - transitivity (m7 (wa a)); [apply mu8 | apply mu7]; rewrite wa_unsigned by lia; assumption.
    - intros viewA. exact (wmono_trans asegs m6 m7 m8 wm7 wm8 (wa a) viewA). }
  assert (env8 : cl_env m8 lb' canary).
  { assert (clOut : forall x, cl_cell x -> client_static x
              /\ outside [(G_LS_ONCE, G_LS_ONCE + 4); (12205712, 12205720); (G_IC_OPTSDONE, G_IC_OPTSDONE + 8)] x).
    { intros x clx. split; [exact (cl_cell_static x clx)|]. destruct clx as (lo' & hi' & inC & xr).
      unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in inC. cbn [In] in inC.
      unfold G_LS_ONCE, G_IC_OPTSDONE.
      repeat (destruct inC as [E|inC]; [injection E as <- <-; cbn [outside]; repeat split; try exact I; lia|]). destruct inC. }
    apply (cl_env_seg [(fl, fl + 1)] m7 m8 lb' canary); [apply (cl_env_seg _ m6 m7 lb' canary env6 mu7) | exact mu8 |];
      intros x clx; destruct (clOut x clx) as (xSt & xOut); [exact (proj1 (statOut x xSt xOut)) | exact (proj2 (statOut x xSt xOut))]. }

  assert (outSplit : forall (W1 W2 : list (Z * Z)) y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
  { intros W1. induction W1 as [|[l1 h1] W1 IHW]; intros W2 y outY; cbn [app outside] in *; [split; [exact I | exact outY]|].
    destruct outY as (nHere & outRest). destruct (IHW W2 y outRest) as (outL & outR). split; [split; assumption | exact outR]. }
  assert (acMono : forall L1 L2 (F1 F2 : list (Z * nat)) hiSp loSp y, (forall q, In q L1 -> In q L2) -> (forall q, In q F1 -> In q F2) -> loSp <= hiSp ->
            aclient L1 F1 hiSp y -> aclient L2 F2 loSp y).
  { intros L1 L2 F1 F2 hiSp loSp y upL upF sLe acY.
    destruct acY as [stkY|[stY|[(p0 & n0 & pIn & pR)|[(g0 & k0 & gIn & gR)|(g0 & k0 & gIn & gR)]]]].
    - left. lia.
    - right; left. exact stY.
    - right; right; left. exists p0, n0. split; [apply upL; exact pIn | exact pR].
    - right; right; right; left. exists g0, k0. split; [apply upF; exact gIn | exact gR].
    - right; right; right; right. exists g0, k0. split; [apply upF; exact gIn | exact gR]. }
  assert (liveAll : forall q, In q (rt_live RT Σ) -> In q (rt_live RT Σ3))
    by (intros q qIn; apply liveUp; rewrite lvS2, lvS1; right; right; exact qIn).
  assert (frameAll : forall q, In q (rt_frames RT Σ) -> In q (rt_frames RT Σ3)) by (intros q qIn; rewrite frS3f; right; exact qIn).
  pose proof (af_fshadow_apart RT AF Σ3 m6 f 0 art6 fIn3) as (_ & fShFrames).
  change (fs_size 0) with 64 in fShFrames. unfold shad, SHB in fShFrames. rewrite fDiv in fShFrames.
  assert (awayF : forall y, aclient (rt_live RT Σ) (rt_frames RT Σ) U y ->
            outside [(f, f + 64); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fl, fl + 1)] y).
  { intros y acY. cbn [outside].
    assert (flNot : ~ (fl <= y < fl + 1)).
    { intros yIn. assert (yEq : y = fl) by lia. subst y.
      destruct acY as [stkY|[stY|[(p0 & n0 & pIn & pR)|[(g0 & k0 & gIn & gR)|(g0 & k0 & gIn & gR)]]]].
      - unfold STACK_WIN, RT_STACK in *. lia.
      - apply flApart. right; left. exact stY.
      - apply flApart. right; right; left. exists p0, n0. split; [apply liveAll; exact pIn | exact pR].
      - apply flApart. right; right; right; left. exists g0, k0. split; [apply frameAll; exact gIn | exact gR].
      - apply flApart. right; right; right; right. exists g0, k0. split; [apply frameAll; exact gIn | exact gR]. }
    destruct acY as [stkY|[stY|[(p0 & n0 & pIn & pR)|[(g0 & k0 & gIn & gR)|(g0 & k0 & gIn & gR)]]]].
    - unfold STACK_WIN, RT_STACK in *. repeat split; try exact I; try exact flNot; lia.
    - pose proof (shOut y stY). repeat split; try exact I; try exact flNot; lia.
    - pose proof (heap3 p0 n0 (liveAll _ pIn)) as (_ & _ & _ & hF & hSh). repeat split; try exact I; try exact flNot; lia.
    - pose proof (af_frames_disj RT AF Σ3 m6 f 0 g0 k0 [] (rt_frames RT Σ) art6 frS3f gIn) as gApart.
      specialize (fShFrames g0 k0 (frameAll _ gIn)). change (fs_size 0) with 64 in gApart.
      repeat split; try exact I; try exact flNot; lia.
    - pose proof (af_frames_disj RT AF Σ3 m6 f 0 g0 k0 [] (rt_frames RT Σ) art6 frS3f gIn) as gApart.
      pose proof (af_fshadow_apart RT AF Σ3 m6 g0 k0 art6 (frameAll _ gIn)) as (_ & gSh).
      specialize (gSh f 0%nat fIn3). change (fs_size 0) with 64 in gApart, gSh. unfold shad, SHB in gSh, gR.
      repeat split; try exact I; try exact flNot; lia. }
  assert (presAll : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) U (ICF_W j1) m m8).
  { intros a acA outA.
    destruct (outSplit _ _ _ outA) as (outHead & outRest). destruct (outSplit _ _ _ outRest) as (outIb & outLs).
    cbn [outside] in outHead. destruct outHead as (nBo & nLo & nOd & nCb & _).
    pose proof (awayF _ acA) as awayA. cbn [outside] in awayA. destruct awayA as (nF & nSh & nFl & _).
    assert (padNN : 0 <= pad) by (clear - padR; lia).
    assert (stkSide : bv_unsigned a < U - 96 - pad - 160 \/ U <= bv_unsigned a).
    { destruct (cl_split RT AF Σ m U (96 + pad + 160) (bv_unsigned a) artA ltac:(clear - loWin loRoom roomA padR; unfold RT_STACK in *; lia)
                  ltac:(clear - padNN; lia) acA) as [aHi|aLo]; [right; exact aHi | left; clear - aLo; lia]. }
    clear - a acA outIb outLs nBo nLo nOd nCb nF nSh nFl padNN stkSide pres2 pres4 pres6 mu1 mu3 mu5 mu7 mu8 acMono lvS1 lvS2 frS1 frS2.
    assert (e8 : m8 a = m7 a) by (apply mu8; cbn [outside]; split; [exact nFl | exact I]).
    assert (e7 : m7 a = m6 a) by (apply mu7; cbn [outside]; repeat split; try exact I; try assumption; lia).
    assert (e6 : m6 a = m5 a).
    { apply pres6; [| exact outLs]. apply (acMono (rt_live RT Σ) _ (rt_frames RT Σ) _ U); [| | lia | exact acA].
      - intros q qIn. rewrite lvS2, lvS1. right; right. exact qIn.
      - intros q qIn. rewrite frS2, frS1. right. exact qIn. }
    assert (e5 : m5 a = m4 a) by (apply mu5; cbn [outside]; repeat split; try exact I; try assumption; lia).
    assert (e4 : m4 a = m3 a).
    { apply pres4; [| exact outIb]. apply (acMono (rt_live RT Σ) _ (rt_frames RT Σ) _ U); [| | lia | exact acA].
      - intros q qIn. rewrite lvS1. exact qIn.
      - intros q qIn. rewrite frS1. right. exact qIn. }
    assert (e3 : m3 a = m2 a) by (apply mu3; cbn [outside]; repeat split; try exact I; try assumption; lia).
    assert (e2 : m2 a = m1 a) by (apply pres2; apply (acMono (rt_live RT Σ) _ (rt_frames RT Σ) _ U); [intros q qIn; exact qIn | intros q qIn; exact qIn | lia | exact acA]).
    assert (e1 : m1 a = m a) by (apply mu1; cbn [outside]; split; [lia | exact I]).
    rewrite e8, e7, e6, e5, e4, e3, e2, e1. reflexivity. }
  apply finish. exists Σ4, p1, p2, MK, SA, P, pk, lh, B, L', g', bks', lb', u'.
  split.
  { apply (ASTA_conseq RT Σ4 PMc _ _ c8 at8''). intros ms <-. exists m8.
    split; [exists t0i, t1i, t2i, a1i, a2i, a3i, a4i, a5i, a6i, a7i, t3i, t4i, t5i, t6i, Fg, fcg; reflexivity|].
    split; [split; [exact art8 | split; [exact inv8 | exact stk8]]|].
    split; [exact presAll|].
    repeat match goal with |- _ /\ _ => split end; assumption. }
  rewrite lvS4, frS4, sp0S4, sp0S3f, crS4, cgS4, cgS3, cgS2, cgS1. rewrite lvS2, lvS1 in perm3.
  repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; lia.
Qed.
End ICFull.

