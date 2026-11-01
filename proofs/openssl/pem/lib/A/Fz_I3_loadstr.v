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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_lock Fz_T_local Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_I1_efirst Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw.
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
Notation ERRNO_A := (0xba3e4c)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation MK_INIT := (0xb9f540)%Z (only parsing).
Notation MK_CLEAN := (0x1f69dc)%Z (only parsing).

Section LoadStr.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_SHV : shelve_first_stmt RT.
Hypothesis C_CRS : crypto_strs_stmt RT GOBJ.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition LS_SITES : list (Z * Z) := (SITE_ls_shv, e_loadstr) :: (SITE_ls_crs, e_loadstr) :: SHV_SITES ++ CR_SITES.
Definition LS_CALLS : list (Z * Z) := (SITE_ls_shv, e_shelve) :: (SITE_ls_crs, e_crypto_strs) :: SHV_CALLS ++ CR_CALLS.
(* [comment removed for export] *)
Definition LS_W (j : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (ERRNO_A, ERRNO_A + 4); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1); (NEXT_KEY, NEXT_KEY + 12);
   (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (TSD_MAIN + 8 * j, TSD_MAIN + 8 * j + 8); (TP_A + -150, TP_A + -149);
   (G_ERR_ONCE, G_ERR_ONCE + 4); (G_ERR_LOCK, G_ERR_LOCK + 8); (G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4); (G_LS_RET, G_LS_RET + 4)].

(* [comment removed for export] *)
Definition loadstr_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (nk j : Z) (e od sh kold w oldcb lk0 h0 f0 r0 : word) (ib u : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 832 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_loadstr (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) LS_SITES LS_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4327 < LIVE_MAX ->
  38 <= rt_credit RT Σ -> Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m ERRNO_A [C4 e] ->
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m (TP_A + -96) [C8 oldcb] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
  rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> 1 <= j ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] ->
  rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m G_LS_RET [C4 r0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_loadstr m)))
    (fun c => exists (Σ' : rts RT) (MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte),
       ASTA RT Σ' PMc
         (fun ms => exists (m' : mem) (v : word),
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
            /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LS_W j) m m'
            /\ cl_env m' lb' canary
            /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
            /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
            /\ rw_cells asegs m' ERRNO_A [C4 (sx32 e)]
            /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
            /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
            /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
            /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
            /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)]
            /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
            /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 z64 (Z_to_bv 64 P))
            /\ rw_cells asegs m' P [C8 z64; CB 120 (zeros 120)]
            /\ err_statics m' pk lh /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks'
            /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)]) c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
       /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 38 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP
       /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
       /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).
Theorem loadstr_cps : loadstr_stmt.
Proof using AF AFP C_CRS C_SHV GO_mkey SM0 TSD.
  assert (st_static : forall x, 12186000 <= x < 12343248 -> ~ (12205720 <= x < 12205728) -> ~ (12205800 <= x < 12205848) ->
    ~ (12205856 <= x < 12205872) -> ~ (12341912 <= x < 12341920) -> ~ (12337584 <= x < 12337592) -> client_static x).
  {
    intros x InBlk NotTsd NotTls NotTls2 NotSlot0 NotMisc. unfold client_static, in_ranges, CLIENT_STATIC, RT_STATIC. split.
    - exists 12186000, 12343248. split; [right; right; left; reflexivity | exact InBlk].
    - intros (lo' & hi' & InR & Rng). cbn [In] in InR.
      repeat (destruct InR as [Eq|InR]; [injection Eq as <- <-; lia|]). exact InR.
  }

  assert (st_fresh : forall (Σ Σ' : rts RT) (m' : mem) l1 p n l2 usp x,
    ART RT Σ' m' -> rt_live RT Σ' = l1 ++ (p, n) :: l2 -> (forall e, In e (rt_live RT Σ) -> In e (l1 ++ l2)) ->
    (forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ')) -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (p <= x < p + n)).
  {
    intros Σ Σ' m' l1 p n l2 usp x Art' Split SubL SubF Win Cl Inside.
    assert (Here : In (p, n) (rt_live RT Σ')) by (rewrite Split; apply in_or_app; right; left; reflexivity).
    pose proof (af_live_range RT AF Σ' m' p n Art' Here) as (PPos & PTop & PSeg).
    destruct Cl as [Stack | [Stat | [(q & k & InQ & QR) | [(g & kk & InG & GR) | (g & kk & InG & GR)]]]].
    - lia.
    - pose proof (client_static_range x Stat). unfold SEGTOP_A in *. lia.
    - destruct (af_live_disj RT AF Σ' m' p n q k l1 l2 Art' Split (SubL _ InQ)); lia.
    - pose proof (af_frames_range RT AF Σ' m' g kk Art' (SubF _ InG)) as (_ & _ & _ & Away).
      destruct (Away p n Here); lia.
    - pose proof (af_fshadow_apart RT AF Σ' m' g kk Art' (SubF _ InG)) as (Away & _).
      destruct (Away p n Here); lia.
  }

  assert (st_apart : forall (Σ' : rts RT) (m' : mem) p n L q k,
    ART RT Σ' m' -> Permutation (rt_live RT Σ') ((p, n) :: L) -> In (q, k) L -> p + n <= q \/ q + k <= p).
  {
    intros Σ' m' p n L q k Art' Perm InQ.
    destruct (Permutation_vs_elt_inv [] L (p, n) Perm) as (l1 & l2 & Split).
    assert (Rest : Permutation (l1 ++ l2) L).
    { apply (Permutation_app_inv l1 l2 [] L (p, n)). rewrite <- Split. exact Perm. }
    exact (af_live_disj RT AF Σ' m' p n q k l1 l2 Art' Split (Permutation_in _ (Permutation_sym Rest) InQ)).
  }

  pose (AtShv := fun (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z) (c : config) =>
      exists (Σ1 : rts RT) (f pd : Z) (m1 : mem) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (j8 fr : list byte),
        ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 SITE_ls_shv) (Z_to_bv 64 (bv_unsigned sp + -64 - pd)) gp tp t0' t1' t2' sp (Z_to_bv 64 (bv_unsigned sp + -64 - pd))
                                    (Z_to_bv 64 (f + 32)) (Z_to_bv 64 LS_DESCR) (Z_to_bv 64 e_loadstr) a3' a4' a5' a6' a7'
                                    (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F' (Z_to_bv 64 e_shelve) fc' None m1 (seg_rom asegs))) c
        /\ (pd = 0 \/ pd = 16) /\ bv_unsigned sp mod 32 = pd
        /\ rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ /\ rt_live RT Σ1 = rt_live RT Σ /\ rt_sp0 RT Σ1 = rt_sp0 RT Σ
        /\ rt_credit RT Σ1 = rt_credit RT Σ - 1 /\ rt_cg RT Σ1 = rt_cg RT Σ
        /\ ART RT Σ1 m1 /\ mem_inv asegs m1 /\ wmono asegs m m1
        /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m1
        /\ stk asegs m1 lo (bv_unsigned sp + -64 - pd) /\ stk asegs m1 (bv_unsigned sp + -64 - pd) (bv_unsigned sp + -64)
        /\ rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m1 f [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr); CB 32 fr]
        /\ rw_cells asegs m1 (f / 8 + 2147450880)
             [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
              C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
        /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
              ~ (f <= x < f + 64) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8))).

  pose (AtCrs := fun (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
      (canary : word) (j : Z) (e sh oldcb : word) (c : config) =>
      exists (Σ2 : rts RT) (f pd MK SA P : Z) (m2 : mem) (u' : byte)
             (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (j8 : list byte),
        ASTA RT Σ2 PMc (eq (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64 - pd)) gp tp t0' t1' t2' sp (Z_to_bv 64 (bv_unsigned sp + -64 - pd))
                                    (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                                    (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F' (Z_to_bv 64 e_crypto_strs) fc' None m2 (seg_rom asegs))) c
        /\ bv_unsigned ra' = SITE_ls_crs
        /\ (pd = 0 \/ pd = 16) /\ bv_unsigned sp mod 32 = pd
        /\ rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ /\ rt_live RT Σ2 = (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ
        /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ /\ rt_credit RT Σ2 = rt_credit RT Σ - 2 /\ rt_cg RT Σ2 = rt_cg RT Σ
        /\ ART RT Σ2 m2 /\ mem_inv asegs m2 /\ wmono asegs m m2 /\ stk asegs m2 lo (bv_unsigned sp + -64 - pd)
        /\ stk asegs m2 (bv_unsigned sp + -64 - pd) (bv_unsigned sp + -64)
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SHV_W j (f + 32)) m m2
        /\ cl_env m2 (Z_to_bv 8 1) canary
        /\ rw_cells asegs m2 ERRNO_A [C4 (sx32 e)]
        /\ rw_cells asegs m2 MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m2 MK_INIT [C1 (Z_to_bv 8 1)]
        /\ rw_cells asegs m2 MK_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m2 NEXT_KEY [C4 (Z_to_bv 64 j)]
        /\ rw_cells asegs m2 KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m2 (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
        /\ rw_cells asegs m2 (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m2 (TP_A + -150) [C1 u']
        /\ rw_cells asegs m2 (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m2 (f + 32) [C8 z64]
        /\ rw_cells asegs m2 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
        /\ rw_cells asegs m2 SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
        /\ rw_cells asegs m2 P [C8 (Z_to_bv 64 (-1)); CB 120 (zeros 120)]
        /\ rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m2 f [C8 (Z_to_bv 64 LS_MAGIC)]
        /\ rw_cells asegs m2 (f / 8 + 2147450880)
             [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
              C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
        /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP
        /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
        /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
        /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
              ~ (f <= x < f + 64) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8))
        /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x -> ~ (SA <= x < SA + 32) /\ ~ (P <= x < P + 128))).

  pose (AtUsh := fun (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
      (canary : word) (j : Z) (e od sh oldcb r0 : word) (c : config) =>
      exists (Σ3 : rts RT) (f pd MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte) (m3 : mem)
             (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (j8 : list byte),
        ASTA RT Σ3 PMc (eq (MS (mkR (Z_to_bv 64 SITE_ls_ush) (Z_to_bv 64 (bv_unsigned sp + -64 - pd)) gp tp t0' t1' t2' sp (Z_to_bv 64 (bv_unsigned sp + -64 - pd))
                                    (Z_to_bv 64 0) (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
                                    (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F' (Z_to_bv 64 e_unshelve) fc' None m3 (seg_rom asegs))) c
        /\ (pd = 0 \/ pd = 16) /\ bv_unsigned sp mod 32 = pd
        /\ rt_frames RT Σ3 = (f, 0%nat) :: rt_frames RT Σ
        /\ Permutation (rt_live RT Σ3) (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
        /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
        /\ rt_sp0 RT Σ3 = rt_sp0 RT Σ /\ rt_credit RT Σ - 38 <= rt_credit RT Σ3 /\ rt_cg RT Σ3 = rt_cg RT Σ
        /\ ART RT Σ3 m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -64 - pd)
        /\ stk asegs m3 (bv_unsigned sp + -64 - pd) (bv_unsigned sp + -64)
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LS_W j) m m3
        /\ cl_env m3 lb' canary
        /\ rw_cells asegs m3 G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m3 G_IC_OPTSDONE [C8 od]
        /\ rw_cells asegs m3 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m3 G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
        /\ rw_cells asegs m3 ERRNO_A [C4 (sx32 e)]
        /\ rw_cells asegs m3 MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m3 MK_INIT [C1 (Z_to_bv 8 1)]
        /\ rw_cells asegs m3 MK_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m3 NEXT_KEY [C4 (Z_to_bv 64 j)]
        /\ rw_cells asegs m3 KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m3 (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
        /\ rw_cells asegs m3 (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m3 (TP_A + -150) [C1 u']
        /\ rw_cells asegs m3 (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)]
        /\ rw_cells asegs m3 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
        /\ rw_cells asegs m3 SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
        /\ rw_cells asegs m3 P [C8 (Z_to_bv 64 (-1)); CB 120 (zeros 120)]
        /\ err_statics m3 pk lh /\ rw_cells asegs m3 pk (mutex_cells z64 z64) /\ lh_repE GOBJ m3 L' lh B g' bks'
        /\ rw_cells asegs m3 G_LS_RET [C4 r0]
        /\ rw_cells asegs m3 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m3 f [C8 (Z_to_bv 64 LS_MAGIC)]
        /\ rw_cells asegs m3 (f / 8 + 2147450880)
             [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
              C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
        /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP
        /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
        /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
        /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP
        /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
              ~ (f <= x < f + 64) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8))
        /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x -> ~ (SA <= x < SA + 32) /\ ~ (P <= x < P + 128))).

  assert (st_entry : forall (Σ : rts RT) (PMc : Model -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 832 <= bv_unsigned sp ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_loadstr m)))
      (AtShv Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo)).
  {
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
      Fds Mat TpIs ArtA InvA CallA RoomA FrA CrA T c AstA Kont.
    destruct CallA as (StkA & WinA & RtsA & TopA & AlA).
    set (U := bv_unsigned sp) in *.
    pose proof (af_sp0_win RT AF Σ m ArtA) as Sp0W.
    pose proof (af_client_consts RT AF Σ m ArtA) as (_ & ShbA & _ & UarA & ImgA).
    assert (LoHi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in WinA; lia).
    assert (UCap : U <= 2 ^ 47) by (unfold USTACK_TOP in TopA; lia).
    unfold RT_STACK in RoomA.
    assert (PdCase : U mod 32 = 0 \/ U mod 32 = 16) by (clear - AlA; Z.div_mod_to_equations; lia).
    set (pd := U mod 32) in *.
    assert (PdBound : 0 <= pd <= 16) by lia.
    (* prologue: frame set-up, then the call of the fake-stack allocator *)
    pose proof (ls_w0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd
                  PdCase eq_refl StkA ltac:(lia) LoHi UCap ImgA ShbA UarA InvA) as WalkP.
    cl_lift WalkP AstA cP AstP.
    destruct (ASTA_unpack RT Σ PMc _ cP AstP) as (msP & PostP & AstP'). clear AstP.
    unfold ls_w0_post in PostP.
    destruct PostP as (a1P & mP & -> & MuP & WmP & InvP & FrmP & GapP & StkP).
    assert (BelowU : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) U x -> U <= x \/ x < rt_sp0 RT Σ - STACK_WIN)
      by (intros x Hx; exact (aclient_split RT AF Σ m U x ArtA Hx)).
    assert (PresP : rt_pres (rt_live RT Σ) (rt_frames RT Σ) U m mP).
    { intros x Hx. apply MuP. cbn [outside]. split; [| exact I]. destruct (BelowU _ Hx); lia. }
    assert (ArtP : ART RT Σ mP).
    { apply (af_frame RT AF Σ m mP lo ArtA WinA); [| exact WmP].
      intros x Hx. apply MuP. cbn [outside]. split; [| exact I].
      intros Hin. apply Hx. apply acl_stack. unfold USTACK_TOP in *. lia. }
    set (V := U + -64 - pd) in *.
    assert (VIs : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; subst V; lia).
    assert (CallP : call_ok RT Σ mP (Z_to_bv 64 V) lo).
    { unfold call_ok. rewrite VIs. split; [exact StkP|]. split; [exact WinA|].
      split; [unfold RT_STACK; subst V; lia|]. split; [subst V; unfold USTACK_TOP in *; lia|].
      subst V pd. clear - AlA. Z.div_mod_to_equations. lia. }
    apply (SM0 Σ PMc (Z_to_bv 64 SITE_ls_sm) (Z_to_bv 64 V) gp tp t0 t1 t2 sp (Z_to_bv 64 V) (Z_to_bv 64 64) a1P a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mP lo
             Fds Mat ltac:(left; reflexivity) TpIs FrA CrA ArtP InvP CallP T cP AstP').
    clear AstP'. intros cM (Σ1 & f & AstM & FrS & LvS & SpS & CrS & FPos & FAl & FTop & CgS).
    destruct (ASTA_unpack RT Σ1 PMc _ cM AstM) as (msM & (mM & RetM & (ArtM & InvM & WmM & StkM) & PresM & WrF & WrSh) & AstM'). clear AstM.
    destruct RetM as (t0M & t1M & t2M & a1M & a2M & a3M & a4M & a5M & a6M & a7M & t3M & t4M & t5M & t6M & FM & fcM & ->).
    replace (ret_pc (Z_to_bv 64 SITE_ls_sm)) with (Z_to_bv 64 SITE_ls_sm) in AstM'
      by (symmetry; apply ret_pc_even; [unfold SITE_ls_sm; lia | reflexivity]).
    rewrite VIs in StkM, PresM.
    assert (InF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FrS; left; reflexivity).
    pose proof (af_frames_range RT AF Σ1 mM f 0%nat ArtM InF) as (_ & FBelow & _ & _).
    pose proof (af_frames_align RT AF Σ1 mM f 0%nat ArtM InF) as (_ & FSeg).
    pose proof (af_frames_hi RT AF Σ1 mM f 0%nat ArtM InF) as FHi.
    change (fs_size 0) with 64 in FBelow, FHi, FTop.
    change (fs_size 0 - 8) with 56 in WrF. change (fs_size 0 / 8) with 8 in WrSh.
    rewrite SpS in FBelow.
    pose proof (af_client_consts RT AF Σ1 mM ArtM) as (_ & _ & _ & _ & ImgM).
    (* the saved registers and the padding gap lie above the allocator's stack pointer *)
    assert (AgStack : agree_on (fun x => V <= x < U) mP mM).
    { intros x Hx. apply PresM. apply acl_stack. unfold USTACK_TOP in *. lia. }
    assert (FrmM : rw_cells asegs mM (U + -64) [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs mP mM _ _ FrmP); [| exact WmM].
      intros x Hx. apply AgStack. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. subst V. lia. }
    assert (GapM : stk asegs mM V (U + -64)).
    { apply (stk_agree_nw asegs mP mM _ _ GapP). intros x Hx. apply AgStack. cbv beta in Hx |- *. lia. }
    destruct (wr_at_rw_CB mM f 56 WrF ltac:(lia)) as (fj & FjM).
    destruct (wr_at_rw_CB mM (shad f) 8 WrSh ltac:(lia)) as (sj & SjM).
    unfold shad, SHB in SjM.
    pose proof (ls_w1 sp gp tp t0M t1M t2M a1M a2M a3M a4M a5M a6M a7M s2 s3 s5 s6 s7 s8 s9 s10 s11 t3M t4M t5M t6M
                  ra s0 s1 s2 s3 s4 s5 FM fcM mM f lo pd fj sj
                  PdCase FPos FAl ltac:(unfold SEGTOP_A in FSeg; lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) LoHi UCap ImgM FrmM GapM StkM FjM SjM InvM) as Walk1.
    cl_lift Walk1 AstM' c1 Ast1.
    destruct (ASTA_unpack RT Σ1 PMc _ c1 Ast1) as (ms1 & Post1 & Ast1'). clear Ast1.
    unfold ls_w1_post in Post1.
    destruct Post1 as (j8 & fr & m1 & -> & Mu1 & Wm1 & Inv1 & Frm1 & Hdr1 & Sh1 & Gap1 & Stk1).
    assert (Sh64 : shad (f + 64) = f / 8 + 2147450880 + 8)
      by (rewrite (shad_add64 f 1 FAl); unfold shad, SHB; lia).
    assert (Art1 : ART RT Σ1 m1).
    { apply (af_frame RT AF Σ1 mM m1 lo ArtM ltac:(rewrite SpS; exact WinA)); [| exact Wm1].
      intros x Hx. apply Mu1. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx.
      - apply (acl_frame _ _ _ f 0%nat); [exact InF| change (fs_size 0) with 64; lia].
      - apply (acl_fshadow _ _ _ f 0%nat); [exact InF| change (fs_size 0) with 64; rewrite Sh64; unfold shad, SHB; lia].
      - apply acl_stack. unfold USTACK_TOP in *. lia. }
    assert (FApart : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) U x ->
              ~ (f <= x < f + 64) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)).
    { intros x Hx.
      destruct (newframe_apart RT AF Σ Σ1 mM f 0%nat U x ArtM FrS LvS SpS ltac:(lia) Hx) as (NF1 & NF2).
      change (fs_size 0) with 64 in NF1, NF2. rewrite Sh64 in NF2. unfold shad, SHB in NF2. split; assumption. }
    assert (Pres1 : rt_pres (rt_live RT Σ) (rt_frames RT Σ) U m m1).
    { intros x Hx.
      destruct (FApart (bv_unsigned x) Hx) as (NF1 & NF2).
      rewrite (Mu1 x).
      - rewrite (PresM x). { exact (PresP x Hx). }
        apply (aclient_mono _ _ U _ _ _ _ Hx); [auto| auto| subst V; lia].
      - cbn [outside]. destruct (BelowU _ Hx); repeat split; try exact I; lia. }
    apply Kont. unfold AtShv.
    exists Σ1, f, pd, m1, t0M, t1M, t2M, a3M, a4M, a5M, a6M, a7M, t3M, t4M, t5M, t6M, FM, fcM, j8, fr.
    split; [exact Ast1'|].
    split; [exact PdCase|]. split; [reflexivity|].
    split; [exact FrS|]. split; [exact LvS|]. split; [exact SpS|]. split; [exact CrS|]. split; [exact CgS|].
    split; [exact Art1|]. split; [exact Inv1|].
    split; [exact (wmono_trans asegs _ _ _ WmP (wmono_trans asegs _ _ _ WmM Wm1))|].
    split; [exact Pres1|].
    split; [exact Stk1|]. split; [exact Gap1|]. split; [exact Frm1|]. split; [exact Hdr1|]. split; [exact Sh1|]. exact FApart.
  }

  assert (st_shelve : forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
      (outer : list Z) (lb : byte) (canary : word) (nk j : Z) (e od sh kold w oldcb : word) (ib u : byte),
    fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 832 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_loadstr (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ) LS_SITES LS_CALLS ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4327 < LIVE_MAX -> 38 <= rt_credit RT Σ ->
    cl_env m lb canary ->
    rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
    rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
    rw_cells asegs m ERRNO_A [C4 e] ->
    rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
    rw_cells asegs m (TP_A + -96) [C8 oldcb] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> 1 <= j ->
    rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
    cps asegs (AtShv Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo)
      (AtCrs Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e sh oldcb)).
  {
    intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer lb canary nk j e od sh kold w oldcb ib u
      Fds Mat TpIs CallA RoomA CtxA UwA CgA FrA LvA CrA EnvA
      QStop QOpts QBOnce QBRet QErrno QMkOnce QMkInit QMkKey QCb QT150 QNext NkIn QLock QKeysJ QKeysNk JAlt JPos QTsdJ.
    intros T c Bnd Kont. unfold AtShv in Bnd.
    destruct Bnd as (Σ1 & f & pd & m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & j8 & fr
      & Ast1 & PdCase & PdIs & FrS & LvS & SpS & CrS & CgS & Art1 & Inv1 & Wm1 & Pres1 & Stk1 & Gap1 & Frm1 & Hdr1 & Sh1 & FApart).
    destruct CallA as (_ & WinA & _ & TopA & AlA).
    set (U := bv_unsigned sp) in *.
    unfold RT_STACK in RoomA. unfold USTACK_TOP in TopA.
    assert (JIn : 0 <= j < 128) by (destruct JAlt as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
    assert (PdBound : 0 <= pd <= 16) by lia.
    assert (InF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FrS; left; reflexivity).
    pose proof (af_frames_range RT AF Σ1 m1 f 0%nat Art1 InF) as (FPos & FBelow & _ & _).
    pose proof (af_frames_align RT AF Σ1 m1 f 0%nat Art1 InF) as (FAl & FSeg).
    pose proof (af_frames_hi RT AF Σ1 m1 f 0%nat Art1 InF) as FHi.
    pose proof (af_sp0_win RT AF Σ1 m1 Art1) as Sp0W.
    change (fs_size 0) with 64 in FBelow, FHi. rewrite SpS in FBelow, Sp0W.
    unfold SEGTOP_A in FSeg.
    assert (LoHi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in WinA; lia).
    set (V := U + -64 - pd) in *.
    assert (VIs : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; subst V; lia).
    (* the static cells shelve reads are untouched by the prologue and the allocator *)
    pose proof (pres_fp_of_pres (rt_live RT Σ) (rt_frames RT Σ) U [] m m1 Pres1) as PresE1.
    assert (Keep1 : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x) ->
                      rw_cells asegs m1 A cs).
    { intros A cs H Hs. apply (wg_keep_static _ _ _ _ m m1 A cs H PresE1 Wm1). intros x Hx. split; [exact (Hs x Hx) | exact I]. }
    assert (Keep1ro : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x) ->
                      ro_cells asegs m1 A cs).
    { intros A cs H Hs. apply (wg_keep_static_ro _ _ _ _ m m1 A cs H PresE1). intros x Hx. split; [exact (Hs x Hx) | exact I]. }
    pose proof (Keep1 _ _ QStop ltac:(intros x Hx; cbn in Hx; unfold G_IC_STOPPED in Hx; apply st_static; lia)) as QStop1.
    pose proof (Keep1 _ _ QOpts ltac:(intros x Hx; cbn in Hx; unfold G_IC_OPTSDONE in Hx; apply st_static; lia)) as QOpts1.
    pose proof (Keep1 _ _ QBOnce ltac:(intros x Hx; cbn in Hx; unfold G_IC_BASE_ONCE in Hx; apply st_static; lia)) as QBOnce1.
    pose proof (Keep1 _ _ QBRet ltac:(intros x Hx; cbn in Hx; unfold G_IC_BASE_RET in Hx; apply st_static; lia)) as QBRet1.
    pose proof (Keep1 _ _ QErrno ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QErrno1.
    pose proof (Keep1 _ _ QMkOnce ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QMkOnce1.
    pose proof (Keep1 _ _ QMkInit ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QMkInit1.
    pose proof (Keep1 _ _ QMkKey ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QMkKey1.
    pose proof (Keep1 _ _ QCb ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QCb1.
    pose proof (Keep1 _ _ QT150 ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QT1501.
    pose proof (Keep1 _ _ QNext ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QNext1.
    pose proof (Keep1 _ _ QLock ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QLock1.
    pose proof (Keep1 _ _ QKeysJ ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QKeysJ1.
    pose proof (Keep1ro _ _ QKeysNk ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QKeysNk1.
    pose proof (Keep1 _ _ QTsdJ ltac:(intros x Hx; cbn in Hx; apply st_static; lia)) as QTsdJ1.
    pose proof (cl_env_pres _ _ _ m m1 lb canary EnvA Pres1) as Env1.
    (* the slot shelve fills is the fifth 8-byte granule of the fake frame (bytes f+32..f+39, shadow byte 4) *)
    assert (Div32 : (f + 32) / 8 = f / 8 + 4) by (clear - FAl; Z.div_mod_to_equations; lia).
    assert (Slot1 : exists old, rw_cells asegs m1 (f + 32) [CB 8 old]).
    { pose proof (rw_cells_skip m1 f [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr)] [CB 32 fr] Hdr1) as Tail.
      cbn [cells_size csize Nat.add] in Tail.
      apply (rw_cells_split_CB asegs m1 _ [] 32 fr [] [8; 8; 16]%nat) in Tail; [| reflexivity].
      cbn [mk_CB_cells app] in Tail.
      pose proof (rw_cells_head m1 _ _ _ (rw_cells_skip m1 _ [CB 8 (firstn 8 fr)] _ Tail)) as Hd.
      cbn [cells_size csize Nat.add] in Hd. replace (f + Z.of_nat 24 + Z.of_nat 8) with (f + 32) in Hd by lia.
      eexists. exact Hd. }
    destruct Slot1 as (old & Slot1).
    assert (Acc1 : acc asegs m1 (f + 32) 8).
    { apply acc_of_shadow0; [| clear - FAl; Z.div_mod_to_equations; lia | lia].
      pose proof (rw_cells_head m1 _ _ _ (rw_cells_skip m1 _ [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ Sh1)) as Z4.
      cbn [cells_size csize Nat.add] in Z4.
      pose proof (ro_cells_bytes_at asegs m1 _ _ (wg_rw_ro m1 _ _ Z4)) as B4. cbn [cells_bytes cbytes app] in B4.
      unfold shad, SHB. rewrite Div32. replace (f / 8 + 4 + 2147450880) with (f / 8 + 2147450880 + Z.of_nat 4) by lia. exact B4. }
    (* call shelve *)
    assert (CtxS : In (SITE_ls_shv, e_loadstr) (cg_site (rt_cg RT Σ1)) /\ In (SITE_ls_shv, e_shelve) (cg_call (rt_cg RT Σ1))).
    { rewrite CgS. split; [apply (cg_has_site _ _ _ _ _ CgA) | apply (cg_has_call _ _ _ _ _ CgA)]; left; reflexivity. }
    assert (AgUp : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
    { intros x Hx. apply Pres1. apply acl_stack. exact Hx. }
    assert (SavedFp : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
    { pose proof (rw_cells_skip m1 _ [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ Frm1) as Sk.
      cbn [cells_size csize Nat.add] in Sk. replace (bv_unsigned sp - 16) with (U + -64 + Z.of_nat 48) by (subst U; lia). exact Sk. }
    destruct (cl_chain_call (rt_cg RT Σ1) e_loadstr e_shelve SITE_ls_shv m m1 ra s0 sp (Z_to_bv 64 V) outer
                ltac:(rewrite CgS; exact CtxA) (proj1 CtxS) (proj2 CtxS) UwA AgUp SavedFp ltac:(rewrite VIs; lia) ltac:(unfold USTACK_TOP; lia))
      as (CtxSh & UwSh).
    assert (CallS : call_ok RT Σ1 m1 (Z_to_bv 64 V) lo).
    { unfold call_ok. rewrite VIs, SpS. split; [exact Stk1|]. split; [exact WinA|]. unfold RT_STACK, USTACK_TOP.
      split; [subst V; lia|]. split; [subst V; lia|]. subst V. clear - AlA PdIs. subst pd. Z.div_mod_to_equations. lia. }
    apply (C_SHV Σ1 PMc (Z_to_bv 64 SITE_ls_shv) (Z_to_bv 64 V) gp tp t0' t1' t2' sp (Z_to_bv 64 V)
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 LS_DESCR) (Z_to_bv 64 e_loadstr) a3' a4' a5' a6' a7'
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
             F' fc' m1 lo (bv_unsigned ra :: outer) lb canary (f + 32) f nk j e od sh kold w oldcb ib u old
             Fds Mat TpIs eq_refl Art1 Inv1 CallS ltac:(rewrite VIs; unfold RT_STACK; subst V; lia)
             ltac:(rewrite unsigned_lit by (unfold SITE_ls_shv; lia); exact CtxSh) UwSh
             ltac:(rewrite CgS; apply (cg_has_weaken _ _ _ _ _ CgA); vm_compute; reflexivity)
             ltac:(rewrite FrS; cbn [length]; lia) ltac:(rewrite LvS; lia) ltac:(rewrite CrS; lia)
             Env1 QStop1 QOpts1 QBOnce1 QBRet1 QErrno1 QMkOnce1 QMkInit1 QMkKey1 QCb1 QT1501 QNext1 NkIn QLock1 QKeysJ1 QKeysNk1 JAlt JPos QTsdJ1
             InF ltac:(lia) ltac:(lia) ltac:(clear - FAl; Z.div_mod_to_equations; lia) Acc1 Slot1 T c Ast1).
    clear Ast1. intros c2 (Σ2 & MK & SA & P & u' & Ast2 & LvS2 & FrS2 & SpS2 & CrS2 & CgS2 & MkPos & MkAl & MkTop & SaPos & SaAl & SaTop & PPos & PAl & PTop).
    destruct (ASTA_unpack RT Σ2 PMc _ c2 Ast2) as (ms2 & (m2 & Ret2 & (Art2 & Inv2 & Wm2 & Stk2) & Pres2 & Env2 & QErrno2 & QMkOnce2 & QMkInit2
       & QMkKey2 & QNext2 & QLock2 & QKeysJ2 & QCb2 & QT1502 & QTsdJ2 & QSlot2 & QMk2 & QSa2 & QP2) & Ast2'). clear Ast2.
    destruct Ret2 as (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & Fr & fcr & ->).
    replace (ret_pc (Z_to_bv 64 SITE_ls_shv)) with (Z_to_bv 64 SITE_ls_shv) in Ast2'
      by (symmetry; apply ret_pc_even; [unfold SITE_ls_shv; lia | reflexivity]).
    pose proof (ls_w2 (Z_to_bv 64 V) gp tp t0r t1r t2r sp (Z_to_bv 64 V) a1r a2r a3r a4r a5r a6r a7r
                  (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                  Fr fcr m2 lo Stk2 LoHi ltac:(rewrite VIs; subst V; lia) ltac:(rewrite VIs; subst V; lia) Inv2) as Walk2.
    cl_lift Walk2 Ast2' c3 Ast3.
    destruct (ASTA_unpack RT Σ2 PMc _ c3 Ast3) as (ms3 & (ra3 & -> & Ra3) & Ast3'). clear Ast3.
    rewrite VIs in Stk2, Pres2.
    (* what the prologue left in the frame, the fake frame and its shadow survives shelve *)
    assert (ShB : 2147450880 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= f \/ f + 64 <= f / 8 + 2147450880).
    { destruct FHi as [Lw|Hg]; [right | left]; Z.div_mod_to_equations; lia. }
    assert (Keep2 : forall A cs, rw_cells asegs m1 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) V x /\ outside (SHV_W j (f + 32)) x) ->
              rw_cells asegs m2 A cs).
    { intros A cs H Hx. apply (rw_cells_agree asegs m1 m2 A cs H); [| exact Wm2]. intros x Hin. apply Pres2; apply Hx; exact Hin. }
    assert (SBelow : forall x, 65536 <= x < SEGTOP_A -> x < f) by (unfold SEGTOP_A; lia).
    assert (OutShv : forall x, (12343248 <= x \/ x < 12186000) -> ~ (f + 32 <= x < f + 40) -> outside (SHV_W j (f + 32)) x).
    { intros x Hx Hr. unfold SHV_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
    assert (Frm2 : rw_cells asegs m2 (U + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply Keep2; [exact Frm1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      - apply acl_stack. unfold USTACK_TOP. subst V. lia.
      - apply OutShv; lia. }
    assert (Hdr2 : rw_cells asegs m2 f [C8 (Z_to_bv 64 LS_MAGIC)]).
    { apply Keep2; [exact (rw_cells_head m1 _ _ _ Hdr1)|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      - apply (acl_frame _ _ _ f 0%nat); [exact InF | change (fs_size 0) with 64; lia].
      - apply OutShv; lia. }
    assert (Sh2 : rw_cells asegs m2 (f / 8 + 2147450880)
           [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]).
    { apply Keep2; [exact Sh1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      - apply (acl_fshadow _ _ _ f 0%nat); [exact InF |]. change (fs_size 0) with 64.
        rewrite (shad_add64 f 1 FAl). unfold shad, SHB. lia.
      - apply OutShv; lia. }
    assert (Gap2 : stk asegs m2 V (U + -64)).
    { apply (stk_agree_nw asegs m1 m2 _ _ Gap1). intros x Hx. cbv beta in Hx. apply Pres2.
      - apply acl_stack. unfold USTACK_TOP. subst V. lia.
      - apply OutShv; lia. }
    assert (PresAll : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) U (SHV_W j (f + 32)) m m2).
    { intros x Hx Ho. rewrite (Pres2 x).
      - exact (Pres1 x Hx).
      - apply (aclient_mono _ _ U _ _ _ _ Hx); [rewrite LvS; auto | rewrite FrS; intros q Hq; right; exact Hq | subst V; lia].
      - exact Ho. }
    assert (BlkApart : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) U x -> ~ (SA <= x < SA + 32) /\ ~ (P <= x < P + 128)).
    { intros x Hx.
      assert (FrSub : forall q, In q (rt_frames RT Σ) -> In q (rt_frames RT Σ2)) by (intros q Hq; rewrite FrS2, FrS; right; exact Hq).
      assert (WinU : rt_sp0 RT Σ2 - STACK_WIN <= U) by (rewrite SpS2, SpS; lia).
      split.
      - apply (st_fresh Σ Σ2 m2 [(P, 128)] SA 32 ((MK, 72) :: rt_live RT Σ) U x Art2 ltac:(rewrite LvS2, LvS; reflexivity)
                 ltac:(intros q Hq; right; right; exact Hq) FrSub WinU Hx).
      - apply (st_fresh Σ Σ2 m2 [] P 128 ((SA, 32) :: (MK, 72) :: rt_live RT Σ) U x Art2 ltac:(rewrite LvS2, LvS; reflexivity)
                 ltac:(intros q Hq; right; right; exact Hq) FrSub WinU Hx). }
    apply Kont. unfold AtCrs.
    exists Σ2, f, pd, MK, SA, P, m2, u', ra3, t0r, t1r, t2r, a1r, a2r, a3r, a4r, a5r, a6r, a7r, t3r, t4r, t5r, t6r, Fr, fcr, j8.
    split; [exact Ast3'|]. split; [exact Ra3|]. split; [exact PdCase|]. split; [exact PdIs|].
    split; [rewrite FrS2; exact FrS|]. split; [rewrite LvS2, LvS; reflexivity|].
    split; [rewrite SpS2; exact SpS|]. split; [rewrite CrS2, CrS; lia|]. split; [rewrite CgS2; exact CgS|].
    split; [exact Art2|]. split; [exact Inv2|]. split; [exact (wmono_trans asegs _ _ _ Wm1 Wm2)|]. split; [exact Stk2|]. split; [exact Gap2|].
    split; [exact PresAll|]. split; [exact Env2|].
    do 14 (split; [assumption|]).
    split; [exact Frm2|]. split; [exact Hdr2|]. split; [exact Sh2|].
    do 9 (split; [assumption|]).
    split; [exact FApart|]. exact BlkApart.
  }

  assert (st_crypto : forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
      (outer : list Z) (canary : word) (j : Z) (e od sh oldcb lk0 h0 f0 r0 : word),
    fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 832 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_loadstr (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ) LS_SITES LS_CALLS ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4327 < LIVE_MAX -> 38 <= rt_credit RT Σ ->
    Forall (fun x => 0 < snd x) (rt_live RT Σ) -> 1 <= j < 128 ->
    rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
    rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
    rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] ->
    rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
    rw_cells asegs m G_LS_RET [C4 r0] ->
    cps asegs (AtCrs Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e sh oldcb)
      (AtUsh Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e od sh oldcb r0)).
  {
    intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary j e od sh oldcb lk0 h0 f0 r0
      Fds Mat TpIs CallA RoomA CtxA UwA CgA FrA LvA CrA PosA JIn QStop QOpts QBOnce QBRet QEOnce QELock QEHash QEFlag QLsRet.
    intros T c Bnd Kont. unfold AtCrs in Bnd.
    destruct Bnd as (Σ2 & f & pd & MK & SA & P & m2 & u' & ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7'
      & t3' & t4' & t5' & t6' & F' & fc' & j8 & Ast2 & RaIs & PdCase & PdIs & FrS2 & LvS2 & SpS2 & CrS2 & CgS2
      & Art2 & Inv2 & Wm2 & Stk2 & Gap2 & Pres2 & Env2 & QErrno2 & QMkOnce2 & QMkInit2 & QMkKey2 & QNext2 & QLock2 & QKeysJ2
      & QCb2 & QT1502 & QTsdJ2 & QSlot2 & QMk2 & QSa2 & QP2 & Frm2 & Hdr2 & Sh2
      & MkPos & MkAl & MkTop & SaPos & SaAl & SaTop & PPos & PAl & PTop & FApart & BlkApart).
    destruct CallA as (_ & WinA & _ & TopA & AlA).
    set (U := bv_unsigned sp) in *.
    unfold RT_STACK in RoomA. unfold USTACK_TOP in TopA.
    assert (PdBound : 0 <= pd <= 16) by lia.
    assert (InF : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FrS2; left; reflexivity).
    pose proof (af_frames_range RT AF Σ2 m2 f 0%nat Art2 InF) as (FPos & FBelow & _ & _).
    pose proof (af_frames_align RT AF Σ2 m2 f 0%nat Art2 InF) as (FAl & FSeg).
    pose proof (af_frames_hi RT AF Σ2 m2 f 0%nat Art2 InF) as FHi.
    pose proof (af_sp0_win RT AF Σ2 m2 Art2) as Sp0W.
    change (fs_size 0) with 64 in FBelow, FHi. rewrite SpS2 in FBelow, Sp0W.
    unfold SEGTOP_A in FSeg.
    assert (LoHi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in WinA; lia).
    set (V := U + -64 - pd) in *.
    assert (VIs : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; subst V; lia).
    (* the cells crypto reads, and the return slot of G_LS_RET, were not touched before *)
    assert (Keep2 : forall A cs, rw_cells asegs m A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x /\ outside (SHV_W j (f + 32)) x) ->
              rw_cells asegs m2 A cs).
    { intros A cs H Hs. exact (wg_keep_static _ _ _ _ m m2 A cs H Pres2 Wm2 Hs). }
    assert (Far : forall x, 12186000 <= x < 12186880 -> outside (SHV_W j (f + 32)) x).
    { intros x Hx. unfold SHV_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
    assert (ErrFar : forall x, 12187600 <= x < 12187720 -> outside (SHV_W j (f + 32)) x).
    { intros x Hx. unfold SHV_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
    pose proof (Keep2 _ _ QStop ltac:(intros x Hx; cbn in Hx; unfold G_IC_STOPPED in Hx; split; [apply st_static | apply Far]; lia)) as QStop2.
    pose proof (Keep2 _ _ QOpts ltac:(intros x Hx; cbn in Hx; unfold G_IC_OPTSDONE in Hx; split; [apply st_static | apply Far]; lia)) as QOpts2.
    pose proof (Keep2 _ _ QBOnce ltac:(intros x Hx; cbn in Hx; unfold G_IC_BASE_ONCE in Hx; split; [apply st_static | apply Far]; lia)) as QBOnce2.
    pose proof (Keep2 _ _ QBRet ltac:(intros x Hx; cbn in Hx; unfold G_IC_BASE_RET in Hx; split; [apply st_static | apply Far]; lia)) as QBRet2.
    pose proof (Keep2 _ _ QLsRet ltac:(intros x Hx; cbn in Hx; unfold G_LS_RET in Hx; split; [apply st_static | apply Far]; lia)) as QLsRet2.
    pose proof (Keep2 _ _ QEOnce ltac:(intros x Hx; cbn in Hx; unfold G_ERR_ONCE in Hx; split; [apply st_static | apply ErrFar]; lia)) as QEOnce2.
    pose proof (Keep2 _ _ QELock ltac:(intros x Hx; cbn in Hx; unfold G_ERR_LOCK in Hx; split; [apply st_static | apply ErrFar]; lia)) as QELock2.
    pose proof (Keep2 _ _ QEHash ltac:(intros x Hx; cbn in Hx; unfold G_ERR_HASH in Hx; split; [apply st_static | apply ErrFar]; lia)) as QEHash2.
    pose proof (Keep2 _ _ QEFlag ltac:(intros x Hx; cbn in Hx; unfold G_ERR_FLAG in Hx; split; [apply st_static | apply ErrFar]; lia)) as QEFlag2.
    (* the frame of the caller is unchanged above the stack pointer, so the unwind chain extends *)
    assert (AgUp : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m2).
    { intros x Hx. apply Pres2; [apply acl_stack; exact Hx|].
      unfold SHV_W, G_ALLOW_CUST. cbn [outside]. unfold USTACK_TOP in Hx. repeat split; try exact I; lia. }
    assert (SavedFp : rw_cells asegs m2 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
    { pose proof (rw_cells_skip m2 _ [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ Frm2) as Sk.
      cbn [cells_size csize Nat.add] in Sk. replace (bv_unsigned sp - 16) with (U + -64 + Z.of_nat 48) by (subst U; lia). exact Sk. }
    assert (CtxC : In (SITE_ls_crs, e_loadstr) (cg_site (rt_cg RT Σ2)) /\ In (SITE_ls_crs, e_crypto_strs) (cg_call (rt_cg RT Σ2))).
    { rewrite CgS2. split; [apply (cg_has_site _ _ _ _ _ CgA) | apply (cg_has_call _ _ _ _ _ CgA)]; right; left; reflexivity. }
    destruct (cl_chain_call (rt_cg RT Σ2) e_loadstr e_crypto_strs SITE_ls_crs m m2 ra s0 sp (Z_to_bv 64 V) outer
                ltac:(rewrite CgS2; exact CtxA) (proj1 CtxC) (proj2 CtxC) UwA AgUp SavedFp ltac:(rewrite VIs; lia) ltac:(unfold USTACK_TOP; lia))
      as (CtxCr & UwCr).
    rewrite <- RaIs in CtxCr.
    assert (CallC : call_ok RT Σ2 m2 (Z_to_bv 64 V) lo).
    { unfold call_ok. rewrite VIs, SpS2. split; [exact Stk2|]. split; [exact WinA|]. unfold RT_STACK, USTACK_TOP.
      split; [subst V; lia|]. split; [subst V; lia|]. subst V. clear - AlA PdIs. subst pd. Z.div_mod_to_equations. lia. }
    assert (PosC : Forall (fun x => 0 < snd x) (rt_live RT Σ2)).
    { rewrite LvS2. repeat apply Forall_cons; cbn [snd]; try lia. exact PosA. }
    (* call crypto *)
    apply (C_CRS Σ2 PMc ra' (Z_to_bv 64 V) gp tp t0' t1' t2' sp (Z_to_bv 64 V) (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
             F' fc' m2 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary od lk0 h0 f0 oldcb
             Fds Mat TpIs Art2 Inv2 CallC ltac:(rewrite VIs; unfold RT_STACK; subst V; lia) CtxCr UwCr
             ltac:(rewrite CgS2; apply (cg_has_weaken _ _ _ _ _ CgA); vm_compute; reflexivity)
             ltac:(rewrite FrS2; cbn [length]; lia) ltac:(rewrite LvS2; cbn [length]; lia) ltac:(rewrite CrS2; lia) PosC
             Env2 QStop2 QOpts2 QBOnce2 QBRet2 QEOnce2 QELock2 QEHash2 QEFlag2 QCb2 T c Ast2).
    clear Ast2. intros c3 (Σ3 & pk & lh & B & L' & g' & bks' & lb' & Ast3 & Perm3 & LenL & GItems & FrS3 & SpS3 & CrS3 & CgS3 & PkPos & PkAl & PkTop).
    destruct (ASTA_unpack RT Σ3 PMc _ c3 Ast3) as (ms3 & (m3 & Ret3 & (Art3 & Inv3 & Stk3) & Pres3 & Env3 & QStop3 & QOpts3 & QBOnce3 & QBRet3
       & ErrSt3 & QCb3 & QPk3 & Lh3) & Ast3'). clear Ast3.
    destruct Ret3 as (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & Fr & fcr & ->).
    assert (RaEq : ra' = Z_to_bv 64 SITE_ls_crs) by (rewrite <- (Z_to_bv_bv_unsigned ra'), RaIs; reflexivity).
    rewrite RaEq in Ast3'.
    replace (ret_pc (Z_to_bv 64 SITE_ls_crs)) with (Z_to_bv 64 SITE_ls_crs) in Ast3'
      by (symmetry; apply ret_pc_even; [unfold SITE_ls_crs; lia | reflexivity]).
    rewrite VIs in Stk3, Pres3.
    (* what crypto leaves alone: client memory of the frames below, outside its write set *)
    assert (Keep3 : forall A cs, rw_cells asegs m2 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) V x /\ outside (EFIRST_W pk) x) ->
              rw_cells asegs m3 A cs).
    { intros A cs H Hx. apply (rw_cells_agree_nw asegs m2 m3 A cs H). intros x Hin. apply Pres3; apply Hx; exact Hin. }
    assert (EfFar : forall x, (12187720 <= x \/ x < 12187584) -> ~ (12205712 <= x < 12205720) -> outside (EFIRST_W pk) x).
    { intros x Hx Hc. unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF.
      cbn [outside]. repeat split; try exact I; lia. }
    assert (StatC : forall A cs, rw_cells asegs m2 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x /\ (12187720 <= x \/ x < 12187584) /\ ~ (12205712 <= x < 12205720)) ->
              rw_cells asegs m3 A cs).
    { intros A cs H Hx. apply Keep3; [exact H|]. intros x Hin. destruct (Hx x Hin) as (Hs & H1 & H2).
      split; [apply acl_static; exact Hs | exact (EfFar x H1 H2)]. }
    pose proof (StatC _ _ QErrno2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QErrno3.
    pose proof (StatC _ _ QMkOnce2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QMkOnce3.
    pose proof (StatC _ _ QMkInit2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QMkInit3.
    pose proof (StatC _ _ QMkKey2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QMkKey3.
    pose proof (StatC _ _ QNext2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QNext3.
    pose proof (StatC _ _ QLock2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QLock3.
    pose proof (StatC _ _ QKeysJ2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QKeysJ3.
    pose proof (StatC _ _ QT1502 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QT1503.
    pose proof (StatC _ _ QTsdJ2 ltac:(intros x Hx; cbn in Hx; split; [apply st_static; lia | split; lia])) as QTsdJ3.
    pose proof (StatC _ _ QLsRet2 ltac:(intros x Hx; cbn in Hx; unfold G_LS_RET in Hx; split; [apply st_static; lia | split; lia])) as QLsRet3.
    assert (InMK : In (MK, 72) (rt_live RT Σ2)) by (rewrite LvS2; right; right; left; reflexivity).
    assert (InSA : In (SA, 32) (rt_live RT Σ2)) by (rewrite LvS2; right; left; reflexivity).
    assert (InP : In (P, 128) (rt_live RT Σ2)) by (rewrite LvS2; left; reflexivity).
    assert (LiveC : forall p n A cs, In (p, n) (rt_live RT Σ2) -> rw_cells asegs m2 A cs -> p <= A -> A + Z.of_nat (cells_size cs) <= p + n ->
              rw_cells asegs m3 A cs).
    { intros p n A cs Hin H H1 H2. apply Keep3; [exact H|]. intros x Hx.
      pose proof (af_live_range RT AF Σ2 m2 p n Art2 Hin) as (_ & _ & PSeg). unfold SEGTOP_A in PSeg.
      split; [apply (acl_live _ _ _ p n); [exact Hin | lia]|].
      destruct (Z_lt_le_dec (p + n) 65537) as [Lo|Hi']; [| apply EfFar; lia].
      apply EfFar; lia. }
    pose proof (LiveC _ _ _ _ InMK QMk2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as QMk3.
    pose proof (LiveC _ _ _ _ InSA QSa2 ltac:(lia) ltac:(unfold sa_hdr; cbn [cells_size csize Nat.add]; lia)) as QSa3.
    pose proof (LiveC _ _ _ _ InP QP2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as QP3.
    assert (FrameC : forall A cs, rw_cells asegs m2 A cs -> f <= A -> A + Z.of_nat (cells_size cs) <= f + 56 -> rw_cells asegs m3 A cs).
    { intros A cs H H1 H2. apply Keep3; [exact H|]. intros x Hx. split.
      - apply (acl_frame _ _ _ f 0%nat); [exact InF | change (fs_size 0) with 64; lia].
      - apply EfFar; lia. }
    pose proof (FrameC _ _ QSlot2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as QSlot3.
    pose proof (FrameC _ _ Hdr2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as Hdr3.
    assert (Sh3 : rw_cells asegs m3 (f / 8 + 2147450880)
           [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]).
    { apply Keep3; [exact Sh2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      - apply (acl_fshadow _ _ _ f 0%nat); [exact InF |]. change (fs_size 0) with 64.
        rewrite (shad_add64 f 1 FAl). unfold shad, SHB. lia.
      - apply EfFar; [| lia]. destruct FHi as [Lw|Hg]; Z.div_mod_to_equations; lia. }
    assert (Frm3 : rw_cells asegs m3 (U + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply Keep3; [exact Frm2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      - apply acl_stack. unfold USTACK_TOP. subst V. lia.
      - apply EfFar; lia. }
    (* back from crypto: load the shelved state and call unshelve *)
    pose proof (ls_w3 (Z_to_bv 64 V) gp tp t0r t1r t2r sp (Z_to_bv 64 V) a1r a2r a3r a4r a5r a6r a7r
                  (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                  Fr fcr m3 lo (f + 32) ltac:(lia) ltac:(lia) QSlot3 ltac:(rewrite VIs; exact Stk3) LoHi
                  ltac:(rewrite VIs; subst V; lia) ltac:(rewrite VIs; subst V; lia) Inv3) as Walk3.
    cl_lift Walk3 Ast3' c4 Ast4.
    destruct (ASTA_unpack RT Σ3 PMc _ c4 Ast4) as (ms4 & Eq4 & Ast4'). clear Ast4. subst ms4.
    assert (Gap3 : stk asegs m3 V (U + -64)).
    { apply (stk_agree_nw asegs m2 m3 _ _ Gap2). intros x Hx. cbv beta in Hx. apply Pres3.
      - apply acl_stack. unfold USTACK_TOP. subst V. lia.
      - apply EfFar; lia. }
    (* the write set so far stays inside LS_W *)
    assert (ResOut : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) U x -> ~ (f + 32 <= x < f + 40)).
    { intros x Hx Hr. destruct (FApart x Hx) as (NF & _). lia. }
    assert (PresAll : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) U (LS_W j) m m3).
    { intros x Hx Ho.
      assert (Cl2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) V (bv_unsigned x)).
      { apply (aclient_mono _ _ U _ _ _ _ Hx); [rewrite LvS2; intros q Hq; right; right; right; exact Hq
                                              | rewrite FrS2; intros q Hq; right; exact Hq | subst V; lia]. }
      pose proof (ResOut _ Hx) as NR.
      unfold LS_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in Ho. cbn [outside] in Ho.
      rewrite (Pres3 x Cl2).
      - apply Pres2; [exact Hx|]. unfold SHV_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
      - unfold EFIRST_W, G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF.
        cbn [outside]. repeat split; try exact I; lia. }
    apply Kont. unfold AtUsh.
    exists Σ3, f, pd, MK, SA, P, pk, lh, B, L', g', bks', lb', u', m3, t0r, t1r, t2r, a2r, a3r, a4r, a5r, a6r, a7r, t3r, t4r, t5r, t6r, Fr, fcr, j8.
    split; [exact Ast4'|]. split; [exact PdCase|]. split; [exact PdIs|].
    split; [rewrite FrS3; exact FrS2|].
    split; [rewrite LvS2 in Perm3; exact Perm3|].
    split; [exact LenL|]. split; [exact GItems|].
    split; [rewrite SpS3; exact SpS2|]. split; [rewrite CrS2 in CrS3; lia|]. split; [rewrite CgS3; exact CgS2|].
    split; [exact Art3|]. split; [exact Inv3|]. split; [exact Stk3|]. split; [exact Gap3|]. split; [exact PresAll|]. split; [exact Env3|].
    do 4 (split; [assumption|]).
    split; [exact QErrno3|]. split; [exact QMkOnce3|]. split; [exact QMkInit3|]. split; [exact QMkKey3|]. split; [exact QNext3|].
    split; [exact QLock3|]. split; [exact QKeysJ3|]. split; [exact QCb3|]. split; [exact QT1503|]. split; [exact QTsdJ3|].
    split; [exact QMk3|]. split; [exact QSa3|]. split; [exact QP3|].
    split; [exact ErrSt3|]. split; [exact QPk3|]. split; [exact Lh3|]. split; [exact QLsRet3|].
    split; [exact Frm3|]. split; [exact Hdr3|]. split; [exact Sh3|].
    do 12 (split; [assumption|]).
    split; [exact FApart|]. exact BlkApart.
  }

  assert (st_unshelve : forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
      (canary : word) (j : Z) (e od sh oldcb r0 : word),
    mat_stable PMc -> tp = Z_to_bv 64 TP_A -> call_ok RT Σ m sp lo -> lo + RT_STACK + 832 <= bv_unsigned sp -> 1 <= j < 128 ->
    cps asegs (AtUsh Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e od sh oldcb r0)
      (fun c => exists (Σ' : rts RT) (MK SA P pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' u' : byte),
         ASTA RT Σ' PMc
           (fun ms => exists (m' : mem) (v : word),
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
              /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LS_W j) m m'
              /\ cl_env m' lb' canary
              /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
              /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
              /\ rw_cells asegs m' ERRNO_A [C4 (sx32 e)]
              /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
              /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
              /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
              /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
              /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)]
              /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
              /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 z64 (Z_to_bv 64 P))
              /\ rw_cells asegs m' P [C8 z64; CB 120 (zeros 120)]
              /\ err_statics m' pk lh /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks'
              /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)]) c
         /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
         /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ - 38 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
         /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP
         /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
         /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP
         /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP)).
  {

    assert (EpiA : forall (ra spv gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (F : bvmap 5 word) (fc : bv 32) (m : mem) (f : Z) (x0 r0 : word) (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
      0 < f -> f mod 64 = 0 -> SEGTOP_A <= f -> f + 64 <= 2147450880 \/ 17594333495296 <= f -> f + 64 <= 2 ^ 47 ->
      rw_cells asegs m f [C8 x0] ->
      rw_cells asegs m (f / 8 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
      rw_cells asegs m G_LS_RET [C4 r0] -> mem_inv asegs m ->
      evt asegs (fun ms => exists m' : mem,
          ms = MS (mkR ra spv gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 2047276) fc None m' (seg_rom asegs)
          /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (G_LS_RET, G_LS_RET + 4)] m m'
          /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' f [C8 (Z_to_bv 64 1172321806)]
          /\ rw_cells asegs m' (f / 8 + 2147450880)
               [C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245);
                C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245); C1 (Z_to_bv 8 245)]
          /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)])
        (MS (mkR ra spv gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 SITE_ls_ush)) fc None m (seg_rom asegs))).
    { intros ra spv gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f x0 r0 b0 b1 b2 b3 b4 b5 b6 b7
        FPos FAl FSeg FSh FTop Magic Shadow RetCell Inv.
      unfold G_LS_RET in RetCell |- *.
      pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (12186400, 12186400 + 4)] m) as Mu.
      pose proof (wmono_refl asegs m) as Wm.
      unfold SITE_ls_ush. th_ret_lit.
      zstep. zstep. zstep. th_sb.
      zstep. zstep. th_fix_lit_store.
      zstep. zstep. zstep. th_fix_lit_store.
      step. rewrite (Ubs.ubs_eqb0_false (Z_to_bv 64 f)) by (rewrite unsigned_lit by lia; lia). cbv iota.
      zstep.
      zstep. th_sb. zstep. th_sb. zstep. th_sb. zstep. th_sb.
      zstep. th_sb. zstep. th_sb. zstep. th_sb. zstep. th_sb.
      apply evt_done. eexists. split; [reflexivity|].
      split; [replace (f / 8 + 2147450880 + 8) with (f / 8 + 2147450888) in Mu by lia; exact Mu|].
      split; [exact Wm|]. split; [exact Inv|]. split; [exact Magic|]. split; [exact Shadow|]. exact RetCell. }

    assert (EpiB : forall (ra0 spv gp tp t0 t1 t2 sp s1v a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (F : bvmap 5 word) (fc : bv 32) (m : mem) (f fl : Z) (j8 : list byte) (s0' s1' s2' s3' s4' s5' rav : word),
      0 < f -> f + 64 <= 2 ^ 47 -> 0 < fl -> fl + 1 <= bv_unsigned sp - 64 -> 12345344 <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
      ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
      rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 rav] ->
      mem_inv asegs m ->
      evt asegs (fun ms => exists m' : mem,
          ms = MS (mkR rav sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc rav) fc None m' (seg_rom asegs)
          /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)]
          /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 rav])
        (MS (mkR ra0 spv gp tp t0 t1 t2 sp s1v a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3v s4v (Z_to_bv 64 f)
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 2047276) fc None m (seg_rom asegs))).
    { intros ra0 spv gp tp t0 t1 t2 sp s1v a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fl j8 s0' s1' s2' s3' s4' s5' rav
        FPos FTop FlPos FlLow ULow UTop Slot Flag Frame Inv.
      pose proof (munch_refl [(fl, fl + 1)] m) as Mu.
      pose proof (wmono_refl asegs m) as Wm.
      pose proof (bv_unsigned_in_range 64 sp) as URng. unfold bv_modulus in URng. cbn [Z.of_N] in URng.
      remember (bv_unsigned sp) as U eqn:UIs.
      rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- UIs.
      zstep. zstep. th_sb.
      zstep. zstep.
      do 7 zstep.
      zstep. zstep.
      apply evt_done. eexists. split; [reflexivity|].
      split; [exact Mu|]. split; [exact Wm|]. split; [exact Inv|]. split; [exact Flag|]. exact Frame. }

    intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e od sh oldcb r0 Mat TpIs CallA RoomA JIn.
    intros T c Bnd Kont. unfold AtUsh in Bnd.
    destruct Bnd as (Σ3 & f & pd & MK & SA & P & pk & lh & B & L' & g' & bks' & lb' & u' & m3
      & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & j8
      & Ast3 & PdCase & PdIs & FrS3 & Perm3 & LenL & GItems & SpS3 & CrS3 & CgS3 & Art3 & Inv3 & Stk3 & Gap3 & Pres3 & Env3
      & QStop & QOpts & QBOnce & QBRet & QErrno & QMkOnce & QMkInit & QMkKey & QNext & QLock & QKeysJ & QCb & QT150 & QTsdJ
      & QMk & QSa & QP & ErrSt & QPk & Lh & QLsRet & Frm & Hdr & Sh
      & MkPos & MkAl & MkTop & SaPos & SaAl & SaTop & PPos & PAl & PTop & PkPos & PkAl & PkTop & FApart & BlkApart).
    destruct CallA as (_ & WinA & _ & TopA & AlA).
    set (U := bv_unsigned sp) in *.
    unfold RT_STACK in RoomA. unfold USTACK_TOP in TopA.
    assert (PdBound : 0 <= pd <= 16) by lia.
    assert (InF : In (f, 0%nat) (rt_frames RT Σ3)) by (rewrite FrS3; left; reflexivity).
    pose proof (af_frames_range RT AF Σ3 m3 f 0%nat Art3 InF) as (FPos & FBelow & _ & FLive).
    pose proof (af_frames_align RT AF Σ3 m3 f 0%nat Art3 InF) as (FAl & FSeg).
    pose proof (af_frames_hi RT AF Σ3 m3 f 0%nat Art3 InF) as FHi.
    pose proof (af_fshadow_apart RT AF Σ3 m3 f 0%nat Art3 InF) as (FShLive & _).
    pose proof (af_sp0_win RT AF Σ3 m3 Art3) as Sp0W.
    change (fs_size 0) with 64 in FBelow, FHi, FLive, FShLive. rewrite SpS3 in FBelow, Sp0W.
    assert (Sh64 : shad (f + 64) = f / 8 + 2147450880 + 8) by (rewrite (shad_add64 f 1 FAl); unfold shad, SHB; lia).
    rewrite Sh64 in FShLive. unfold shad, SHB in FShLive.
    unfold SEGTOP_A in FSeg.
    assert (LoHi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in WinA; lia).
    set (V := U + -64 - pd) in *.
    assert (VIs : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; subst V; lia).
    (* the blocks shelve left, seen through crypto's permutation of the live list *)
    assert (InL3 : forall q, In q (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ) -> In q (rt_live RT Σ3))
      by (intros q Hq; exact (Permutation_in _ (Permutation_sym Perm3) Hq)).
    assert (InMK : In (MK, 72) (rt_live RT Σ3)) by (apply InL3; apply in_or_app; right; do 3 right; left; reflexivity).
    assert (InSA : In (SA, 32) (rt_live RT Σ3)) by (apply InL3; apply in_or_app; right; do 2 right; left; reflexivity).
    assert (InP : In (P, 128) (rt_live RT Σ3)) by (apply InL3; apply in_or_app; right; right; left; reflexivity).
    assert (BlkFacts : forall p n, In (p, n) (rt_live RT Σ3) -> 1 <= n <= 64512 ->
              0x10007fff8000 <= p /\ p + n <= lo /\ acc asegs m3 p n /\ (p + n <= 65536 \/ 12345344 <= p)).
    { intros p n Hin Hn. pose proof (af_live_range RT AF Σ3 m3 p n Art3 Hin) as (_ & P1 & P2).
      pose proof (afp_live_hi RT GOBJ AFP Σ3 m3 p n Art3 Hin ltac:(lia)) as PH.
      pose proof (af_acc_live RT AF Σ3 m3 p n Art3 Hin) as (_ & PA). rewrite SpS3 in P1. unfold SEGTOP_A in P2.
      split; [exact PH|]. split; [lia|]. split; [exact PA | exact P2]. }
    destruct (BlkFacts MK 72 InMK ltac:(lia)) as (MkHi & MkLo & MkAcc & _).
    destruct (BlkFacts SA 32 InSA ltac:(lia)) as (SaHi & SaLo & SaAcc & _).
    destruct (BlkFacts P 128 InP ltac:(lia)) as (PHi & PLo & PAcc & _).
    assert (PermSA : Permutation (rt_live RT Σ3) ((SA, 32) :: L' ++ (pk, 40) :: (P, 128) :: (MK, 72) :: rt_live RT Σ)).
    { eapply Permutation_trans; [exact Perm3|].
      replace (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
        with ((L' ++ [(pk, 40); (P, 128)]) ++ (SA, 32) :: (MK, 72) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
      replace (L' ++ (pk, 40) :: (P, 128) :: (MK, 72) :: rt_live RT Σ)
        with ((L' ++ [(pk, 40); (P, 128)]) ++ (MK, 72) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
      apply Permutation_sym, Permutation_middle. }
    assert (PermP : Permutation (rt_live RT Σ3) ((P, 128) :: L' ++ (pk, 40) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)).
    { eapply Permutation_trans; [exact Perm3|].
      replace (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
        with ((L' ++ [(pk, 40)]) ++ (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
      replace (L' ++ (pk, 40) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ)
        with ((L' ++ [(pk, 40)]) ++ (SA, 32) :: (MK, 72) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
      apply Permutation_sym, Permutation_middle. }
    assert (SaP : SA + 32 <= P \/ P + 128 <= SA).
    { apply (st_apart Σ3 m3 SA 32 _ P 128 Art3 PermSA). apply in_or_app. right. right. left. reflexivity. }
    (* the unshelve call *)
    pose proof (af_client_consts RT AF Σ3 m3 Art3) as (_ & Shb3 & _ & _ & Img3).
    pose proof (afp_gsh_byte RT GOBJ AFP Σ3 m3 MK_KEY 4 MK_KEY Art3 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KeySh.
    change (if 12186912 + 4 - 12186912 <? 8 then 12186912 + 4 - 12186912 else 0) with 4 in KeySh.
    pose proof (unshelve_proof (Z_to_bv 64 SITE_ls_ush) (Z_to_bv 64 V) gp tp t0' t1' t2' sp (Z_to_bv 64 V) (Z_to_bv 64 0) (Z_to_bv 64 0)
                  a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                  s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m3 lo j MK SA P z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 (-1))
                  (zeros 24) (zeros 40) (zeros 120)
                  TpIs ltac:(intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate)
                  (wg_rw_ro m3 _ _ QMkOnce) (wg_rw_ro m3 _ _ QMkKey) ltac:(lia) KeySh (wg_rw_ro m3 _ _ (TSD Σ3 m3 Art3))
                  (wg_rw_ro m3 _ _ QTsdJ) MkHi ltac:(clear - MkAl; Z.div_mod_to_equations; lia) MkLo MkAcc QMk
                  SaHi ltac:(clear - SaAl; Z.div_mod_to_equations; lia) SaLo SaAcc QSa
                  PHi ltac:(clear - PAl; Z.div_mod_to_equations; lia) PLo PAcc QP SaP Img3 Shb3
                  ltac:(rewrite VIs; exact Stk3) LoHi ltac:(rewrite VIs; subst V; lia) ltac:(rewrite VIs; subst V; lia) Inv3) as WalkU.
    cl_lift WalkU Ast3 c4 Ast4.
    destruct (ASTA_unpack RT Σ3 PMc _ c4 Ast4) as (ms4 & (t1u & a1u & a2u & a3u & topu & m4 & -> & Mu4 & Wm4 & Inv4 & Stk4 & TopEq & QSa4 & QP4) & Ast4').
    clear Ast4. rewrite VIs in Mu4, Stk4.

    assert (ShLo : f / 8 + 2147450880 + 8 <= lo).
    { assert (f / 8 <= (2 ^ 47 - 64) / 8) by (apply Z.div_le_mono; lia).
      change ((2 ^ 47 - 64) / 8) with 17592186044408 in H. lia. }
    assert (Keep34 : forall A cs, rw_cells asegs m3 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) -> ~ (V - 112 <= x < V) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8)) ->
              rw_cells asegs m4 A cs).
    { intros A cs H Hx. apply (rw_cells_agree asegs m3 m4 A cs H); [| exact Wm4]. intros x Hin. apply Mu4.
      destruct (Hx _ Hin) as (N1 & N2 & N3). cbn [outside]. repeat split; try exact I; assumption. }
    pose proof (Keep34 _ _ Hdr ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; repeat split;
                   [lia | destruct (FLive SA 32 InSA); lia | destruct (FLive P 128 InP); lia])) as Hdr4.
    pose proof (Keep34 _ _ Sh ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; repeat split;
                   [lia | destruct (FShLive SA 32 InSA); lia | destruct (FShLive P 128 InP); lia])) as Sh4.
    pose proof (Keep34 _ _ QLsRet ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold G_LS_RET in Hx; repeat split; lia)) as LsRet4.
    (* epilogue, first part: retire the fake frame *)
    pose proof (EpiA (Z_to_bv 64 SITE_ls_ush) (Z_to_bv 64 V) gp tp t0' t1u t2' sp (Z_to_bv 64 V) (Z_to_bv 64 1) a1u a2u a3u a4' a5' a6' a7'
                  s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m4 f (Z_to_bv 64 LS_MAGIC) r0
                  (Z_to_bv 8 (-15)) (Z_to_bv 8 (-15)) (Z_to_bv 8 (-15)) (Z_to_bv 8 (-15)) (Z_to_bv 8 0) (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13)) (Z_to_bv 8 (-13))
                  FPos FAl ltac:(unfold SEGTOP_A; lia) ltac:(lia) ltac:(lia) Hdr4 Sh4 LsRet4 Inv4) as WalkA.
    cl_lift WalkA Ast4' c5 Ast5.
    destruct (ASTA_unpack RT Σ3 PMc _ c5 Ast5) as (ms5 & (m5 & -> & Mu5 & Wm5 & Inv5 & Hdr5 & Sh5 & LsRet5) & Ast5'). clear Ast5.
    assert (Art5 : ART RT Σ3 m5).
    { apply (af_frame RT AF Σ3 m3 m5 lo Art3 ltac:(rewrite SpS3; exact WinA)); [| exact (wmono_trans asegs _ _ _ Wm4 Wm5)].
      intros x NotCl. rewrite (Mu5 x).
      - apply Mu4. cbn [outside]. repeat split; try exact I; intros Hin; apply NotCl.
        + apply acl_stack. unfold USTACK_TOP. lia.
        + apply (acl_live _ _ _ SA 32); [exact InSA | lia].
        + apply (acl_live _ _ _ P 128); [exact InP | lia].
      - cbn [outside]. unfold G_LS_RET. repeat split; try exact I; intros Hin; apply NotCl.
        + apply (acl_frame _ _ _ f 0%nat); [exact InF | change (fs_size 0) with 64; lia].
        + apply (acl_fshadow _ _ _ f 0%nat); [exact InF | change (fs_size 0) with 64; rewrite Sh64; unfold shad, SHB; lia].
        + apply acl_static, st_static; lia. }
    destruct (af_frame_release RT AF Σ3 m5 f 0%nat (rt_frames RT Σ) Art5 FrS3) as (Σ4 & fl & FlC & NAC & FlPos & FlTop & SlotRo & Rel).
    change (fs_size 0) with 64 in SlotRo. replace (f + 64 - 8) with (f + 56) in SlotRo by lia.
    rewrite SpS3 in FlTop.
    assert (Frm5 : rw_cells asegs m5 (U + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m4 m5 _ _ (Keep34 _ _ Frm ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; repeat split; lia)));
        [| exact Wm5].
      intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply Mu5. cbn [outside]. unfold G_LS_RET.
      repeat split; try exact I; lia. }
    (* epilogue, second part: release the fake frame and return *)
    pose proof (EpiB (Z_to_bv 64 SITE_ls_ush) (Z_to_bv 64 V) gp tp t0' t1u t2' sp (Z_to_bv 64 V) (Z_to_bv 64 (-11)) a1u a2u a3u a4' a5' a6' a7'
                  (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m5 f fl j8 s0 s1 s2 s3 s4 s5 ra
                  FPos ltac:(lia) FlPos ltac:(lia) ltac:(lia) ltac:(lia) SlotRo FlC Frm5 Inv5) as WalkB.
    cl_lift WalkB Ast5' c6 Ast6.
    destruct (ASTA_unpack RT Σ3 PMc _ c6 Ast6) as (ms6 & (m6 & -> & Mu6 & Wm6 & Inv6 & Fl6 & Frm6) & Ast6'). clear Ast6.
    destruct (Rel m6 Mu6 Wm6 Fl6) as (Art6 & FrS4 & LvS4 & SpS4 & CrS4 & AlS4 & AmS4 & CgS4).
    pose proof (ASTA_switch RT Σ3 Σ4 PMc _ c6 Ast6' AlS4 AmS4) as Ast6''. clear Ast6'.

    assert (VLo : lo <= V - 112) by (subst V; lia).
    assert (VU : V + 64 <= U) by (subst V; lia).
    (* what the code wrote after crypto: the unshelve stack and SA/P words, the retired frame, its shadow, G_LS_RET, the flag *)
    assert (Quiet : forall x : word,
              ~ (V - 112 <= bv_unsigned x < V) -> ~ (SA + 8 <= bv_unsigned x < SA + 24) -> ~ (P <= bv_unsigned x < P + 8) ->
              ~ (f <= bv_unsigned x < f + 8) -> ~ (f / 8 + 2147450880 <= bv_unsigned x < f / 8 + 2147450880 + 8) ->
              ~ (12186400 <= bv_unsigned x < 12186404) -> bv_unsigned x <> fl -> m6 x = m3 x).
    { intros x N1 N2 N3 N4 N5 N6 N7. rewrite (Mu6 x), (Mu5 x), (Mu4 x); [reflexivity | ..];
        cbn [outside]; unfold G_LS_RET; repeat split; try exact I; lia. }
    assert (Wm36 : wmono asegs m3 m6) by exact (wmono_trans asegs _ _ _ Wm4 (wmono_trans asegs _ _ _ Wm5 Wm6)).
    assert (Keep36 : forall A cs, rw_cells asegs m3 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
                 ~ (V - 112 <= x < V) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8) /\ ~ (f <= x < f + 8) /\
                 ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) /\ ~ (12186400 <= x < 12186404) /\ x <> fl) ->
              rw_cells asegs m6 A cs).
    { intros A cs H Hx. apply (rw_cells_agree asegs m3 m6 A cs H); [| exact Wm36]. intros x Hin.
      destruct (Hx _ Hin) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). exact (Quiet x N1 N2 N3 N4 N5 N6 N7). }
    assert (StatQ : forall x, client_static x -> ~ (12186400 <= x < 12186404) ->
                 ~ (V - 112 <= x < V) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8) /\ ~ (f <= x < f + 8) /\
                 ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) /\ ~ (12186400 <= x < 12186404) /\ x <> fl).
    { intros x Hs Hr. pose proof (client_static_range x Hs) as Rg. unfold SEGTOP_A in Rg.
      repeat split; try lia. intros ->. apply NAC. apply acl_static. exact Hs. }
    assert (LiveQ : forall q k x, In (q, k) (L' ++ (pk, 40) :: (MK, 72) :: rt_live RT Σ) -> q <= x < q + k ->
                 ~ (V - 112 <= x < V) /\ ~ (SA + 8 <= x < SA + 24) /\ ~ (P <= x < P + 8) /\ ~ (f <= x < f + 8) /\
                 ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) /\ ~ (12186400 <= x < 12186404) /\ x <> fl).
    { intros q k x Hin Hx.
      assert (InRest : forall z, In (q, k) (L' ++ (pk, 40) :: z :: (MK, 72) :: rt_live RT Σ)).
      { intros z. apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [left; exact H | right].
        destruct H as [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. }
      assert (In3 : In (q, k) (rt_live RT Σ3)).
      { apply InL3. pose proof Hin as Hin'. apply in_app_or in Hin'. apply in_or_app.
        destruct Hin' as [H|H]; [left; exact H | right].
        destruct H as [H|[H|H]]; [left; exact H | right; right; right; left; exact H | right; right; right; right; exact H]. }
      pose proof (af_live_range RT AF Σ3 m3 q k Art3 In3) as (Q0 & Q1 & Q2). rewrite SpS3 in Q1. unfold SEGTOP_A in Q2.
      destruct (st_apart Σ3 m3 SA 32 _ q k Art3 PermSA (InRest (P, 128))) as [D1|D1];
      destruct (st_apart Σ3 m3 P 128 _ q k Art3 PermP (InRest (SA, 32))) as [D2|D2];
      destruct (FLive q k In3) as [D3|D3]; destruct (FShLive q k In3) as [D4|D4];
      (repeat split; try (clear - Hx Q0 Q1 Q2 WinA VLo D1 D2 D3 D4; lia)); intros ->; apply NAC; apply (acl_live _ _ _ q k _ In3); clear - Hx; lia. }
    (* the client memory of the caller outside LS_W is unchanged *)
    assert (ClLow : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) U x -> U <= x \/ (x < lo /\ aclient (rt_live RT Σ3) (rt_frames RT Σ3) USTACK_TOP x)).
    { intros x Hx.
      assert (Up : forall z, In z (rt_live RT Σ) -> In z (rt_live RT Σ3))
        by (intros z Hz; apply InL3; apply in_or_app; right; do 4 right; exact Hz).
      assert (UpF : forall z, In z (rt_frames RT Σ) -> In z (rt_frames RT Σ3)) by (intros z Hz; rewrite FrS3; right; exact Hz).
      destruct (aclient_split RT AF Σ3 m3 U x Art3 (aclient_mono _ _ U _ _ U _ Hx Up UpF ltac:(lia))) as [Hi|Lo'];
        [left; exact Hi | right]. rewrite SpS3 in Lo'.
      split; [lia|].
      destruct Hx as [S|[S|[(p & n & Hi & Hr)|[(g & k & Hi & Hr)|(g & k & Hi & Hr)]]]].
      - lia.
      - apply acl_static. exact S.
      - apply (acl_live _ _ _ p n); [apply Up; exact Hi | exact Hr].
      - apply (acl_frame _ _ _ g k); [apply UpF; exact Hi | exact Hr].
      - apply (acl_fshadow _ _ _ g k); [apply UpF; exact Hi | exact Hr]. }
    assert (PresAll : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) U (LS_W j) m m6).
    { intros x Hx Ho. rewrite <- (Pres3 x Hx Ho).
      unfold LS_W, G_LS_RET in Ho. cbn [outside] in Ho.
      destruct Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NR & _).
      destruct (FApart _ Hx) as (NF1 & NF2). destruct (BlkApart _ Hx) as (NB1 & NB2).
      assert (LoU : lo < U) by (clear - RoomA; lia).
      destruct (ClLow _ Hx) as [Hi | (Lo' & Cl3)];
        (apply Quiet; intros R; [ | apply NB1 | apply NB2 | apply NF1 | apply NF2 | apply NR | ]).
      - clear - Hi R VU; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R Hi FlTop WinA LoU; lia.
      - clear - Lo' R VLo; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - clear - R; lia.
      - apply NAC. rewrite <- R. exact Cl3. }
    (* stack of the caller: the part below the frame, the pad gap, and the saved registers *)
    assert (Stk6 : stk asegs m6 lo U).
    { assert (Below : stk asegs m6 lo V).
      { apply (stk_agree_nw asegs m4 m6 _ _ Stk4). intros x Hx. cbv beta in Hx. rewrite (Mu6 x), (Mu5 x); [reflexivity| ..];
          cbn [outside]; unfold G_LS_RET; repeat split; try exact I; lia. }
      assert (Pad : stk asegs m6 V (U + -64)).
      { apply (stk_agree_nw asegs m3 m6 _ _ Gap3). intros x Hx. cbv beta in Hx. apply Quiet; lia. }
      pose proof (stk_of_rw_cells asegs m6 _ _ Frm6) as Top6. cbn [cells_size csize Nat.add] in Top6.
      replace (bv_unsigned sp + -64 + Z.of_nat 64) with U in Top6 by (subst U; lia).
      apply (stk_merge asegs m6 lo (U + -64) U); [apply (stk_merge asegs m6 lo V (U + -64)); [exact Below | exact Pad | lia] | exact Top6 | lia]. }
    (* the cells of the postcondition *)
    assert (Q6 : forall A cs, rw_cells asegs m3 A cs -> 12186000 <= A -> A + Z.of_nat (cells_size cs) <= 12343248 ->
               ~ (A < 12205728 /\ 12205720 < A + Z.of_nat (cells_size cs)) -> ~ (A < 12205848 /\ 12205800 < A + Z.of_nat (cells_size cs)) ->
               ~ (A < 12205872 /\ 12205856 < A + Z.of_nat (cells_size cs)) -> ~ (A < 12341920 /\ 12341912 < A + Z.of_nat (cells_size cs)) ->
               ~ (A < 12337592 /\ 12337584 < A + Z.of_nat (cells_size cs)) -> ~ (A < 12186404 /\ 12186400 < A + Z.of_nat (cells_size cs)) ->
               rw_cells asegs m6 A cs).
    { intros A cs H L1 L2 R1 R2 R3 R4 R5 R6. apply Keep36; [exact H|]. intros x Hx.
      apply StatQ; [apply st_static|]; clear - Hx L1 L2 R1 R2 R3 R4 R5 R6; lia. }

    assert (QSide : forall A cs, rw_cells asegs m3 A cs -> 12186000 <= A -> A + Z.of_nat (cells_size cs) <= 12186400 \/ 12186404 <= A /\ A + Z.of_nat (cells_size cs) <= 12205720 \/ 12205728 <= A /\ A + Z.of_nat (cells_size cs) <= 12205800 \/ 12205872 <= A /\ A + Z.of_nat (cells_size cs) <= 12337584 \/ 12337592 <= A /\ A + Z.of_nat (cells_size cs) <= 12341912 \/ 12341920 <= A /\ A + Z.of_nat (cells_size cs) <= 12343248 ->
               rw_cells asegs m6 A cs).
    { intros A cs H L1 L2. apply (Q6 A cs H L1); clear - L1 L2; lia. }
    assert (QStop6 : rw_cells asegs m6 G_IC_STOPPED [C1 (Z_to_bv 8 0)]) by (apply QSide; [exact QStop | unfold G_IC_STOPPED; lia | cbn; unfold G_IC_STOPPED; lia]).
    assert (QOpts6 : rw_cells asegs m6 G_IC_OPTSDONE [C8 od]) by (apply QSide; [exact QOpts | unfold G_IC_OPTSDONE; lia | cbn; unfold G_IC_OPTSDONE; lia]).
    assert (QBOnce6 : rw_cells asegs m6 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]) by (apply QSide; [exact QBOnce | unfold G_IC_BASE_ONCE; lia | cbn; unfold G_IC_BASE_ONCE; lia]).
    assert (QBRet6 : rw_cells asegs m6 G_IC_BASE_RET [C4 (Z_to_bv 64 1)]) by (apply QSide; [exact QBRet | unfold G_IC_BASE_RET; lia | cbn; unfold G_IC_BASE_RET; lia]).
    assert (QErrno6 : rw_cells asegs m6 ERRNO_A [C4 (sx32 e)]) by (apply QSide; [exact QErrno | lia | cbn; lia]).
    assert (QMkOnce6 : rw_cells asegs m6 MK_ONCE [C4 (Z_to_bv 64 2)]) by (apply QSide; [exact QMkOnce | lia | cbn; lia]).
    assert (QMkInit6 : rw_cells asegs m6 MK_INIT [C1 (Z_to_bv 8 1)]) by (apply QSide; [exact QMkInit | lia | cbn; lia]).
    assert (QMkKey6 : rw_cells asegs m6 MK_KEY [C4 (Z_to_bv 64 j)]) by (apply QSide; [exact QMkKey | lia | cbn; lia]).
    assert (QNext6 : rw_cells asegs m6 NEXT_KEY [C4 (Z_to_bv 64 j)]) by (apply QSide; [exact QNext | lia | cbn; lia]).
    assert (QLock6 : rw_cells asegs m6 KEY_LOCK [C4 z64; C4 z64; C4 sh]) by (apply QSide; [exact QLock | lia | cbn; lia]).
    assert (QKeysJ6 : rw_cells asegs m6 (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)])
      by (apply QSide; [exact QKeysJ | lia | cbn [cells_size csize Nat.add]; clear - JIn; lia]).
    assert (QCb6 : rw_cells asegs m6 (TP_A + -96) [C8 oldcb]) by (apply QSide; [exact QCb | lia | cbn; lia]).
    assert (QT1506 : rw_cells asegs m6 (TP_A + -150) [C1 u']) by (apply QSide; [exact QT150 | lia | cbn; lia]).
    assert (QTsdJ6 : rw_cells asegs m6 (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)])
      by (apply QSide; [exact QTsdJ | lia | cbn [cells_size csize Nat.add]; clear - JIn; lia]).
    assert (ErrSt6 : err_statics m6 pk lh).
    { destruct ErrSt as (E1 & E2 & E3 & E4). unfold err_statics.
      split; [apply QSide; [exact E1 | unfold G_ERR_ONCE; lia | cbn; unfold G_ERR_ONCE; lia]|].
      split; [apply QSide; [exact E2 | unfold G_ERR_FLAG; lia | cbn; unfold G_ERR_FLAG; lia]|].
      split; [apply QSide; [exact E3 | unfold G_ERR_LOCK; lia | cbn; unfold G_ERR_LOCK; lia]|].
      apply QSide; [exact E4 | unfold G_ERR_HASH; lia | cbn; unfold G_ERR_HASH; lia]. }
    assert (InBlk : forall q k A cs, In (q, k) (L' ++ (pk, 40) :: (MK, 72) :: rt_live RT Σ) -> rw_cells asegs m3 A cs ->
              q <= A -> A + Z.of_nat (cells_size cs) <= q + k -> rw_cells asegs m6 A cs).
    { intros q k A cs Hin H L1 L2. apply Keep36; [exact H|]. intros x Hx. apply (LiveQ q k x Hin). clear - Hx L1 L2; lia. }
    assert (QMk6 : rw_cells asegs m6 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]).
    { apply (InBlk MK 72); [apply in_or_app; right; right; left; reflexivity | exact QMk | lia | cbn [cells_size csize Nat.add]; lia]. }
    assert (QPk6 : rw_cells asegs m6 pk (mutex_cells z64 z64)).
    { apply (InBlk pk 40); [apply in_or_app; right; left; reflexivity | exact QPk | lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia]. }
    assert (Lh6 : lh_repE GOBJ m6 L' lh B g' bks').
    { destruct Lh as (LhR & LhP & LhA). split; [| split; [exact LhP | exact LhA]].
      apply (lh_rep_agree asegs _ _ m3 m6 _ _ _ _ _ _ _ _ _ _ LhR); [| intros; assumption].
      intros a Ha Hfp.
      assert (InL : exists q k, In (q, k) L' /\ q <= a < q + k).
      { destruct Hfp as [R|[R|(p & A & Hp & R)]].
        - exists lh, 104. split; [| exact R]. apply (Permutation_in _ (Permutation_sym LhP)). left. reflexivity.
        - exists B, (8 * g_na g'). split; [| exact R]. apply (Permutation_in _ (Permutation_sym LhP)). right. left. reflexivity.
        - exists A, 24. split; [| exact R]. apply (Permutation_in _ (Permutation_sym LhP)). right. right.
          apply (in_map (fun x : bptr * Z => (snd x, 24)) _ (p, A) Hp). }
      destruct InL as (q & k & HinL & Hr).
      destruct (LiveQ q k a ltac:(apply in_or_app; left; exact HinL) Hr) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
      unfold wa. split.
      - apply Quiet; rewrite unsigned_lit by exact Ha; assumption.
      - apply Wm36. }
    assert (QSa6 : rw_cells asegs m6 SA (sa_hdr (Z_to_bv 64 1) z64 z64 z64 (Z_to_bv 64 P))).
    { assert (TopZ : topu = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned topu), TopEq; reflexivity).
      rewrite TopZ in QSa4.
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + sa_delta (Z_to_bv 64 0) (Z_to_bv 64 (-1)))) with (Z_to_bv 64 0) in QSa4 by reflexivity.
      apply (rw_cells_agree asegs m4 m6 _ _ QSa4); [| exact (wmono_trans asegs _ _ _ Wm5 Wm6)].
      intros x Hx. cbv beta in Hx. unfold sa_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
      destruct (FLive SA 32 InSA) as [D3|D3]; destruct (FShLive SA 32 InSA) as [D4|D4];
      (rewrite (Mu6 x), (Mu5 x); [reflexivity| ..]); cbn [outside]; unfold G_LS_RET; repeat split; try exact I;
        try (clear - Hx D3 D4 SaHi; lia);
        intros R; apply NAC; apply (acl_live _ _ _ SA 32 _ InSA); clear - Hx R; lia. }
    assert (QP6 : rw_cells asegs m6 P [C8 z64; CB 120 (zeros 120)]).
    { apply (rw_cells_agree asegs m4 m6 _ _ QP4); [| exact (wmono_trans asegs _ _ _ Wm5 Wm6)].
      intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
      destruct (FLive P 128 InP) as [D3|D3]; destruct (FShLive P 128 InP) as [D4|D4];
      (rewrite (Mu6 x), (Mu5 x); [reflexivity| ..]); cbn [outside]; unfold G_LS_RET; repeat split; try exact I;
        try (clear - Hx D3 D4 PHi; lia);
        intros R; apply NAC; apply (acl_live _ _ _ P 128 _ InP); clear - Hx R; lia. }
    assert (LsRet6 : rw_cells asegs m6 G_LS_RET [C4 (Z_to_bv 64 1)]).
    { apply (rw_cells_agree asegs m5 m6 _ _ LsRet5); [| exact Wm6]. intros x Hx. cbv beta in Hx. unfold G_LS_RET in Hx.
      cbn [cells_size csize Nat.add] in Hx. apply Mu6. cbn [outside]. split; [| exact I].
      intros R. apply NAC. apply acl_static, st_static; clear - Hx R; lia. }
    assert (Env6 : cl_env m6 lb' canary).
    { apply (cl_env_agree m3 m6 lb' canary Env3). intros a Ha.
      assert (NotRet : ~ (12186400 <= bv_unsigned a < 12186404)).
      { destruct Ha as (lo' & hi' & HinC & Hr). unfold CL_CELLS in HinC. cbn [In] in HinC.
        unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in HinC.
        repeat (destruct HinC as [Eq|HinC]; [injection Eq as <- <-; clear - Hr; lia|]). destruct HinC. }
      destruct (StatQ _ (cl_cell_static _ Ha) NotRet) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
      exact (Quiet a N1 N2 N3 N4 N5 N6 N7). }
    apply Kont.
    exists Σ4, MK, SA, P, pk, lh, B, L', g', bks', lb', u'.
    split.
    - eapply ASTA_conseq; [exact Ast6''|]. intros ms <-. exists m6, (Z_to_bv 64 fl).
      split; [exists t0', t1u, t2', a1u, a2u, a3u, a4', a5', a6', a7', t3', t4', t5', t6', F', fc'; reflexivity|].
      split; [split; [exact Art6 | split; [exact Inv6 | exact Stk6]]|].
      split; [exact PresAll|]. split; [exact Env6|].
      split; [exact QStop6|]. split; [exact QOpts6|]. split; [exact QBOnce6|]. split; [exact QBRet6|].
      split; [exact QErrno6|]. split; [exact QMkOnce6|]. split; [exact QMkInit6|]. split; [exact QMkKey6|]. split; [exact QNext6|].
      split; [exact QLock6|]. split; [exact QKeysJ6|]. split; [exact QCb6|]. split; [exact QT1506|]. split; [exact QTsdJ6|].
      split; [exact QMk6|]. split; [exact QSa6|]. split; [exact QP6|].
      split; [exact ErrSt6|]. split; [exact QPk6|]. split; [exact Lh6|]. exact LsRet6.
    - split; [rewrite LvS4; exact Perm3|]. split; [exact LenL|]. split; [exact GItems|].
      split; [exact FrS4|]. split; [rewrite SpS4; exact SpS3|]. split; [rewrite CrS4; exact CrS3|]. split; [rewrite CgS4; exact CgS3|].
      repeat split; assumption.
  }
  unfold loadstr_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    nk j e od sh kold w oldcb lk0 h0 f0 r0 ib u
    Fds Mat TpIs Art0 Inv0 Call0 Room0 Ctx0 Uw0 Cg0 Fr0 Lv0 Cr0 Pos0 Env0
    QStop QOpts QBOnce QBRet QErrno QMkOnce QMkInit QMkKey QCb QT150 QNext NkIn QLock QKeysJ QKeysNk JAlt JPos QTsdJ
    QEOnce QELock QEHash QEFlag QLsRet.
  assert (JIn : 1 <= j < 128).
  { split; [exact JPos|]. destruct JAlt as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]. }
  eapply cps_seq.
  { exact (st_entry Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             Fds Mat TpIs Art0 Inv0 Call0 Room0 ltac:(lia) ltac:(lia)). }
  eapply cps_seq.
  { exact (st_shelve Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer lb canary nk j e od sh kold w oldcb ib u
             Fds Mat TpIs Call0 Room0 Ctx0 Uw0 Cg0 Fr0 Lv0 Cr0 Env0
             QStop QOpts QBOnce QBRet QErrno QMkOnce QMkInit QMkKey QCb QT150 QNext NkIn QLock QKeysJ QKeysNk JAlt JPos QTsdJ). }
  eapply cps_seq.
  { exact (st_crypto Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary j e od sh oldcb lk0 h0 f0 r0
             Fds Mat TpIs Call0 Room0 Ctx0 Uw0 Cg0 Fr0 Lv0 Cr0 Pos0 JIn QStop QOpts QBOnce QBRet QEOnce QELock QEHash QEFlag QLsRet). }
  exact (st_unshelve Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary j e od sh oldcb r0 Mat TpIs Call0 Room0 JIn).
Qed.
End LoadStr.
