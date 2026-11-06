(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhSpec3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition A_MALLOC : Z := 0x662d0.     (* [comment removed for export] *)
Definition A_FREE : Z := 0x66190.       (* [comment removed for export] *)

Definition callee_saved_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section Specs.
  Context {fx : FPState} {RN : run_ceil}.

  Definition regs_kept (R R' : bvmap 5 word) : Prop :=
    forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

  (* [comment removed for export] *)
  Definition ainv_t : Type := list (Z * Z) -> Z -> Z -> mem -> Model -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition malloc_pre (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (B C ret n sp : Z) : Prop :=
    m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
    bv_unsigned (getr R 10) = n /\ 1 <= n <= MH_NMAX /\
    bv_unsigned (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\
    getr R 4 = Z_to_bv 64 TPV /\
    (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) /\
    B + (n + MBLK) <= MH_GBUDGET /\ C + 1 <= LMAX.

  (* [comment removed for export] *)
  Definition malloc_ok (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc : list (Z * Z)) (B C ret n sp : Z) (c' : config) : Prop :=
    exists R' M' mdl' (p : word),
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\ getr R' 10 = p /\
      bv_unsigned p mod 16 = 0 /\ blk_ok (bv_unsigned p) n /\
      (forall b m, In (b, m) Lc -> bv_unsigned p + n <= b \/ b + m <= bv_unsigned p) /\
      (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + n -> M' a <> None /\ store_ok RSEGS M' a 1%nat = true) /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV ((bv_unsigned p, n) :: Lc) (B + (n + MBLK)) (C + 1) M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  (* [comment removed for export] *)
  Definition malloc_null (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc : list (Z * Z)) (B C ret sp : Z) (c' : config) : Prop :=
    exists R' M' mdl',
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\ getr R' 10 = Z_to_bv 64 0 /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV Lc B C M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  Definition malloc_cfg (R : bvmap 5 word) (M : mem) (mdl : Model) : config :=
    mkCfg (mkst R (Z_to_bv 64 A_MALLOC) M (seg_rom RSEGS)) mdl.


  (* [comment removed for export] *)
  Definition MALLOC_KATW (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      AINV Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      katw RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV stk R M mdl Lc B C ret n sp) (malloc_null AINV stk R M mdl Lc B C ret sp).


  (* [comment removed for export] *)
  Definition MALLOC_ALT_F (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      AINVF Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      kats RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV stk R M mdl Lc B C ret n sp) (malloc_null AINV stk R M mdl Lc B C ret sp).

  (* [comment removed for export] *)
  Definition MALLOC_BIG_R (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      MMAP_THRESHOLD <= n ->
      AINV_R Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      kats RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV_R stk R M mdl Lc B C ret n sp) (malloc_null AINV_R stk R M mdl Lc B C ret sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_pre (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc Lc' : list (Z * Z)) (B C B' C' ret sp : Z) (p : word) : Prop :=
    m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
    getr R 10 = p /\
    ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C)
     \/ exists m L1 L2, Lc = L1 ++ (bv_unsigned p, m) :: L2 /\ Lc' = L1 ++ L2
                         /\ B' = Z.max 0 (B - (m + MBLK)) /\ C' = Z.max 0 (C - 1)) /\
    bv_unsigned (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\
    getr R 4 = Z_to_bv 64 TPV /\
    (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true).

  Definition free_post (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc' : list (Z * Z)) (B' C' ret sp : Z) (c' : config) : Prop :=
    exists R' M' mdl',
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc' sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV Lc' B' C' M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  Definition free_cfg (R : bvmap 5 word) (M : mem) (mdl : Model) : config :=
    mkCfg (mkst R (Z_to_bv 64 A_FREE) M (seg_rom RSEGS)) mdl.

  Definition FREE_KAT (stk : Z) : Prop :=
    forall R M mdl Lc Lc' B C B' C' ret sp p,
      AINV Lc B C M mdl -> free_pre stk R M mdl Lc Lc' B C B' C' ret sp p ->
      kat RSEGS (free_cfg R M mdl) (free_post AINV stk R M mdl Lc' B' C' ret sp).

  (* [comment removed for export] *)
  Definition FREE_R (stk : Z) : Prop :=
    forall R M mdl Lc Lc' B C B' C' ret sp p,
      AINV_R Lc B C M mdl -> free_pre stk R M mdl Lc Lc' B C B' C' ret sp p ->
      kat RSEGS (free_cfg R M mdl) (free_post AINV_R stk R M mdl Lc' B' C' ret sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition A_LIBC_AUXV : Z := 0xaae28.
  Record first_env (M : mem) (mdl : Model) (auxw : Z) (avl : list (Z * Z)) : Prop := FE {
    fe_ctx : forall a, MLOCK <= a < CTX_END -> M (Z_to_bv 64 a) = None;    (* [comment removed for export] *)
    fe_auxv : cell M A_LIBC_AUXV 8 auxw;
    fe_av_rng : 0 <= auxw /\ auxw + 16 * (Z.of_nat (length avl) + 1) <= 2 ^ 63 /\ auxw mod 8 = 0;
    fe_av_keys : forall i kv, nth_error avl i = Some kv ->
                   cell M (auxw + 16 * Z.of_nat i) 8 (fst kv) /\ cell M (auxw + 16 * Z.of_nat i + 8) 8 (snd kv) /\
                   0 < fst kv < 2 ^ 64 /\ 0 <= snd kv < 2 ^ 64;
    fe_av_end : cell M (auxw + 16 * Z.of_nat (length avl)) 8 0;
    fe_av_rnd : forall kv, In kv avl -> fst kv = 25 ->
                  snd kv + 24 <= 2 ^ 63 /\ exists bs, length bs = 8%nat /\ rdn RSEGS M (Z_to_bv 64 (snd kv + 8)) 8%nat = Some bs;
    fe_pgsz : cell M A_PAGESIZE 8 4096;
    fe_locks : cell M A_NEED_LOCKS 1 0;
    fe_canary : exists v, cell M A_CANARY 8 v;
    fe_maps : vm_maps (m_vmmaps mdl) = [] /\ vm_noaccess (m_vmmaps mdl) = [];
    fe_brk : vm_brk (m_vmmaps mdl) = vm_start_brk (m_vmmaps mdl) /\
             bv_unsigned (vm_start_brk (m_vmmaps mdl)) mod 4096 = 0 /\
             IMG_HI <= bv_unsigned (vm_start_brk (m_vmmaps mdl)) /\
             bv_unsigned (vm_start_brk (m_vmmaps mdl)) + 2 ^ 31 + 8192 <= CEIL;
    fe_res : vm_reserved (m_vmmaps mdl) = segments_reserved RSEGS;
    fe_top : page_floor (alloc_top (m_vmmaps mdl)) = CEIL;
    fe_lim : VMLIM <= vm_limit (m_vmmaps mdl)
  }.


End Specs.

(* [comment removed for export] *)
Abbreviation MSTK := MSTK_M.
End UbMhSpec3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition mh_static (a : Z) : Prop := statb a \/ (CTX <= a < CTX_END).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Live.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  (* [comment removed for export] *)
  Lemma live_geom : forall p n, In (p, n) L ->
    exists y k off res, is_group st y /\ 0 <= k <= g_lastidx st y /\ s_slot st y k = SUser p n off res /\
      0 <= n /\ g_mem st y + 16 <= p /\ p + n <= g_slot_end st y k /\ g_slot_end st y k < gspan st y /\
      HEAPLO + 16 <= p /\ p + n < CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p).
  Proof.
    intros p n Hin. destruct (wL_in st L (WF_live st L HWF) p n Hin) as (y & k & o & r & Hy & Hk & Sy).
    pose proof (wG_each st L (WF_groups st L HWF) y Hy) as WG.
    pose proof (wg_slots st L y WG k Hk) as SW. rewrite Sy in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & A3 & A4 & A5 & _).
    pose proof (wg_stride st L y WG) as [S16 _]. destruct (group_range st L HWF y Hy) as [R1 R2].
    pose proof (group_img st L HWF y Hy) as [GI GS].
    assert (g_stride st y * (k + 1) <= g_stride st y * g_cnt st y) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    assert (0 <= g_stride st y * k) by (apply Z.mul_nonneg_nonneg; lia).
    exists y, k, o, r. split; [exact Hy|]. split; [exact Hk|]. split; [exact Sy|].
    unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *. repeat split; hlia.
  Qed.

  Lemma live_zone : forall p n, In (p, n) L -> HEAPLO + 16 <= p /\ p + n <= CEIL /\ 0 <= n /\ (p + n <= IMG_LO \/ IMG_HI <= p).
  Proof. intros p n Hin. destruct (live_geom p n Hin) as (y & k & o & r & _ & _ & _ & N & _ & _ & _ & P1 & P2 & P3). split; [lia|]. split; [lia|]. split; [lia | exact P3]. Qed.

  Lemma live_appb : forall p n a, In (p, n) L -> p <= a < p + n -> appb st a.
  Proof.
    intros p n a Hin Ha. destruct (live_geom p n Hin) as (y & k & o & r & Hy & Hk & Sy & _).
    exists y, k, p, n, o, r. repeat split; try assumption; lia.
  Qed.

  Lemma live_disj : forall L1 L2 b m b' m', L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
  Proof.
    intros L1 L2 b m b' m' EL Hin'.
    assert (Hin : In (b, m) L) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
    assert (HinL' : In (b', m') L) by (rewrite EL; apply in_app_iff in Hin'; apply in_app_iff; destruct Hin' as [X|X]; [left; exact X | right; right; exact X]).
    assert (NE : (b, m) <> (b', m')).
    { intros E. pose proof (wL_nodup st L (WF_live st L HWF)) as ND. apply NoDup_ListNoDup in ND. rewrite EL in ND.
      apply NoDup_remove_2 in ND. apply ND. rewrite E. exact Hin'. }
    destruct (wL_in st L (WF_live st L HWF) b m Hin) as (y & k & o & r & Hy & Hk & Sy).
    destruct (wL_in st L (WF_live st L HWF) b' m' HinL') as (y' & k' & o' & r' & Hy' & Hk' & Sy').
    destruct (decide ((y, k) = (y', k'))) as [E|NE2].
    - exfalso. injection E. intros <- <-. rewrite Sy in Sy'. injection Sy'. intros _ _ <- <-. exact (NE eq_refl).
    - exact (ge_app_disj st (WF_geom st L HWF) y k y' k' b m o r b' m' o' r' Hy Hy' Hk Hk' Sy Sy' NE2).
  Qed.
End Live.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AppFrame.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Variable W : Z -> Prop.                      (* [comment removed for export] *)
  Hypothesis Wimg : forall a, W a -> IMG_LO <= a < IMG_HI /\ ~ mh_static a.
  (* [comment removed for export] *)
  Hypothesis CH : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    ((exists p n, In (p, n) L /\ p <= a < p + n) \/ CEIL <= a \/ W a) /\ M' (Z_to_bv 64 a) <> None.

  Lemma dfoot_rng : forall a, dfoot st a -> 0 <= a < 2 ^ 64.
  Proof.
    intros a [Fa|[Fa|[(ar & Har & Fa)|(x & Hx & Kx & Fa)]]]; unfold A_ERRNO, TPV, CTX_END, CTX in *; try lia.
    - destruct (wa_rng st (WF_areas st L HWF) ar Har) as (_ & R1 & R2). ceil; unfold HEAPLO in *. lia.
    - destruct (group_range st L HWF x Hx) as [R _].
      pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KD. rewrite Kx in KD.
      destruct KD as (_ & Kreg & _). destruct (wr_rng st (WF_regions st L HWF) _ Kreg) as (_ & R2 & _). cbn in R2.
      ceil; unfold HEAPLO in *. lia.
  Qed.

  Lemma app_keep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Proof.
    intros a Fa D. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact D|].
    exact (proj2 (CH a (dfoot_rng a Fa) NE)).
  Qed.

  (* [comment removed for export] *)
  Lemma ch_low : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> a < CEIL ->
    (exists p n, In (p, n) L /\ p <= a < p + n) \/ W a.
  Proof.
    intros a Hr NE Hc. destruct (CH a Hr NE) as [[X|[X|X]] _]; [left; exact X | lia | right; exact X].
  Qed.

  (* [comment removed for export] *)
  Lemma ch_img : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> IMG_LO <= a < IMG_HI -> W a.
  Proof.
    intros a Hr NE Ha. destruct (ch_low a Hr NE ltac:(ceil; lia)) as [(p & n & Hin & Hpa)|Wa]; [exfalso | exact Wa].
    destruct (live_zone st L HWF p n Hin) as (_ & _ & _ & IMGp). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ch_obj : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> a < CEIL -> (a < IMG_LO \/ IMG_HI <= a) ->
    exists p n, In (p, n) L /\ p <= a < p + n.
  Proof.
    intros a Hr NE Hc Ho. destruct (ch_low a Hr NE Hc) as [X|Wa]; [exact X | exfalso].
    destruct (Wimg a Wa) as [R _]. lia.
  Qed.

  Theorem REP_app_frame : REP st M'.
  Proof.
    constructor.
    - apply (rep_statics_tr_s st st M M' HREP app_keep); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      assert (IMGa : IMG_LO <= a < IMG_HI).
      { unfold statb, A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, A_TAB_CTZ, A_TAB_SC, A_TAB_MED in *. lia. }
      exact (proj2 (Wimg a (ch_img a Hr NE IMGa)) (or_introl Ha)).
    - apply (rep_ctx_tr st st M M' HREP app_keep (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        assert (IMGa : IMG_LO <= a < IMG_HI) by (unfold CTX_END, CTX in *; lia).
        exact (proj2 (Wimg a (ch_img a Hr NE IMGa)) (or_intror Ha)).
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st L M M' HWF HREP app_keep (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        pose proof (area_img st L HWF ar Har) as AI.
        destruct (ch_obj a ltac:(ceil; unfold HEAPLO in *; lia) NE ltac:(ceil; lia) ltac:(lia)) as (p & n & Hin & Hpa).
        apply (ge_app_area st (WF_geom st L HWF) a); [exact (live_appb st L HWF p n a Hin Hpa) | exists ar; split; [exact Har | exact Ha]].
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st st L M M' HWF HREP app_keep); try (intros; assumption).
      + intros; repeat split; reflexivity.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. pose proof (gcell_in_span st L HWF x a Hx G). destruct (group_range st L HWF x Hx).
        pose proof (group_img st L HWF x Hx) as [GI GS].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (ch_obj a ltac:(ceil; unfold HEAPLO in *; lia) NE ltac:(lia) ltac:(lia)) as (p & n & Hin & Hpa).
        exact (ge_app_cell st (WF_geom st L HWF) x a Hx G (live_appb st L HWF p n a Hin Hpa)).
      + intros x a Hx G. left. exact G.
  Qed.
End AppFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Props.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Definition swin_ok (SWIN : list (Z * Z)) : Prop :=
    forall lo hi a, In (lo, hi) SWIN -> lo <= a < hi -> IMG_LO <= a < IMG_HI /\ ~ mh_static a.





  Definition app_write (SWIN : list (Z * Z)) (L : list (Z * Z)) (M M' : mem) : Prop :=
    forall a : word, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None.

  Lemma REP_app_write : forall SWIN st L M M', swin_ok SWIN -> WF st L -> REP st M -> app_write SWIN L M M' -> REP st M'.
  Proof.
    intros SWIN st L M M' HS HWF HREP CH.
    apply (REP_app_frame st L M M' HWF HREP (in_wins SWIN)).
    - intros a (lo & hi & Hin & Ha). exact (HS lo hi a Hin Ha).
    - intros a Hr NE. destruct (CH (Z_to_bv 64 a) NE) as [X D]. rewrite u_Z2bv in X by lia. split; [|exact D].
      destruct X as [(b & n & Hin & Hb)|[X|X]]; [left; exists b, n; split; assumption | right; left; exact X | right; right; exact X].
  Qed.

  Theorem AINV_frame : forall (SWIN : list (Z * Z)) L B C M M' mdl,
    swin_ok SWIN -> AINV L B C M mdl -> app_write SWIN L M M' -> AINV L B C M' mdl.
  Proof.
    intros SWIN L B C M M' mdl HS ((st & HWF & HREP & HLG & NJ & NL) & HB & HC & HV) CH.
    split; [|split; [exact HB | split; [exact HC | exact HV]]].
    exists st. split; [exact HWF|]. split; [exact (REP_app_write SWIN st L M M' HS HWF HREP CH)|].
    split; [exact HLG|]. split; [exact NJ | exact NL].
  Qed.


  Theorem AINV_R_frame : forall (SWIN : list (Z * Z)) L B C M M' mdl,
    swin_ok SWIN -> AINV_R L B C M mdl -> app_write SWIN L M M' -> AINV_R L B C M' mdl.
  Proof.
    intros SWIN L B C M M' mdl HS ((st & HWF & HREP & HLG & NJ & NL & LO) & HB & HC & HV) CH.
    split; [|split; [exact HB | split; [exact HC | exact HV]]].
    exists st. split; [exact HWF|]. split; [exact (REP_app_write SWIN st L M M' HS HWF HREP CH)|].
    split; [exact HLG|]. split; [exact NJ|]. split; [exact NL | exact LO].
  Qed.

  Theorem AINV_vm : forall L B C M mdl mdl', AINV L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINV L B C M mdl'.
  Proof. intros L B C M mdl mdl' (HM & HB & HC & HV) E. unfold AINV. rewrite E. repeat split; assumption. Qed.

  Theorem AINV_R_vm : forall L B C M mdl mdl', AINV_R L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINV_R L B C M mdl'.
  Proof. intros L B C M mdl mdl' (HM & HB & HC & HV) E. unfold AINV_R. rewrite E. repeat split; assumption. Qed.

  Theorem AINV_mono : forall L B C B' C' M mdl, AINV L B C M mdl -> B <= B' -> C <= C' -> AINV L B' C' M mdl.
  Proof. intros L B C B' C' M mdl (HM & HB & HC & HV) H1 H2. unfold AINV. repeat split; try assumption; lia. Qed.

  Theorem AINV_R_mono : forall L B C B' C' M mdl, AINV_R L B C M mdl -> B <= B' -> C <= C' -> AINV_R L B' C' M mdl.
  Proof. intros L B C B' C' M mdl (HM & HB & HC & HV) H1 H2. unfold AINV_R. repeat split; try assumption; lia. Qed.

  Theorem AINV_zone : forall L B C M mdl b m, AINV L B C M mdl -> In (b, m) L -> blk_ok b m.
  Proof.
    intros L B C M mdl b m ((st & HWF & _) & _) Hin. destruct (live_zone st L HWF b m Hin) as (Z1 & Z2 & _ & Z3).
    split; [exact Z1|]. split; [exact Z2 | exact Z3].
  Qed.

  Theorem AINV_disj : forall L B C M mdl L1 L2 b m b' m',
    AINV L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
  Proof.
    intros L B C M mdl L1 L2 b m b' m' ((st & HWF & _) & _) EL Hin. exact (live_disj st L HWF L1 L2 b m b' m' EL Hin).
  Qed.


  (* [comment removed for export] *)
  Lemma WF_Lequiv : forall st L L', WF st L -> (forall x, In x L' <-> In x L) -> NoDup L' -> length L' = length L -> WF st L'.
  Proof.
    intros st L L' HWF EQ ND LEN. pose proof HWF as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split.
    - destruct C4 as [GND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      intros x Hx. pose proof (EACH x Hx) as WG.
      destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
      constructor; try assumption.
      intros k Hk. pose proof (Slots k Hk) as SW. destruct (s_slot st x k); cbn [slot_wf] in *; try exact SW.
      destruct SW as (A1 & A2 & A3 & A4 & A5 & A6 & A7). repeat (split; [assumption|]). apply EQ. exact A7.
    - split; [exact C5|]. split; [|split; [exact C7 | exact C8]].
      destruct C6 as [IN ND0 FUN LEN0]. constructor.
      + intros q nq Hin. apply IN. apply EQ. exact Hin.
      + exact ND.
      + exact FUN.
      + rewrite LEN. exact LEN0.
  Qed.

  Lemma PHI_perm : forall L L', Permutation L L' -> PHI L = PHI L'.
  Proof. intros L L' P. induction P; cbn; lia. Qed.

  Theorem AINV_perm : forall L L' B C M mdl, Permutation L L' -> AINV L B C M mdl -> AINV L' B C M mdl.
  Proof.
    intros L L' B C M mdl P ((st & HWF & HREP & HLG & NJ & NL) & HB & HC & HV).
    split; [|split; [rewrite <- (PHI_perm L L' P); exact HB | split; [rewrite <- (Permutation_length P); exact HC | exact HV]]].
    exists st. split; [|split; [exact HREP | split; [exact HLG | split; [exact NJ | exact NL]]]].
    apply (WF_Lequiv st L L' HWF).
    - intros x. split; intros H; [apply (Permutation_in _ (Permutation_sym P) H) | apply (Permutation_in _ P H)].
    - apply NoDup_ListNoDup. apply (Permutation_NoDup P). apply NoDup_ListNoDup. exact (wL_nodup st L (WF_live st L HWF)).
    - symmetry. apply Permutation_length. exact P.
  Qed.

End Props.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set_errno (st : mst) (e : Z) : mst :=
  MST (s_ctx st) (s_areas st) (s_meta st) (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
      (s_slot st) (s_regions st) (s_brk st) (s_canary st) e (s_limbo st).

Section Errno.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma SLe : forall st e, same_layout st (set_errno st e).
  Proof. intros st e. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  Lemma WF_set_errno : forall st L e, WF st L -> 0 <= e < 2 ^ 32 -> WF (set_errno st e) L.
  Proof.
    intros st L e HWF He. pose proof HWF as (C & A & Ls & G & Ge & Lv & R & WI). pose proof (SLe st e) as SL.
    split.
    { destruct C; constructor; assumption. }
    split; [exact (wf_areas_ext st _ SL A)|].
    split.
    { destruct Ls; constructor; assumption. }
    split.
    { destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      intros x Hx. pose proof (EACH x Hx) as WG. destruct WG; constructor; assumption. }
    split; [exact (wf_geom_ext st _ L SL HWF Ge)|].
    split; [exact (wf_live_ext st _ L SL Lv) |]. split; [exact (wf_regions_ext st _ L SL HWF eq_refl R) | exact (wf_img_ext st _ SL (WF_img st L HWF))].
  Qed.

  Lemma LEDGER_set_errno : forall st e vm, LEDGER st vm -> LEDGER (set_errno st e) vm.
  Proof. intros st e vm [A B C D E]. constructor; cbn; assumption. Qed.

  (* [comment removed for export] *)
  Definition errno_write (M M' : mem) (e : Z) : Prop :=
    cell M' A_ERRNO 4 e /\
    forall a : word, M' a <> M a -> A_ERRNO <= bv_unsigned a < A_ERRNO + 4 /\ M' a <> None.

  Lemma REP_set_errno : forall st L (M M' : mem) e, WF st L -> REP st M -> errno_write M M' e -> REP (set_errno st e) M'.
  Proof.
    intros st L M M' e HWF HREP [CE EW].
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (A_ERRNO <= a < A_ERRNO + 4) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hr OUT. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (EW _ NE) as [IN _]. rewrite u_Z2bv in IN by lia. exact (OUT IN). }
    assert (KEEP : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).
    { intros a Fa D. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact D|].
      exact (proj2 (EW _ NE)). }
    constructor.
    - pose proof (rp_statics st M HREP) as [A1 A2 A3 A4 A5 A6 A7 A8].
      assert (LOW : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= A_ERRNO \/ A_ERRNO + 4 <= a) -> cell M a k v -> cell M' a k v).
      { intros a k v Ha Hk Hd C. eapply cell_agree; [exact Ha | exact Hk | | exact C]. intros y Hy Ry. cbv beta in Ry. apply AG; [lia|]. lia. }
      constructor; cbn [s_canary s_errno set_errno];
        try (eapply LOW; [ unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                         | cbn; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                         | cbn; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                         | eassumption ]).
      + exact CE.
      + intros a Ha. rewrite AG; [exact (A7 a Ha) | unfold A_TAB_CTZ in Ha; lia | unfold A_TAB_CTZ, A_ERRNO, TPV in *; lia].
      + intros a Ha. rewrite AG; [exact (A8 a Ha) | unfold A_TAB_SC, A_TAB_MED in Ha; lia | unfold A_TAB_SC, A_TAB_MED, A_ERRNO, TPV in *; lia].
    - apply (rep_ctx_tr st (set_errno st e) M M' HREP KEEP (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). cbv beta. apply AG; [exact Hr|]. unfold CTX_END, CTX, A_ERRNO, TPV in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st (set_errno st e) L M M' HWF HREP KEEP (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        pose proof (area_img st L HWF ar Har) as AI.
        apply NE. apply AG; [ceil; unfold HEAPLO in *; lia|]. unfold A_ERRNO, TPV in *. lia.
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st (set_errno st e) L M M' HWF HREP KEEP); try (intros; assumption).
      + intros; repeat split; reflexivity.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. cbn in Hx. pose proof (gcell_in_span st L HWF x a Hx G). destruct (group_range st L HWF x Hx).
        pose proof (group_img st L HWF x Hx) as [GI GS].
        apply AG; [ceil; unfold HEAPLO in *; lia|]. unfold gspan, A_ERRNO, TPV in *. lia.
      + intros x a Hx G. left. exact G.
  Qed.

  Theorem AINV_errno : forall L B C M M' mdl e,
    AINV L B C M mdl -> 0 <= e < 2 ^ 32 -> errno_write M M' e -> AINV L B C M' mdl.
  Proof.
    intros L B C M M' mdl e ((st & HWF & HREP & HLG & NJ & NL) & HB & HC & HV) He EW.
    split; [|split; [exact HB | split; [exact HC | exact HV]]].
    exists (set_errno st e). split; [exact (WF_set_errno st L e HWF He)|]. split; [exact (REP_set_errno st L M M' e HWF HREP EW)|].
    split; [exact (LEDGER_set_errno st e _ HLG)|]. split; [exact NJ | exact NL].
  Qed.

End Errno.
