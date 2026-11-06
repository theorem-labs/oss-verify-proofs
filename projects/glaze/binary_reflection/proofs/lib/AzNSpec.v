(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.


(* [comment removed for export] *)
Definition em64 (M : word -> option byte) (a : Z) (w : Z) : Prop :=
  exists bs, (forall i, (i < 8)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)))
             /\ length bs = 8%nat /\ bytes_le_to_Z bs = w.

Definition regs_kept (R R' : bvmap 5 word) : Prop :=
  forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

(* [comment removed for export] *)
Definition ablk_ok {RC : run_ceil} (G : gtable) (p n : Z) : Prop :=
  PTRLO <= p /\ p + n <= CEIL_run /\ (p + n <= g_img_lo G \/ g_img_hi G <= p) /\ (p + n <= SHMAPLO \/ KHI <= p).

Section NSpec.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FTOPc : Z.
Variable G : gtable.
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Variable AINVN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
(* [comment removed for export] *)
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
Variable bcap ccap : Z.

(* [comment removed for export] *)
Definition nvisible (Lc Lf : list (Z * Z)) (z : Z) : Prop :=
  in_blocks Lc z \/ in_blocks Lf z \/ in_lshadow (Lc ++ Lf) z \/ in_sshadow z \/ in_ishadow G z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_pshadow (W : list (Z * Z)) (z : Z) : Prop :=
  exists lo hi, In (lo, hi) W /\ lo < hi /\ in_shadow SB lo (hi - lo) z.

(* [comment removed for export] *)
Definition nkept (Lc Lf : list (Z * Z)) (scr : word -> Prop) (a : word) : Prop :=
  ((in_blocks Lc (u a) \/ in_blocks Lf (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a)) /\ ~ scr a
   /\ (errw G (u a) -> in_blocks Lc (u a) \/ in_blocks Lf (u a) \/ CEIL_run <= u a))     (* [comment removed for export] *)
  \/ (g_ro_lo G <= u a < g_img_hi G /\ ~ in_wins (g_privx G) (u a))
  \/ in_lshadow (Lc ++ Lf) (u a)
  \/ in_sshadow (u a)
  \/ in_ishadow G (u a)
  \/ in_pshadow PERMc (u a).                                             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition errno_kept (M M' : word -> option byte) : Prop := forall a : word, errw G (u a) -> M a <> None -> M' a <> None.

Definition scratch (sp stk : Z) (a : word) : Prop := sp - stk <= u a < sp.
Definition noscratch (a : word) : Prop := False.

Definition scratch_ok (M' : word -> option byte) (sp stk : Z) : Prop :=
  forall a : word, scratch sp stk a -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true.

(* [comment removed for export] *)
Definition ncall_pre (R : bvmap 5 word) (M : word -> option byte) (ret sp stk : Z) : Prop :=
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0
  /\ u (getr R (Z_to_bv 5 2)) = sp /\ sp mod 16 = 0 /\ SFLOOR + stk <= sp /\ sp <= SPTOPc /\ sp + 16 <= two47   (* [comment removed for export] *)
  /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)
  /\ (forall a : word, scratch sp stk a -> RiscvSemantics.store_ok SEGS M a 1 = true).

(* [comment removed for export] *)
Definition nmodel (mdl mdl' : Model) : Prop :=
  m_halted mdl' = None /\ m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nmalloc_post_ok (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (Lc Lf : list (Z * Z)) (B C K n sp stk : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) (p : word) : Prop :=
  FXOK fx' /\ regs_kept R R' /\ getr R' (Z_to_bv 5 10) = p
  /\ u p mod 16 = 0 /\ ablk_ok G (u p) n
  /\ (64512 < n -> u p mod 4096 = 2048)                                          (* [comment removed for export] *)
  /\ (forall b m, In (b, m) (Lc ++ Lf) -> u p + n <= b \/ b + m <= u p)
  /\ (forall z, in_wins PERMc z -> ~ (u p <= z < u p + n))                       (* [comment removed for export] *)
  /\ (forall a : word, u p <= u a < u p + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true)
  /\ (forall z, u p <= z < u p + n -> exists b : byte, M' (Z_to_bv 64 (SB + z / 8)) = Some b /\ (u b = 0 \/ z mod 8 < u b <= 7))   (* [comment removed for export] *)
  /\ (forall a : word, in_shadow SB (u p) n (u a) -> RiscvSemantics.store_ok SEGS M' a 1 = true)
  /\ (forall a : word, nkept Lc Lf (scratch sp stk) a -> M' a = M a) /\ errno_kept M M'
  /\ scratch_ok M' sp stk
  /\ AINV ((u p, n) :: Lc) Lf (B + mcost n) (C + MCNT) (K + kcost n) M' mdl'
  /\ nmodel mdl mdl'.
Definition nmalloc_post_null (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (Lc Lf : list (Z * Z)) (B C K n sp stk : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) : Prop :=
  FXOK fx' /\ regs_kept R R' /\ getr R' (Z_to_bv 5 10) = Z_to_bv 64 0
  /\ (forall a : word, nkept Lc Lf (scratch sp stk) a -> M' a = M a) /\ errno_kept M M'
  /\ scratch_ok M' sp stk
  /\ AINVN n Lc Lf B C K M' mdl'                                        (* [comment removed for export] *)
  /\ nmodel mdl mdl'.
(* [comment removed for export] *)
Definition nmalloc_pre (fpcreq : bool) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (Lc Lf : list (Z * Z)) (B C K ret n sp stk : Z) : Prop :=
  m_halted mdl = None /\ FXOK fx /\ AINV Lc Lf B C K M mdl /\ ncall_pre R M ret sp stk
  /\ u (getr R (Z_to_bv 5 10)) = n /\ 1 <= n <= NMAX
  /\ (fpcreq = true -> FPC M (u (getr R (Z_to_bv 5 8))) sp)          (* [comment removed for export] *)
  /\ B + mcost n <= bcap /\ C + MCNT <= ccap /\ K + kcost n <= GKCAP.

(* [comment removed for export] *)
Definition malloc_nspec2 (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
           (stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret n sp : Z) Tok Tnull,
    nmalloc_pre true fx R M mdl Lc Lf B C K ret n sp stk -> FRESH Lc Lf B C K M mdl n -> Tok [] -> Tnull [] ->
    (forall fx' R' M' mdl' (p : word), nmalloc_post_ok R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') Tok) ->
    (forall fx' R' M' mdl', nmalloc_post_null R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' -> RZ (cfg fx' R' ret M' mdl') Tnull) ->
    RZ (cfg fx R entry M mdl) (t_alt2 Tnull Tok).

(* [comment removed for export] *)
Definition malloc_nspec1 (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
           (stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret n sp : Z) Tok,
    nmalloc_pre true fx R M mdl Lc Lf B C K ret n sp stk -> FRESH Lc Lf B C K M mdl n -> Tok [] ->
    (forall fx' R' M' mdl' (p : word), nmalloc_post_ok R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') Tok) ->
    RZ (cfg fx R entry M mdl) Tok.

(* [comment removed for export] *)
Definition malloc_nspec (stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret n sp : Z) T,
    nmalloc_pre true fx R M mdl Lc Lf B C K ret n sp stk -> T [] ->
    (forall fx' R' M' mdl' (p : word), nmalloc_post_ok R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    (forall fx' R' M' mdl', nmalloc_post_null R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition alloc1_nspec (XTRA : (word -> option byte) -> Prop) (stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret n sp : Z) T,
    nmalloc_pre false fx R M mdl Lc Lf B C K ret n sp stk -> XTRA M -> m_fds mdl = APS.fds_std -> Z.of_nat (length Lf) + 1 <= FTOPc -> T [] ->
    (forall fx' R' M' mdl' (p : word), nmalloc_post_ok R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nopnew_x (M : word -> option byte) : Prop :=
  forall E, Forall (fun K => AX2S.kentry_ok SEGS E M K) (g_opnew_kn G).


(* [comment removed for export] *)
Definition free_nspec (stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lc' Lf B C K B' C' K' (ret sp : Z) (p : word) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp stk ->
    getr R (Z_to_bv 5 10) = p ->
    FPC M (u (getr R (Z_to_bv 5 8))) sp ->
    ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C /\ K' = K)
     \/ exists m L1 L2, Lc = L1 ++ (u p, m) :: L2 /\ Lc' = L1 ++ L2
                         /\ Z.max 0 (B - mcost m) <= B' /\ Z.max 0 (C - MCNT) <= C' /\ K' = K + KFREE /\ K' <= GKCAP) ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, nkept Lc' Lf (scratch sp stk) a -> M' a = M a) -> errno_kept M M' ->
        scratch_ok M' sp stk ->
        AINV Lc' Lf B' C' K' M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition stkmal_nspec (k : Z) : Prop :=
  let n := 64 * 2 ^ k in
  forall fx R M mdl Lc Lf B C K (ret sp : Z) T,
    0 <= k <= 3 ->
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp MSTK_F ->
    Z.of_nat (length Lf) + 1 <= FTOPc ->
    (forall fx' R' M' mdl' (f : word) (flag : Z),
        FXOK fx' -> regs_kept R R' -> getr R' (Z_to_bv 5 10) = f ->
        u f mod n = 0 -> ablk_ok G (u f) n ->
        (forall b m, In (b, m) (Lc ++ Lf) -> u f + n <= b \/ b + m <= u f) ->
        (forall z, in_wins PERMc z -> ~ (u f <= z < u f + n)) ->                     (* [comment removed for export] *)
        (forall a : word, u f <= u a < u f + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        em64 M' (u f + n - 8) flag ->
        (forall i, 0 <= i < n / 8 -> M' (Z_to_bv 64 (SB + u f / 8 + i)) = Some (Z_to_bv 8 0)) ->
        (forall a : word, in_shadow SB (u f) n (u a) -> RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        (forall a : word, nkept Lc Lf (scratch sp MSTK_F) a -> M' a = M a) -> errno_kept M M' ->
        scratch_ok M' sp MSTK_F ->
        AINV Lc ((u f, n) :: Lf) B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R (g_stkmal G k) M mdl) T.

(* [comment removed for export] *)
Definition fakerel_nspec : Prop :=
  forall (p rs : Z) fx R M mdl Lc Lf F1 F2 B C K (f n flag : Z) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    Lf = F1 ++ (f, n) :: F2 ->
    em64 M (f + n - 8) flag ->
    fetch_word SEGS (Z_to_bv 64 p) = Some (Z_to_bv 32 (0x23 + rs * 2 ^ 15)) ->
    1 <= rs <= 31 -> u (getr R (Z_to_bv 5 rs)) = flag -> 0 <= p -> p + 4 < 2 ^ 64 ->
    (forall M' mdl',
        (forall a : word, nkept Lc (F1 ++ F2) noscratch a -> M' a = M a) -> errno_kept M M' ->
        AINV Lc (F1 ++ F2) B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx R (p + 4) M' mdl') T) ->
    RZ (cfg fx R p M mdl) T.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nmem (a : Z) : Prop := (0 <= a <= SB - 1) \/ (KHI <= a < two47).
(* [comment removed for export] *)
Definition nacc (M : word -> option byte) (b n : Z) : Prop :=
  forall z, b <= z < b + n -> exists bt, M (Z_to_bv 64 (SB + z / 8)) = Some bt /\ (u bt = 0 \/ z mod 8 < u bt <= 7).
(* [comment removed for export] *)
Definition nshvis (Lc Lf : list (Z * Z)) (b n : Z) : Prop :=
  forall z, b <= z < b + n ->
    in_blocks (Lc ++ map fusable Lf) z \/ in_wins PERMc z \/ (CEIL_run <= z < two47) \/ (g_ro_lo G <= z < g_img_hi G).
(* [comment removed for export] *)
Definition ndst (Lc Lf : list (Z * Z)) (a : word) : Prop := owned SWIN PERMc SPTOPc (Lc ++ map fusable Lf) a.

(* [comment removed for export] *)
Definition ndst_pre (M : word -> option byte) (Lc Lf : list (Z * Z)) (dst n : Z) : Prop :=
  0 <= n <= 2 ^ 40 /\ nmem dst /\ nmem (dst + n) /\ nacc M dst n /\ nshvis Lc Lf dst n
  /\ (forall a : word, dst <= u a < dst + n -> ndst Lc Lf a /\ RiscvSemantics.store_ok SEGS M a 1 = true).
(* [comment removed for export] *)
Definition nsrc_pre (M : word -> option byte) (Lc Lf : list (Z * Z)) (src n : Z) (bs : list byte) : Prop :=
  nmem src /\ nmem (src + n) /\ nacc M src n /\ nshvis Lc Lf src n
  /\ rdn SEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
(* [comment removed for export] *)
Definition nmem_post (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (Lc Lf : list (Z * Z)) (B C K : Z)
           (ret sp dst n : Z) (bytes : nat -> option byte) (T : TSet) : Prop :=
  forall fx' R' M' mdl',
    FXOK fx' -> regs_kept R R' -> u (getr R' (Z_to_bv 5 10)) = dst ->
    (forall i, (i < Z.to_nat n)%nat -> M' (Z_to_bv 64 (dst + Z.of_nat i)) = bytes i) ->
    (forall a : word, M' a <> M a -> (dst <= u a < dst + n) \/ scratch sp MSTK_M a) ->
    scratch_ok M' sp MSTK_M ->
    AINV Lc Lf B C K M' mdl' ->
    nmodel mdl mdl' ->
    RZ (cfg fx' R' ret M' mdl') T.

(* [comment removed for export] *)
Definition copy_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp dst src n : Z) (bs : list byte) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) = src -> u (getr R (Z_to_bv 5 12)) = n ->
    (dst + n <= src \/ src + n <= dst) ->                        (* [comment removed for export] *)
    ndst_pre M Lc Lf dst n -> nsrc_pre M Lc Lf src n bs ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) -> (forall a : word, src <= u a < src + n -> ~ scratch sp MSTK_M a) ->   (* [comment removed for export] *)
    nmem_post R M mdl Lc Lf B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition move_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp dst src n : Z) (bs : list byte) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) = src -> u (getr R (Z_to_bv 5 12)) = n ->
    (dst <> src \/ (forall i, 0 <= i < n -> M (Z_to_bv 64 (src + i)) <> None)) ->
    ndst_pre M Lc Lf dst n -> nsrc_pre M Lc Lf src n bs ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) -> (forall a : word, src <= u a < src + n -> ~ scratch sp MSTK_M a) ->   (* [comment removed for export] *)
    nmem_post R M mdl Lc Lf B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition fill_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp dst c n : Z) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) mod 256 = c -> u (getr R (Z_to_bv 5 12)) = n ->
    ndst_pre M Lc Lf dst n ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) ->   (* [comment removed for export] *)
    nmem_post R M mdl Lc Lf B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c)) T ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition nstr_pre (M : word -> option byte) (Lc Lf : list (Z * Z)) (s len : Z) : Prop :=
  0 <= len /\ len + 1 <= 2 ^ 40 /\ nmem s /\ nmem (s + len + 1) /\ nacc M s (len + 1) /\ nshvis Lc Lf s (len + 1)
  /\ (forall i, 0 <= i < len -> exists b, rdn SEGS M (Z_to_bv 64 (s + i)) 1 = Some [b] /\ b <> Z_to_bv 8 0)
  /\ rdn SEGS M (Z_to_bv 64 (s + len)) 1 = Some [Z_to_bv 8 0]
  /\ (forall i, s - s mod 8 <= i < (s + len + 8) - (s + len) mod 8 -> rdn SEGS M (Z_to_bv 64 i) 1 <> None).
Definition nstr_post (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (Lc Lf : list (Z * Z)) (B C K : Z)
           (ret sp len : Z) (T : TSet) : Prop :=
  forall fx' R' M' mdl',
    FXOK fx' -> regs_kept R R' -> u (getr R' (Z_to_bv 5 10)) = len ->
    (forall a : word, M' a <> M a -> scratch sp MSTK_M a) ->
    scratch_ok M' sp MSTK_M ->
    AINV Lc Lf B C K M' mdl' ->
    nmodel mdl mdl' ->
    RZ (cfg fx' R' ret M' mdl') T.
Definition strlen_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret sp s len : Z) T,
    m_halted mdl = None -> FXOK fx ->
    AINV Lc Lf B C K M mdl ->
    ncall_pre R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = s ->
    nstr_pre M Lc Lf s len ->
    (forall a : word, s <= u a < s + len + 1 -> ~ scratch sp MSTK_M a) ->
    nstr_post R M mdl Lc Lf B C K ret sp len T ->
    RZ (cfg fx R entry M mdl) T.

End NSpec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HContracts.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Variable AINVHN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hchanged (stk : Z) (L LF : list (Z * Z)) (sp : Z) (a : word) : Prop :=
  scratch sp stk a
  \/ (u a < CEIL_run /\ ~ (g_img_lo G <= u a < g_img_hi G) /\ ~ nvisible G L LF (u a))
  \/ in_wins (g_privx G) (u a).

(* [comment removed for export] *)
Definition hcall_pre (R : bvmap 5 word) (M : word -> option byte) (ret sp stk : Z) : Prop :=
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0
  /\ u (getr R (Z_to_bv 5 2)) = sp /\ sp mod 16 = 0 /\ CEIL_run + stk <= sp /\ sp + 16 <= two47   (* [comment removed for export] *)
  /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)
  /\ (forall a : word, scratch sp stk a -> RiscvSemantics.store_ok SEGS M a 1 = true).

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
Definition hmalloc_pre (fpcreq : bool) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (L LF : list (Z * Z)) (B C K ret n sp stk : Z) : Prop :=
  FXOK fx /\ m_halted mdl = None /\ AINVH L LF B C K M mdl /\ hcall_pre R M ret sp stk
  /\ u (getr R (Z_to_bv 5 10)) = n /\ 1 <= n <= NMAX
  /\ (fpcreq = true -> FPC M (u (getr R (Z_to_bv 5 8))) sp)
  /\ B + mcost n <= GBUDGET /\ C + MCNT <= GCOUNT /\ K + kcost n <= GKCAP.
Definition hmalloc_post_ok (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (L LF : list (Z * Z)) (B C K n sp stk : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) (p : word) : Prop :=
  FXOK fx' /\ regs_kept R R' /\ getr R' (Z_to_bv 5 10) = p
  /\ u p mod 16 = 0 /\ ablk_ok G (u p) n
  /\ (64512 < n -> u p mod 4096 = 2048)                                          (* [comment removed for export] *)
  /\ (forall b m, In (b, m) (L ++ LF) -> u p + n <= b \/ b + m <= u p)
  /\ (forall a : word, u p <= u a < u p + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true)
  /\ (forall z, u p <= z < u p + n -> exists b : byte, M' (Z_to_bv 64 (SB + z / 8)) = Some b /\ (u b = 0 \/ z mod 8 < u b <= 7))   (* [comment removed for export] *)
  /\ (forall a : word, in_shadow SB (u p) n (u a) -> RiscvSemantics.store_ok SEGS M' a 1 = true)
  /\ (forall a : word, M' a <> M a -> hchanged stk L LF sp a) /\ errno_kept G M M'
  /\ scratch_ok SEGS M' sp stk
  /\ AINVH ((u p, n) :: L) LF (B + mcost n) (C + MCNT) (K + kcost n) M' mdl'
  /\ nmodel mdl mdl'.
Definition hmalloc_post_null (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (L LF : list (Z * Z)) (B C K n sp stk : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) : Prop :=
  FXOK fx' /\ regs_kept R R' /\ getr R' (Z_to_bv 5 10) = Z_to_bv 64 0
  /\ (forall a : word, M' a <> M a -> hchanged stk L LF sp a) /\ errno_kept G M M'
  /\ scratch_ok SEGS M' sp stk
  /\ AINVHN n L LF B C K M' mdl'      (* [comment removed for export] *)
  /\ nmodel mdl mdl'.


(* [comment removed for export] *)
Definition h_malloc1_at (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
           (stk entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret n sp : Z) Tok,
    hmalloc_pre true fx R M mdl L LF B C K ret n sp stk -> FRESH L LF B C K M mdl n -> Tok [] ->
    (forall fx' R' M' mdl' (p : word), hmalloc_post_ok R M mdl L LF B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') Tok) ->
    RZ (cfg fx R entry M mdl) Tok.

Definition h_malloc_at (stk entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret n sp : Z) T,
    hmalloc_pre true fx R M mdl L LF B C K ret n sp stk -> T [] ->
    (forall fx' R' M' mdl' (p : word), hmalloc_post_ok R M mdl L LF B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    (forall fx' R' M' mdl', hmalloc_post_null R M mdl L LF B C K n sp stk fx' R' M' mdl' -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition h_alloc1_at (XTRA : (word -> option byte) -> Prop) (stk entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret n sp : Z) T,
    hmalloc_pre false fx R M mdl L LF B C K ret n sp stk -> XTRA M -> m_fds mdl = APS.fds_std -> Z.of_nat (length LF) + 1 <= FMIN -> T [] ->
    (forall fx' R' M' mdl' (p : word), hmalloc_post_ok R M mdl L LF B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.
(* [comment removed for export] *)
Definition hopnew_x (M : word -> option byte) : Prop :=
  forall E, Forall (fun K => AX2S.kentry_ok SEGS E M K) (g_opnew_kn G).

Definition h_free_at (stk entry : Z) : Prop :=
  forall fx R M mdl L L' LF B C K B' C' K' (ret sp : Z) (p : word) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre R M ret sp stk ->
    getr R (Z_to_bv 5 10) = p ->
    FPC M (u (getr R (Z_to_bv 5 8))) sp ->
    ((p = Z_to_bv 64 0 /\ L' = L /\ B' = B /\ C' = C /\ K' = K)
     \/ exists m L1 L2, L = L1 ++ (u p, m) :: L2 /\ L' = L1 ++ L2
                         /\ B' = Z.max 0 (B - mcost m) /\ C' = Z.max 0 (C - MCNT) /\ K' = K + KFREE /\ K' <= GKCAP) ->
    (forall fx' R' M' mdl',
        FXOK fx' -> regs_kept R R' ->
        (forall a : word, M' a <> M a -> hchanged stk L' LF sp a) -> errno_kept G M M' ->
        scratch_ok SEGS M' sp stk ->
        AINVH L' LF B' C' K' M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Fixpoint hfcount (n : Z) (LF : list (Z * Z)) : Z :=
  match LF with [] => 0 | f :: r => (if Z.eqb (snd f) n then 1 else 0) + hfcount n r end.

Definition h_stkmal (k : Z) : Prop :=
  let n := 64 * 2 ^ k in
  forall fx R M mdl L LF B C K (ret sp : Z) T,
    0 <= k <= 3 ->
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre R M ret sp MSTK_F ->
    hfcount n LF + 1 <= FMIN ->
    (forall fx' R' M' mdl' (f : word) (flag : Z),
        FXOK fx' -> regs_kept R R' -> getr R' (Z_to_bv 5 10) = f ->
        u f mod n = 0 -> ablk_ok G (u f) n ->
        (forall b m, In (b, m) (L ++ LF) -> u f + n <= b \/ b + m <= u f) ->
        (forall a : word, u f <= u a < u f + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        em64 M' (u f + n - 8) flag ->
        (forall i, 0 <= i < n / 8 -> M' (Z_to_bv 64 (SB + u f / 8 + i)) = Some (Z_to_bv 8 0)) ->
        (forall a : word, in_shadow SB (u f) n (u a) -> RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        (forall a : word, M' a <> M a -> hchanged MSTK_F L LF sp a) -> errno_kept G M M' ->
        scratch_ok SEGS M' sp MSTK_F ->
        AINVH L ((u f, n) :: LF) B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R (g_stkmal G k) M mdl) T.

Definition h_fakerel : Prop :=
  forall (p rs : Z) fx R M mdl L LF F1 F2 B C K (f n flag : Z) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    LF = F1 ++ (f, n) :: F2 ->
    em64 M (f + n - 8) flag ->
    fetch_word SEGS (Z_to_bv 64 p) = Some (Z_to_bv 32 (0x23 + rs * 2 ^ 15)) ->
    1 <= rs <= 31 -> u (getr R (Z_to_bv 5 rs)) = flag -> 0 <= p -> p + 4 < 2 ^ 64 ->     (* [comment removed for export] *)
    (forall M' mdl',
        (forall a : word, M' a <> M a -> u a = flag /\ flag < CEIL_run /\ ~ (g_img_lo G <= flag < g_img_hi G) /\ ~ nvisible G L (F1 ++ F2) flag) ->
        AINVH L (F1 ++ F2) B C K M' mdl' ->
        nmodel mdl mdl' ->
        RZ (cfg fx R (p + 4) M' mdl') T) ->
    RZ (cfg fx R p M mdl) T.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable FRESHA : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.

Record hcontracts : Prop := HC {
  hc_malloc1 : h_malloc1_at FRESHA MSTK_A (g_malloc G);            (* [comment removed for export] *)
  hc_malloc1_thunk : h_malloc1_at FRESHA MSTK_A (g_malloc_thunk G);
  hc_malloc : h_malloc_at MSTK_A (g_malloc G);                     (* [comment removed for export] *)
  hc_malloc_thunk : h_malloc_at MSTK_A (g_malloc_thunk G);
  hc_opnew : h_alloc1_at hopnew_x MSTK_N (g_opnew G);           (* [comment removed for export] *)
  hc_free : h_free_at MSTK_A (g_free G);
  hc_free_thunk : h_free_at MSTK_A (g_free_thunk G);
  hc_opdel : h_free_at MSTK_A (g_opdel G);
  hc_opdel_sized : h_free_at MSTK_A (g_opdel_sized G);
  hc_stkmal : forall k, 0 <= k <= 3 -> h_stkmal k;
  hc_fakerel : h_fakerel;
  (* [comment removed for export] *)
  hc_fpc_stop : forall M v lo, v <= lo -> FPC M v lo;
  hc_fpc_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo
}.
(* [comment removed for export] *)
Record hcontracts_core : Prop := HCC {
  hcc_malloc1 : h_malloc1_at FRESHA MSTK_A (g_malloc G);          (* [comment removed for export] *)
  hcc_malloc1_thunk : h_malloc1_at FRESHA MSTK_A (g_malloc_thunk G);
  hcc_malloc : h_malloc_at MSTK_A (g_malloc G);
  hcc_malloc_thunk : h_malloc_at MSTK_A (g_malloc_thunk G);
  hcc_free : h_free_at MSTK_A (g_free G);
  hcc_free_thunk : h_free_at MSTK_A (g_free_thunk G);
  hcc_opdel : h_free_at MSTK_A (g_opdel G);
  hcc_opdel_sized : h_free_at MSTK_A (g_opdel_sized G);
  hcc_stkmal : forall k, 0 <= k <= 3 -> h_stkmal k;
  hcc_fakerel : h_fakerel;
  hcc_fpc_stop : forall M v lo, v <= lo -> FPC M v lo;
  hcc_fpc_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo
}.


End HContracts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section LContracts.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.

(* [comment removed for export] *)
Definition hdst (L LF : list (Z * Z)) (a : word) : Prop :=
  in_blocks L (u a) \/ in_blocks (map fusable LF) (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a).
Definition hshvis (L LF : list (Z * Z)) (b n : Z) : Prop :=
  forall z, b <= z < b + n -> in_blocks (L ++ map fusable LF) z \/ (CEIL_run <= z < two47) \/ (g_ro_lo G <= z < g_img_hi G).
Definition hdst_pre (M : word -> option byte) (L LF : list (Z * Z)) (dst n : Z) : Prop :=
  0 <= n <= 2 ^ 40 /\ nmem dst /\ nmem (dst + n) /\ nacc M dst n /\ hshvis L LF dst n
  /\ (forall a : word, dst <= u a < dst + n -> hdst L LF a /\ RiscvSemantics.store_ok SEGS M a 1 = true).
Definition hsrc_pre (M : word -> option byte) (L LF : list (Z * Z)) (src n : Z) (bs : list byte) : Prop :=
  nmem src /\ nmem (src + n) /\ nacc M src n /\ hshvis L LF src n
  /\ rdn SEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs.

#[local] Notation cfg := (fun fx R p M mdl => mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

Definition hmem_post (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (L LF : list (Z * Z)) (B C K : Z)
           (ret sp dst n : Z) (bytes : nat -> option byte) (T : TSet) : Prop :=
  forall fx' R' M' mdl',
    FXOK fx' -> regs_kept R R' -> u (getr R' (Z_to_bv 5 10)) = dst ->
    (forall i, (i < Z.to_nat n)%nat -> M' (Z_to_bv 64 (dst + Z.of_nat i)) = bytes i) ->
    (forall a : word, M' a <> M a -> (dst <= u a < dst + n) \/ scratch sp MSTK_M a) ->
    scratch_ok SEGS M' sp MSTK_M ->
    AINVH L LF B C K M' mdl' ->
    nmodel mdl mdl' ->
    RZ (cfg fx' R' ret M' mdl') T.

Definition h_copy_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp dst src n : Z) (bs : list byte) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) = src -> u (getr R (Z_to_bv 5 12)) = n ->
    (dst + n <= src \/ src + n <= dst) ->                        (* [comment removed for export] *)
    hdst_pre M L LF dst n -> hsrc_pre M L LF src n bs ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) -> (forall a : word, src <= u a < src + n -> ~ scratch sp MSTK_M a) ->
    hmem_post R M mdl L LF B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T ->
    RZ (cfg fx R entry M mdl) T.

Definition h_move_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp dst src n : Z) (bs : list byte) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) = src -> u (getr R (Z_to_bv 5 12)) = n ->
    (dst <> src \/ (forall i, 0 <= i < n -> M (Z_to_bv 64 (src + i)) <> None)) ->                  (* [comment removed for export] *)
    hdst_pre M L LF dst n -> hsrc_pre M L LF src n bs ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) -> (forall a : word, src <= u a < src + n -> ~ scratch sp MSTK_M a) ->
    hmem_post R M mdl L LF B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T ->
    RZ (cfg fx R entry M mdl) T.

Definition h_fill_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp dst c n : Z) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = dst -> u (getr R (Z_to_bv 5 11)) mod 256 = c -> u (getr R (Z_to_bv 5 12)) = n ->
    hdst_pre M L LF dst n ->
    (forall a : word, dst <= u a < dst + n -> ~ scratch sp MSTK_M a) ->
    hmem_post R M mdl L LF B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c)) T ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Definition hstr_pre (M : word -> option byte) (L LF : list (Z * Z)) (s len : Z) : Prop :=
  0 <= len /\ len + 1 <= 2 ^ 40 /\ nmem s /\ nmem (s + len + 1) /\ nacc M s (len + 1) /\ hshvis L LF s (len + 1)
  /\ (forall i, 0 <= i < len -> exists b, rdn SEGS M (Z_to_bv 64 (s + i)) 1 = Some [b] /\ b <> Z_to_bv 8 0)
  /\ rdn SEGS M (Z_to_bv 64 (s + len)) 1 = Some [Z_to_bv 8 0]
  /\ (forall i, s - s mod 8 <= i < (s + len + 8) - (s + len) mod 8 -> rdn SEGS M (Z_to_bv 64 i) 1 <> None).
Definition hstr_post (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) (L LF : list (Z * Z)) (B C K : Z)
           (ret sp len : Z) (T : TSet) : Prop :=
  forall fx' R' M' mdl',
    FXOK fx' -> regs_kept R R' -> u (getr R' (Z_to_bv 5 10)) = len ->
    (forall a : word, M' a <> M a -> scratch sp MSTK_M a) ->
    scratch_ok SEGS M' sp MSTK_M ->
    AINVH L LF B C K M' mdl' ->
    nmodel mdl mdl' ->
    RZ (cfg fx' R' ret M' mdl') T.
Definition h_strlen_at (entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret sp s len : Z) T,
    FXOK fx -> m_halted mdl = None ->
    AINVH L LF B C K M mdl ->
    hcall_pre SEGS G R M ret sp MSTK_M ->
    u (getr R (Z_to_bv 5 10)) = s ->
    hstr_pre M L LF s len ->
    (forall a : word, s <= u a < s + len + 1 -> ~ scratch sp MSTK_M a) ->
    hstr_post R M mdl L LF B C K ret sp len T ->
    RZ (cfg fx R entry M mdl) T.

(* [comment removed for export] *)
Record lcontracts : Prop := LC {
  lc_memcpy : h_copy_at (g_memcpy G);
  lc_amemcpy : h_copy_at (g_amemcpy G);
  lc_memset : h_fill_at (g_memset G);
  lc_amemset : h_fill_at (g_amemset G);
  lc_memmove : h_move_at (g_memmove G);
  lc_amemmove : h_move_at (g_amemmove G);
  lc_strlen : h_strlen_at (g_strlen G)
}.
End LContracts.

