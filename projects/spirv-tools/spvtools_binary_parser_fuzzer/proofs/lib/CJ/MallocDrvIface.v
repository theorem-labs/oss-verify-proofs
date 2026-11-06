(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Malloc MallocCtrl Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MTight.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocRep RImage RMalloc_iface RBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim ShapeAlg SRealizes ShapeUpto RefMemcpyLib LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt MallocInstS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition dcell (M : LibIface.mem) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition dclear (M : LibIface.mem) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

Record mng_main_mem (M : LibIface.mem) : Prop := MNG_MAIN_MEM {
  mm_ctx    : dclear M RMLOCK (RCTX + 928);
  mm_vmlock : dclear M RVMLOCK (RVMLOCK + 4);
  mm_libc0  : dcell M RLIBC 1 1;
  mm_libc1  : dcell M (RLIBC + 1) 1 0;
  mm_libc2  : dcell M (RLIBC + 2) 1 0;
  mm_libc3  : dcell M (RLIBC + 3) 1 0;
  mm_libc4  : dcell M (RLIBC + 4) 4 0;
  mm_auxv   : exists auxv, 0 <= auxv < 2 ^ 64 /\ dcell M (RLIBC + 8) 8 auxv;
  mm_tlshd  : dcell M (RLIBC + 16) 8 0;
  mm_tlssz  : dcell M (RLIBC + 24) 8 224;
  mm_tlsal  : dcell M (RLIBC + 32) 8 8;
  mm_tlscnt : dcell M (RLIBC + 40) 8 0;
  mm_pgsz   : dcell M (RLIBC + 48) 8 4096;
  mm_gloc   : forall i, 0 <= i < 48 -> exists b, rdn SEGS M (Z_to_bv 64 (RLIBC + 56 + i)) 1 = Some [b] /\ b = Z_to_bv 8 0;

  mm_guard  : dcell M RSSP_GUARD 8 rr_canary;
  mm_ro     : img_ro_clear L M
}.

Record mng_main_model (mo : Model) : Prop := MNG_MAIN_MODEL {
  mo_maps  : vm_maps (m_vmmaps mo) = [];
  mo_noacc : vm_noaccess (m_vmmaps mo) = [];
  mo_resv  : vm_reserved (m_vmmaps mo) = segments_reserved SEGS;
  mo_brk   : vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo);
  mo_sb    : valid_brk SEGS (vm_start_brk (m_vmmaps mo));
  mo_sbhi  : bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * 4096 <= alloc_ceiling;
  mo_lim   : 2 ^ 34 <= vm_limit (m_vmmaps mo);
  mo_lazy  : m_vm_lazy mo = [];
  mo_mat   : m_vm_materialized mo = []
}.

Definition a_inv0 (A : mstateA) (M : LibIface.mem) (mo : Model) : Prop :=
  a_invX A M mo /\ a_LB A = [] /\ a_P A = lib_caps /\ a_big A = LIB_BIGCAP.

Definition auxv_words (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list Z :=
  [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].
Definition mng_auxv (M : LibIface.mem) (sp : Z) : Prop :=
  exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
    dcell M (RLIBC + 8) 8 av
    /\ (forall i, (i < 20)%nat -> dcell M (av + 8 * Z.of_nat i) 8 (nth i (auxv_words x3 x4 x5 x16 x6 x11 x12 x23 rnd) 0))
    /\ dcell M (rnd + 8) 8 rr_secret
    /\ alloc_ceiling <= sp /\ sp <= av /\ av + 160 <= 2 ^ 64 /\ sp <= rnd + 8 /\ rnd + 16 <= 2 ^ 64
    /\ Forall (fun x => 0 <= x < 2 ^ 64) [x3; x4; x5; x16; x6; x11; x12; x23; rnd].

Definition a_tight (A : mstateA) : Prop := TIGHT (ps_m (a_s A)).

Definition a_fresh44 (A : mstateA) : Prop :=
  active (ps_m (a_s A)) 44 = None /\ usage (ps_m (a_s A)) 44 = 0 /\ bounces (ps_m (a_s A)) 44 = 0.

Definition owned_img_ok (A : mstateA) : Prop :=
  forall a, a_owned A a -> in_ranges (ly_img L) a -> mng_static a.

Definition ainv_init_stmt : Prop :=
  forall (M : LibIface.mem) (mo : Model),
    mng_main_mem M -> mng_main_model mo ->
    exists A : mstateA,
      a_inv0 A M mo /\ a_live A = [] /\ a_P A = lib_caps /\ a_big A = LIB_BIGCAP
      /\ owned_img_ok A /\ a_tight A /\ a_fresh44 A.

Definition a_inv0_frame_stmt : Prop :=
  forall A M M' mo mo', a_inv0 A M mo ->
    (forall a : word, a_owned A (bv_unsigned a) -> M' a = M a) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> a_inv0 A M' mo'.

Definition ainv0_owned_stmt : Prop :=
  forall A M mo a, a_inv0 A M mo -> a_owned A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling.

Section Stmts.
#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

Definition mi_free_T_stmt : Prop :=
  forall (fx : FPState) (A : mstateA) R M mo (p n sp ret : Z) (K : TSet),
    a_inv A M mo -> a_tight A -> mstd mo -> img_ro_clear L M ->
    call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
    (p = 0 /\ n = 0 \/ In (p, n) (a_live A)) ->
    alloc_ceiling + MNG_MALLOC_STACK <= sp ->
    stack_room SEGS M sp MNG_MALLOC_STACK ->
    (forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a) ->
    (forall A' R' M' mo', a_inv A' M' mo' -> a_tight A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
        kept R R' -> live_del p (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
        (forall a, a_owned A' a -> a_owned A a \/ (p <= a < p + n)) ->
        frame_eq (fun a => a_owned A a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win L (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' mo') K) ->
    srealizes SEGS (cfg fx R (ly_free L) M mo) K.

Definition mi_malloc_T_stmt : Prop :=
  forall (fx : FPState) (A : mstateA) R M mo (n sp ret : Z) (Ksucc : TSet),
    a_inv A M mo -> a_tight A -> (MNG_BIG <= n \/ (n = 65536 /\ a_fresh44 A)) ->
    mstd mo -> img_ro_clear L M ->
    call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 n -> 0 <= n <= MNG_NMAX ->
    alloc_ceiling + MNG_MALLOC_STACK <= sp ->
    stack_room SEGS M sp MNG_MALLOC_STACK ->
    (forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a) ->
    a_room A n ->
    (forall A' R' M' mo' (p : Z),
        a_inv A' M' mo' -> a_tight A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
        live_add p n (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
        (forall a, a_owned A' a -> a_owned A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
        frame_eq (fun a => a_owned A' a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' mo') Ksucc) ->
    srealizes SEGS (cfg fx R (ly_malloc L) M mo) Ksucc.

Definition mi_malloc_first_stmt : Prop :=
  forall (fx : FPState) (A : mstateA) R M mo (n sp ret : Z) (Ksucc : TSet),
    a_inv0 A M mo -> mng_auxv M sp -> a_tight A -> n = 65536 -> a_fresh44 A ->
    a_live A = [] ->
    mstd mo -> img_ro_clear L M ->
    call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 n ->
    alloc_ceiling + MNG_MALLOC_STACK <= sp ->
    stack_room SEGS M sp MNG_MALLOC_STACK ->
    (forall a, zwin (sp - MNG_MALLOC_STACK) sp a -> ~ a_owned A a) ->
    (forall A' R' M' mo' (p : Z),
        a_inv A' M' mo' -> a_tight A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
        live_add p n (a_live A) (a_live A') -> a_P A' = a_P A -> a_big A' = a_big A ->
        (forall a, a_owned A' a -> a_owned A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
        frame_eq (fun a => a_owned A' a \/ (p <= a < p + n) \/ zwin (sp - MNG_MALLOC_STACK) sp a \/ errno_win L a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ a_owned A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' mo') Ksucc) ->
    srealizes SEGS (cfg fx R (ly_malloc L) M mo) Ksucc.

End Stmts.

End AC_1.
