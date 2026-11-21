(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Frame Cells Mem Step Tac Image ZBridge SysStep Walk Arr ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import PState. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS8 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RunHit.  (* a worker (A1) miss kit *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesS8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require Import S8HBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RULES.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.
Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop).

(* [comment removed for export] *)
Definition call_pre (R : bvmap 5 word) (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (X : list bptr)
    (G : PState -> Model -> Prop) (lo B stackneed : Z) (errv : word) : Prop :=
  RHEAP s LB M /\ OWN X G s mo /\ frame_ok G /\ rauxv_ok M B
  /\ bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B
  /\ stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) /\ ATOP <= lo
  /\ lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - stackneed
  /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv]
  /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M
  /\ reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP.

Lemma call_pre_intro : forall R M mo s LB X G lo B stackneed errv,
  RHEAP s LB M -> OWN X G s mo -> frame_ok G -> rauxv_ok M B ->
  bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) -> ATOP <= lo ->
  lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - stackneed ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M -> reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  call_pre R M mo s LB X G lo B stackneed errv.
Proof. intros. unfold call_pre. tauto. Qed.

(* [comment removed for export] *)
Definition rule_malloc_grow : Prop :=
  forall (j : nat) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (X : list bptr)
         (G : PState -> Model -> Prop) (n lo B : Z) (errv : word) (A Bs : ShapeAlg.TSet),
    call_pre R M mo s LB X G lo B RMALLOC_STACK errv ->
    reg_get R (Z_to_bv 5 10) = Z_to_bv 64 n -> 131072 <= n < 2 ^ 27 ->
    AI (S j) X s mo ->
    A [] -> Bs [] ->
    (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' ->
       (match r with None => True | Some q => AIm j (q :: X) s' mo' end) ->
       realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
                (match r with None => A | Some _ => Bs end)) ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.

(* [comment removed for export] *)
Definition rule_free_grow : Prop :=
  forall (j : nat) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (X : list bptr)
         (G : PState -> Model -> Prop) (p : bptr) (A n lo B : Z) (errv : word) (T : ShapeAlg.TSet),
    call_pre R M mo s LB (p :: X) G lo B RFREE_STACK errv -> In (p, A, n) LB ->
    reg_get R (Z_to_bv 5 10) = Z_to_bv 64 A ->
    AIm j (p :: X) s mo ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (mo' : Model) (s' : PState),
        (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
        mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) ->
        rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] -> rauxv_ok M' B ->
        rheap_pres (lb_remove p LB) (bv_unsigned (reg_get R (Z_to_bv 5 2))) M M' ->
        RHEAP s' (lb_remove p LB) M' -> OWN X G s' mo' -> AI j X s' mo' ->
        realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R (Z_to_bv 64 RFREE_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.

(* [comment removed for export] *)
Definition rule_malloc_first (j0 : nat) : Prop :=
  forall (R : bvmap 5 word) (M : word -> option byte) (mo : Model) (G : PState -> Model -> Prop) (lo B : Z) (errv : word)
         (brk0 : word) (lim : Z) (A Bs : ShapeAlg.TSet),
    (* a worker (A1) route (A): the launch triple is the RunCtx's own (rc_mb rc_sp rc_inp), so the call_pre and
       the run below are one run *)
    let s := ps_init (reservedZ psegs ++ RunHit.vdso_resvZ rc_inp rc_sp rc_mb) ATOP in  (* a worker (B1) *)
    call_pre R M mo s [] [] G lo B RMALLOC_STACK errv ->
    reg_get R (Z_to_bv 5 10) = Z_to_bv 64 65536 ->
    (* a worker port727 (), a worker's form: the launch's VmMaps is init_model's (its reserved list is the
       image's segments ++ the vDSO pair), and the kernel build is the launch's. *)
    m_vmmaps mo = m_vmmaps (init_model (segments_reserved psegs) brk0 rc_mb rc_sp lim rc_inp) -> m_kernel mo = in_kernel rc_inp ->
    2 ^ 34 <= lim ->
    A [] -> Bs [] ->
    (forall R' M' mo' s' r, malloc_ret R R' M M' s s' [] 65536 lo B r -> own_ret [] G r s' mo' ->
       (match r with None => True | Some q => AI j0 [q] s' mo' end) ->
       realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
                (match r with None => A | Some _ => Bs end)) ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.

End RULES.
