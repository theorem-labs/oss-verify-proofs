(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA.
Import ListNotations.
Open Scope Z_scope.

Definition httpmsg_compare_entryA : Z := 0x86914.
Definition ListHead_entryA : Z := 0x8c068.
Definition ListNext_entryA : Z := 0x8c0e8.
Definition FreeListInit_entryA : Z := 0x8c2ac.
Definition ListInit_entryA : Z := 0x8ba78.
Definition memptr_cmp_entryA : Z := 0x8c72c.
Definition memptr_cmp_nocase_entryA : Z := 0x8c7f4.
Definition str_alloc_entryA : Z := 0x8c690.
Definition membuffer_destroy_entryA : Z := 0x8c964.
Definition membuffer_assign_entryA : Z := 0x8ca3c.
Definition membuffer_append_entryA : Z := 0x8cd1c.
Definition membuffer_insert_entryA : Z := 0x8cd6c.
Definition membuffer_append_str_entryA : Z := 0x8d078.
Definition membuffer_delete_entryA : Z := 0x8d0fc.

Section Stmts.
  Context {HC : HasCeiling}.

  Definition httpmsg_compare_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (ia ib lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (ia =? ib)%Z then 1 else 0)) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q) /\ asan_env asegs m'.

  Definition httpmsg_compare_stmt_A : Prop :=
    forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B ia ib lo : Z) (ja : list byte) (n1 n2 pad : word),

    rw_cells asegs m A [CB 16%nat ja; C4 (wz ia)] -> rw_cells asegs m B [C8 n1; C8 n2; C4 (wz ib); C4 pad] ->
    - 2^31 <= ia < 2^31 -> - 2^31 <= ib < 2^31 ->

    asan_env asegs m ->
    rw_cells asegs m (sh (A + 16)) (shadow_zero_cells 1) -> rw_cells asegs m (sh (B + 16)) (shadow_zero_cells 1) ->
    0x609000 <= A -> A + 20 <= alloc_ceiling -> app_mem A 20 -> A mod 8 = 0 ->
    0x609000 <= B -> B + 24 <= alloc_ceiling -> app_mem B 24 -> B mod 8 = 0 ->
    stk asegs m lo (q) -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
    mem_inv asegs m -> a0 = wz A -> a1 = wz B ->
    evt asegs (httpmsg_compare_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ia ib lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz httpmsg_compare_entryA) fc None m (seg_rom asegs)).

  Definition ListHead_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (first size lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (size =? 0)%Z then 0 else first)) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q) /\ asan_env asegs m'.

  Definition ListHead_stmt_A : Prop :=
    forall (L first last size flh fk ffree fcmp lo : Z),
    forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m L (llist_cells first last size flh fk ffree fcmp) ->
    L <> 0%Z -> (0 <= size < 2^63)%Z -> (0 <= first < 2^64)%Z ->
    asan_env asegs m -> rw_cells asegs m (sh L) (shadow_zero_cells 12) ->
    0x609000 <= L -> L + 96 <= alloc_ceiling -> app_mem L 96 -> L mod 8 = 0 ->
    stk asegs m lo (q) -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
    mem_inv asegs m -> a0 = wz L ->
    evt asegs (ListHead_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc first size lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ListHead_entryA) fc None m (seg_rom asegs)).

  Definition ListNext_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L nx lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (nx =? L + 24)%Z then 0 else nx)) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q) /\ asan_env asegs m'.

  Definition ListNext_stmt_A : Prop :=
    forall (L N pv nx it lo : Z),
    forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m N (node_cells pv nx it) ->
    L <> 0%Z -> N <> 0%Z -> (0 <= nx < 2^64)%Z -> (0 < L /\ L + 96 < 2^64)%Z ->
    asan_env asegs m -> rw_cells asegs m (sh N) (shadow_zero_cells 3) ->
    0x609000 <= N -> N + 24 <= alloc_ceiling -> app_mem N 24 -> N mod 8 = 0 -> L mod 8 = 0 ->
    stk asegs m lo (q) -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
    mem_inv asegs m -> a0 = wz L -> a1 = wz N ->
    evt asegs (ListNext_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L nx lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ListNext_entryA) fc None m (seg_rom asegs)).

  Definition FreeListInit_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (FL esz mx lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(FL, FL + 24)%Z; (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' FL [C8 (wz 0); C8 (wz esz); C4 (wz mx); C4 (wz 0)]
      /\ stk asegs m' lo (q) /\ asan_env asegs m' /\ rw_cells asegs m' (sh FL) (shadow_zero_cells 3).

  Definition FreeListInit_stmt_A : Prop :=
    forall (FL esz mx lo : Z) (junk : list byte),
    forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m FL [CB 24%nat junk] -> FL <> 0%Z -> (0 <= esz < 2^64)%Z -> (0 <= mx < 2^31)%Z ->
    asan_env asegs m -> rw_cells asegs m (sh FL) (shadow_zero_cells 3) ->
    0x609000 <= FL -> FL + 24 <= alloc_ceiling -> app_mem FL 24 -> FL mod 8 = 0 ->
    stk asegs m lo (q) -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
    mem_inv asegs m -> a0 = wz FL -> a1 = wz esz -> a2 = wz mx ->
    evt asegs (FreeListInit_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FL esz mx lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz FreeListInit_entryA) fc None m (seg_rom asegs)).

  Definition ListInit_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L fcmp ffree lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(L, L + 96)%Z; (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' L (llist_cells (L + 24) L 0 0 0 ffree fcmp)
      /\ stk asegs m' lo (q) /\ asan_env asegs m' /\ rw_cells asegs m' (sh L) (shadow_zero_cells 12).

  Definition ListInit_stmt_A : Prop :=
    forall (L fcmp ffree lo : Z) (junk : list byte),
    forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m L [CB 96%nat junk] -> L <> 0%Z -> (0 <= fcmp < 2^64)%Z -> (0 <= ffree < 2^64)%Z ->
    asan_env asegs m -> rw_cells asegs m (sh L) (shadow_zero_cells 12) ->
    0x609000 <= L -> L + 96 <= alloc_ceiling -> app_mem L 96 -> L mod 8 = 0 ->
    stk asegs m lo (q) -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 48 ->
    mem_inv asegs m -> a0 = wz L -> a1 = wz fcmp -> a2 = wz ffree ->
    evt asegs (ListInit_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L fcmp ffree lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ListInit_entryA) fc None m (seg_rom asegs)).

  Definition memptr_cmp_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ asan_env asegs m' /\ (-255 <= r <= 255)%Z.

  Definition memptr_cmp_stmt_A_at (entry : Z) : Prop :=
    forall (MP T n S lo : Z) (tok str slack : list byte)
           (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m MP (memptr_cells T n) ->
    bytes_at asegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n <= 2^43)%Z ->
    bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->

    asan_env asegs m -> rw_cells asegs m (sh MP) (shadow_zero_cells 2) ->
    shw m T n -> shw m S (Z.of_nat (length str) + 1) ->
    0x609000 <= MP -> MP + 16 <= alloc_ceiling -> app_mem MP 16 -> MP mod 8 = 0 ->
    T + Z.of_nat (length tok) <= alloc_ceiling -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
    Z.of_nat (length str) + 1 <= 2^43 ->
    stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 32 - A0_RT_STACK ->
    mem_inv asegs m -> a0 = wz MP -> a1 = wz S ->
    evt asegs (memptr_cmp_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz entry) fc None m (seg_rom asegs)).
  Definition memptr_cmp_stmt_A : Prop := memptr_cmp_stmt_A_at memptr_cmp_entryA.
  Definition memptr_cmp_nocase_stmt_A : Prop := memptr_cmp_stmt_A_at memptr_cmp_nocase_entryA.
End Stmts.

Section AStmts.
  Context {HC : HasCeiling}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Variable J : a0_judg FI AI.
  Local Notation K := (am_K FI AI).
  Local Notation BL := (list (block K)).
  Local Notation PS := (aps FI AI).

  Definition str_alloc_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LB : BL) (n lo : Z) (src : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k : K) (U : Z),
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ alloc_frame_A FI AI q lo st m m' LB
      /\ LB' = (k, U, n + 1) :: LB /\ RHEAP_A FI AI s' LB' m'
      /\ rw_cells asegs m' U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])]
      /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (n + 1).

  Definition str_alloc_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (SRC n lo : Z) (src : list byte) (bsrc : block K),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> n + 1 <= 2^26 -> am_budget FI AI s LB (n + 1) ->
    In bsrc LB -> blk_addr bsrc <= SRC -> SRC + n <= blk_addr bsrc + blk_size bsrc ->
    a0 = wz SRC -> a1 = wz n ->
    AJ FI AI J (str_alloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB n lo src m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz str_alloc_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition membuffer_destroy_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LBrest : BL) (MB lo : Z) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
      /\ apx FI AI [(MB, MB + 32)] LBrest q m m'
      /\ LB' = LBrest /\ RHEAP_A FI AI s' LBrest m'
      /\ rw_cells asegs m' MB (mbuf_cells 0 0 0)
      /\ am_nsec FI AI s' = am_nsec FI AI s.

  Definition membuffer_destroy_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBrest : BL) (st : fsstate FI) (MB A len cap lo : Z),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> mblocA FI AI LBrest q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
    shw m MB 32 ->
    ((A = 0 /\ LBrest = LB) \/ (exists k, In (k, A, cap + 1) LB /\ LBrest = lb_remove (am_K_eqb FI AI) k LB)) ->
    a0 = wz MB ->
    AJ FI AI J (membuffer_destroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LBrest MB lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition mownA (m : mem) (LB : BL) (A cap : Z) (ok : option K) (bs : list byte) : Prop :=
    match ok with
    | None => A = 0 /\ cap = 0 /\ bs = []
    | Some k => In (k, A, cap + 1) LB /\ rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs]
    end.

  Definition membuffer_assign_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LB : BL) (ok : option K) (MB A cap n lo : Z) (src : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A' cap' : Z) (ok' : option K) (bs' : list byte),
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
      /\ apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m'
      /\ RHEAP_A FI AI s' LB' m'
      /\ ((ok' = ok /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
          \/ (exists k', ok' = Some k' /\ LB' = (k', A', cap' + 1) :: lb_keepA FI AI ok LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1)))
      /\ rw_cells asegs m' MB (mbuf_cells A' n cap') /\ n <= cap' /\ cap' <= cap + n + 5
      /\ mownA m' LB' A' cap' ok' bs'
      /\ (n >= 1 -> firstn (Z.to_nat (n + 1)) bs' = src ++ [Z_to_bv 8 0]).

  Definition membuffer_assign_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (ok : option K)
           (MB SRC n A len cap lo : Z) (src bs : list byte),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 96 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + n + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + n + 6) ->
    mownA m LB A cap ok bs ->
    mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
    bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> 0 < SRC ->
    msrcA FI AI (lb_keepA FI AI ok LB) q st SRC n -> shw m SRC n -> SRC + n < 2^47 -> (SRC + n <= MB \/ MB + 32 <= SRC) ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n ->
    AJ FI AI J (membuffer_assign_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A cap n lo src m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_assign_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition membuffer_append_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LB : BL) (ok : option K) (MB A len cap n lo : Z) (src bs : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A' cap' : Z) (ok' : option K) (bs' : list byte),
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
      /\ apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m'
      /\ RHEAP_A FI AI s' LB' m'
      /\ ((ok' = ok /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
          \/ (exists k', ok' = Some k' /\ LB' = (k', A', cap' + 1) :: lb_keepA FI AI ok LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1)
                         /\ cap < len + n /\ cap + 5 <= cap' <= cap + Z.max 5 n))
      /\ rw_cells asegs m' MB (mbuf_cells A' (len + n) cap') /\ len + n <= cap' /\ cap' <= cap + n + 5
      /\ mownA m' LB' A' cap' ok' bs'
      /\ firstn (Z.to_nat len) bs' = firstn (Z.to_nat len) bs
      /\ (n >= 1 -> firstn (Z.to_nat (len + n + 1)) bs' = firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0]).

  Definition membuffer_insert_end_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (ok : option K)
           (MB SRC n A len cap lo : Z) (src bs : list byte),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + n + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + n + 6) ->
    mownA m LB A cap ok bs ->
    mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
    bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> 0 < SRC ->
    msrcA FI AI (lb_keepA FI AI ok LB) q st SRC n -> shw m SRC n -> SRC + n < 2^47 -> (SRC + n <= MB \/ MB + 32 <= SRC) ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n -> a3 = wz len ->
    AJ FI AI J (membuffer_append_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A len cap n lo src bs m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_insert_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition membuffer_append_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (ok : option K)
           (MB SRC n A len cap lo : Z) (src bs : list byte),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + n + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + n + 6) ->
    mownA m LB A cap ok bs ->
    mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
    bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> 0 < SRC ->
    msrcA FI AI (lb_keepA FI AI ok LB) q st SRC n -> shw m SRC n -> SRC + n < 2^47 -> (SRC + n <= MB \/ MB + 32 <= SRC) ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n ->
    AJ FI AI J (membuffer_append_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A len cap n lo src bs m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_append_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition membuffer_append_str_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (ok : option K)
           (MB SRC A len cap lo : Z) (str slack bs : list byte),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + Z.of_nat (length str) + 8 <= 2^28 ->
    am_budget_le FI AI s LB (cap + Z.of_nat (length str) + 6) ->
    mownA m LB A cap ok bs ->
    mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
    bytes_at asegs m SRC (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    (- (SRC + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 < SRC ->
    msrcA FI AI (lb_keepA FI AI ok LB) q st SRC (Z.of_nat (length str) + 1) -> shw m SRC (Z.of_nat (length str) + 1) ->
    (SRC + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling \/ (q <= SRC /\ SRC + Z.of_nat (length str) + 1 < 2^47)) ->
    Z.of_nat (length str) + 1 <= 2^43 ->
    (SRC + Z.of_nat (length str) + 1 <= MB \/ MB + 32 <= SRC) ->
    a0 = wz MB -> a1 = wz SRC ->
    AJ FI AI J (membuffer_append_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A len cap (Z.of_nat (length str)) lo str bs m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_append_str_entryA) fc None m (seg_rom asegs))
      s LB.

  Definition del_bytesA (bs : list byte) (idx num len : Z) : list byte :=
    upd_bytes bs (Z.to_nat idx) (firstn (Z.to_nat (len - idx - num)) (skipn (Z.to_nat (idx + num)) bs)).

  Definition membuffer_delete_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LB : BL) (ok : option K) (MB A len cap idx num lo : Z) (bs : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A' len' cap' : Z) (ok' : option K) (bs' : list byte),
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
      /\ apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m'
      /\ RHEAP_A FI AI s' LB' m'
      /\ ((ok' = ok /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
          \/ (exists k', ok' = Some k' /\ LB' = (k', A', cap' + 1) :: lb_keepA FI AI ok LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1)))
      /\ rw_cells asegs m' MB (mbuf_cells A' len' cap') /\ 0 <= len' <= cap' /\ cap' <= cap
      /\ mownA m' LB' A' cap' ok' bs'
      /\ ( (len = 0 /\ len' = 0 /\ bs' = bs)
         \/ (1 <= len /\ len' = len - num
             /\ firstn (Z.to_nat (len' + 1)) bs' = firstn (Z.to_nat len') (del_bytesA bs idx num len) ++ [Z_to_bv 8 0]) ).

  Definition membuffer_delete_stmt_A : Prop :=
    forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (ok : option K)
           (MB idx num A len cap lo : Z) (bs : list byte),
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 80 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
    mem_inv asegs m ->
    rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + 6) ->
    mownA m LB A cap ok bs ->
    mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
    0 <= idx -> 0 <= num -> idx + num <= len ->
    a0 = wz MB -> a1 = wz idx -> a2 = wz num ->
    AJ FI AI J (membuffer_delete_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A len cap idx num lo bs m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_delete_entryA) fc None m (seg_rom asegs))
      s LB.
End AStmts.
