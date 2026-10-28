(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AREALLOC_STUB : Z := 0x1bf17c.   (* [comment removed for export] *)
Definition AREALLOC_ICPT : Z := 0x1bf7b4.   (* [comment removed for export] *)
Definition APC0_REALLOC  : Z := 0x1bf8f0.   (* [comment removed for export] *)
Definition AREALLOC_STACK : Z := 8192.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AFS_MALLOC_0 : Z := 0x1a254c.    (* [comment removed for export] *)
Definition AFS_MALLOC_2 : Z := 0x1a2850.    (* [comment removed for export] *)
Definition AFS_MALLOC_6 : Z := 0x1a3024.    (* [comment removed for export] *)
Definition AFS_FREE_6   : Z := 0x1a31c0.    (* [comment removed for export] *)
Definition ASET_SHADOW_F8 : Z := 0x1c14cc.  (* [comment removed for export] *)

Section IfaceX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Local Abbreviation SR := (as_SR H).  Local Abbreviation VIS := (as_VIS H).  Local Abbreviation AKREL := (as_AKREL H).
  Local Abbreviation MPRES := (as_MPRES H).  Local Abbreviation RHEAP := (as_RHEAP H).  Local Abbreviation rauxv_ok := (as_rauxv_ok H).
  Local Abbreviation lb_remove := (as_lb_remove H).  Local Abbreviation alloc_ok := (as_alloc_ok H).
  Local Abbreviation AL := (as_AL H).  Local Abbreviation Cm := (as_Cm H).  Local Abbreviation Cf := (as_Cf H).
  Local Abbreviation CHAIN := (as_chain H).  Local Abbreviation TR := (as_TR H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition realloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (old n lo B : Z) (bs : list byte) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' : Z) junk (p' : bptr) (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
      /\ apres H (lb_remove p LB) (bv_unsigned sp) m m'
      /\ ablock_range H A' n /\ RHEAP s' ((p', A', n) :: lb_remove p LB) m'
      /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min old n)) (firstn (Z.to_nat (Z.min old n)) bs);
                               CB (Z.to_nat (n - Z.min old n)) junk]
      /\ addressable m' A' n
      /\ ACONST m'
      /\ AL s' >= AL s - Cm n - Cf old.

  (* [comment removed for export] *)
  Definition realloc_stmt_at (entry stack pc0 : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (p : bptr) (A old n lo B : Z)
           (errv : word) (mo : Model) (CH : list (Z * Z)) (bs sbs : list byte),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> In (p, A, old) LB -> alloc_ok s LB n -> Cm n + Cf old <= AL s ->
      rw_cells asegs m A [CB (Z.to_nat old) bs] -> SHAD m A sbs -> Z.of_nat (length sbs) = nsh old ->
      rauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      CHAIN m (bv_unsigned s0) CH -> trace_ok TR pc0 (bv_unsigned ra :: map snd CH) ->
      a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= 64512 -> old <= 64512 ->   (* [comment removed for export] *)
      SR (realloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old n lo B bs m mo) (mkCfg msF mo).

  Definition realloc_stmt : Prop := realloc_stmt_at AREALLOC_STUB AREALLOC_STACK APC0_REALLOC.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stack_malloc_0_stmt : Prop := stack_malloc_stmt H 0 AFS_MALLOC_0.
  Definition stack_malloc_2_stmt : Prop := stack_malloc_stmt H 2 AFS_MALLOC_2.
  (* [comment removed for export] *)
  Definition stack_malloc_stmt_n (k entry : Z) (nlive : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (lo : Z),
      as_RFS H LF m -> (length LF < nlive)%nat ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt asegs (stack_malloc_post H k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition stack_malloc_6_stmt : Prop := stack_malloc_stmt_n 6 AFS_MALLOC_6 256.
  Definition set_shadow_00_stmt : Prop := set_shadow_stmt 0x00 ASET_SHADOW_00.
  Definition set_shadow_f8_stmt : Prop := set_shadow_stmt 0xf8 ASET_SHADOW_F8.

  (* [comment removed for export] *)
  Definition stack_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (ff fp lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (fp, fp + 1); (sh ff, sh ff + fshn 6)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ as_RFS H (lf_remove ff LF) m'
      /\ SHAD m' ff (poison_bytes (Z.to_nat (fshn 6)) 0xf5)
      /\ ACONST m'.
  Definition stack_free_6_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (ff fp lo n : Z) junk1 junk2 (spv : word),
      as_RFS H LF m -> In (6, ff, fp) LF ->
      rw_cells asegs m ff [CB 24 junk1; C8 spv; CB (Z.to_nat (fsz 6 - 40)) junk2; C8 (Z_to_bv 64 fp)] ->
      a0 = Z_to_bv 64 ff -> a1 = Z_to_bv 64 n -> 0 <= n <= fsz 6 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (stack_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF ff fp lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFS_FREE_6) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition slack_law : Prop :=
    forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> wr_at asegs m (A + n) ((- (A + n)) mod 8).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rheap_perm : Prop :=
    forall s LB LB' m, RHEAP s LB m -> Permutation LB LB' -> RHEAP s LB' m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition AGOT_SSPX : Z := 0x5e9798.     (* [comment removed for export] *)
  Definition ACANARYX : Z := 0xc01cd0.      (* [comment removed for export] *)
  Definition canary_law : Prop :=
    forall s LB m, RHEAP s LB m ->
      exists can : Z, rw_cells asegs m AGOT_SSPX [C8 (Z_to_bv 64 ACANARYX)] /\ rw_cells asegs m ACANARYX [C8 (Z_to_bv 64 can)] /\ 0 <= can < 2^64.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition asan_rt_hyps_x : Prop :=
    asan_rt_hyps H /\ realloc_stmt
    /\ stack_malloc_0_stmt /\ stack_malloc_2_stmt /\ stack_malloc_6_stmt /\ stack_free_6_stmt
    /\ set_shadow_00_stmt /\ set_shadow_f8_stmt
    /\ slack_law /\ rheap_perm /\ canary_law.

  (* [comment removed for export] *)
  Lemma HHx_slack_law : asan_rt_hyps_x -> slack_law.
  Proof. intros X. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))))). Qed.
  Lemma HHx_rheap_perm : asan_rt_hyps_x -> rheap_perm.
  Proof. intros X. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 X)))))))))). Qed.
  Lemma HHx_canary : asan_rt_hyps_x -> canary_law.
  Proof. intros X. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 X)))))))))). Qed.
End IfaceX.
