(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition AFS_MALLOC_0 : Z := 0x5b704.   (* [comment removed for export] *)
Definition AFS_MALLOC_2 : Z := 0x5ba08.   (* [comment removed for export] *)
Definition AFS_MALLOC_3 : Z := 0x5bba4.   (* [comment removed for export] *)
Definition AFS_MALLOC_7 : Z := 0x5c100.   (* [comment removed for export] *)
Definition AFS_FREE_7   : Z := 0x5c27c.   (* [comment removed for export] *)
Definition ASET_SHADOW_F8 : Z := 0x076650. (* [comment removed for export] *)
Definition AFS7_MAXLIVE : nat := 128.     (* [comment removed for export] *)
Definition AFS_FREE7_STACK : Z := 96.      (* [comment removed for export] *)

Section Iface5.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  #[local] Notation RFS := (as_RFS H).
  #[local] Notation FSB := (as_FSB H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stack_malloc_0_stmt : Prop := stack_malloc_stmt H 0 AFS_MALLOC_0.
  Definition stack_malloc_2_stmt : Prop := stack_malloc_stmt H 2 AFS_MALLOC_2.
  Definition stack_malloc_3_stmt : Prop := stack_malloc_stmt H 3 AFS_MALLOC_3.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition set_shadow_00_stmt : Prop := set_shadow_stmt 0x00 ASET_SHADOW_00.
  Definition set_shadow_f8_stmt : Prop := set_shadow_stmt 0xf8 ASET_SHADOW_F8.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition stack_malloc7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z) junk1 junk2 junk3,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (FSB, FSB + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 7); (sh ff, sh ff + fshn 7)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ RFS ((7, ff, fp) :: LF) m'
      /\ rw_cells bsegs m' ff [CB 24 junk1; C8 sp; CB (Z.to_nat (fsz 7 - 40)) junk2; C8 (Z_to_bv 64 fp)]
      /\ SHAD m' ff (poison_bytes (Z.to_nat (n / 8)) 0)
      /\ rw_cells bsegs m' (sh ff + n / 8) [CB (Z.to_nat (fshn 7 - n / 8)) junk3]
      /\ rw_cells bsegs m' fp [C1 (b8 1)]
      /\ ACONST m'.

  Definition stack_malloc_7_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (n lo : Z),
      RFS LF m -> (length LF < AFS7_MAXLIVE)%nat ->
      a0 = Z_to_bv 64 n -> n mod 8 = 0 -> 8 <= n <= fsz 7 ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv bsegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt bsegs (stack_malloc7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFS_MALLOC_7) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition stack_free7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (ff fp n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - AFS_FREE7_STACK, bv_unsigned sp); (fp, fp + 1); (sh ff, sh ff + n / 8)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ RFS (lf_remove ff LF) m'
      /\ SHAD m' ff (poison_bytes (Z.to_nat (n / 8)) 0xf5)
      /\ rw_cells bsegs m' fp [C1 (b8 0)]
      /\ ACONST m'.

  Definition stack_free_7_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (ff fp n lo : Z) (sbs : list byte),
      RFS LF m -> In (7, ff, fp) LF ->
      a0 = Z_to_bv 64 ff -> a1 = Z_to_bv 64 n -> n mod 8 = 0 -> 8 <= n <= fsz 7 ->
      rw_cells bsegs m (ff + fsz 7 - 8) [C8 (Z_to_bv 64 fp)] ->
      SHAD m ff sbs -> Z.of_nat (length sbs) = n / 8 ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_FREE7_STACK ->
      mem_inv bsegs m -> ACONST m ->
      evt bsegs (stack_free7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF ff fp n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFS_FREE_7) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition asan_rt_hyps5 : Prop :=
    stack_malloc_0_stmt /\ stack_malloc_2_stmt /\ stack_malloc_3_stmt /\ set_shadow_00_stmt /\ set_shadow_f8_stmt.
  (* [comment removed for export] *)
  Definition asan_rt_hyps5x : Prop := stack_malloc_7_stmt /\ stack_free_7_stmt.
End Iface5.
