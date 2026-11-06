(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg StdioFiles PAtexit_cells.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Malloc Monad Stdio PState HarnessM.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PFUZZ_ENTRY : Z := 0x3c040.     (* [comment removed for export] *)
Definition PVEC : Z := 0xec2e8.            (* [comment removed for export] *)
Definition PVEC_GUARD : Z := 0xec2e0.      (* [comment removed for export] *)
Definition PFALLBACK : Z := 0xec390.       (* [comment removed for export] *)
Definition PFALLBACK_VT : Z := 0xd4e68.    (* [comment removed for export] *)
Definition PDTOR_THUNK : Z := 0x3c020.     (* [comment removed for export] *)
Definition PIOS_DTOR : Z := 0x80124.       (* [comment removed for export] *)
Definition PTRUN_RET : Z := 0x3bd10.       (* [comment removed for export] *)
Definition PHARNESS_STACK : Z := 16384.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_wr : list (Z * Z) := [(0xec2e0, 0xec3c0); (0x10e5a8, 0x10e5ac); (0x10e5d0, 0x10e5d8); (0x10e6d0, 0x10e6d8)].

Definition harness_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside client_wr a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).
Lemma harness_pres_of_rheap_pres : forall LB SP m m', rheap_pres LB SP m m' -> harness_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition UJT : Z := 0xdbbc8.
Definition ujt_meta (ch : Z) : list Z := [if ch =? 34 then 1 else 0; if ch =? 92 then 0 else 1; if ((ch =? 9) || (ch =? 10) || (ch =? 13) || (ch =? 32))%bool then 0 else 1].
Definition UJT_BYTES : list Z := flat_map ujt_meta (map Z.of_nat (seq 0 256)).
Definition client_img (m : mem) : Prop :=      (* [comment removed for export] *)
  rw_cells usegs m 0xd4e78 [C8 (Z_to_bv 64 0x57d64)] /\ rw_cells usegs m 0xd4e88 [C8 (Z_to_bv 64 0x3ff6c)]
  /\ rw_cells usegs m 0xda9f8 [C8 (Z_to_bv 64 0xd4c48)] /\ rw_cells usegs m 0xd4d40 [C8 (Z_to_bv 64 0x11e1a)]
  /\ rw_cells usegs m UJT [CB 768 (map (Z_to_bv 8) UJT_BYTES)].

(* [comment removed for export] *)
Definition patexit (n f2 a2 : Z) (m : mem) : Prop := patx_table n PCALL_THUNK PAEF_GUARD f2 a2 m.

(* [comment removed for export] *)
Definition client_static0 (m : mem) : Prop :=
  client_img m /\ (forall a : word, 0xec2e0 <= bv_unsigned a < 0xec3c0 -> m a = None) /\ patexit_main m.

Definition guard1 : list cell := [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition client_static (s : PState) (LB : list block) (m : mem) : Prop :=
  client_img m /\
  match ps_fa s with
  | None =>
      (forall a : word, 0xec2e0 <= bv_unsigned a < 0xec3c0 -> m a = None)        (* [comment removed for export] *)
      /\ patexit 2 0 0 m                                                           (* [comment removed for export] *)
  | Some p => exists V, In (p, V, 8) LB
      /\ rw_cells usegs m V [C8 (Z_to_bv 64 PFALLBACK)]
      /\ rw_cells usegs m PVEC_GUARD guard1
      /\ rw_cells usegs m PVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
      /\ rw_cells usegs m PFALLBACK [C8 (Z_to_bv 64 PFALLBACK_VT)]
      /\ patexit 3 PDTOR_THUNK PVEC m                                            (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneU.
  Variable fuzz_model : list Z -> M PState Z.      (* [comment removed for export] *)

  Definition fuzz_oneU_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (AB lo : Z) (m : mem)
      (r : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word) (LB' : list block),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ r = 0
      /\ mem_inv usegs m' /\ frm0 fc'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
      /\ rauxv_ok m' AB
      /\ harness_pres LB (bv_unsigned sp) m m'
      /\ RHEAP s' LB' m'
      /\ client_static s' LB' m'
      /\ ps_so s' = ps_so s
      /\ match ps_fa s with
         | Some _ => LB' = LB /\ ps_fa s' = ps_fa s        (* [comment removed for export] *)
         | None   => exists p V, LB' = (p, V, 8) :: LB /\ ps_fa s' = Some p
         end.

  Definition fuzz_oneU_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
      RHEAP s LB m ->
      bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      (forall i, 0 <= i < zlength payload -> outside client_wr (D + i)) ->      (* [comment removed for export] *)
      0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      client_static s LB m ->
      rauxv_ok m AB -> bv_unsigned sp <= AB ->
      stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] ->
      mem_inv usegs m -> frm0 fc ->
      tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) ->
      ra = Z_to_bv 64 PTRUN_RET ->                  (* [comment removed for export] *)
      implM usegs (fuzz_model payload) s
            (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 PFUZZ_ENTRY) fc None m (seg_rom usegs)).
  (* [comment removed for export] *)
  Definition fuzz_oneM_stmt : Prop := fuzz_oneU_stmt.
End FuzzOneU.
End CANSEC1.
