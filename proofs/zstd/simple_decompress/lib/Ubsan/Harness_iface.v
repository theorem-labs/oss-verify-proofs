(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Malloc Monad Stdio Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation PDCTX := 0x48120%Z (only parsing).          (* [comment removed for export] *)
Notation PGOT_TRACE := 0x36e40%Z (only parsing).     (* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PFUZZ_ENTRY : Z := 0x14848.    (* [comment removed for export] *)
Definition PEMPTY : Z := 0x48100.         (* [comment removed for export] *)
Definition PGOT_STDERR : Z := 0x36e28.    (* [comment removed for export] *)
Definition PSTDERR_PTR : Z := 0x36dd8.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HARNESS_STACK : Z := 16384.

(* [comment removed for export] *)
Definition harness_cells (m : mem) : Prop :=
  rw_cells usegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
  /\ rw_cells usegs m PSTDERR_PTR [C8 (wz RSTDERR)]
  /\ rw_cells usegs m PDCTX [C8 (wz 0)]                    (* [comment removed for export] *)
  /\ rw_cells usegs m PGOT_TRACE [C8 (wz 0); C8 (wz 0)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition harness_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  exists m0, munch [(PDCTX, PDCTX + 8)] m m0 /\ wmono usegs m m0 /\ rheap_pres LB SP m0 m'.

(* [comment removed for export] *)
Lemma harness_pres_intro : forall LB SP m m',
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (PDCTX <= a < PDCTX + 8) ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  (forall a, PDCTX <= a < PDCTX + 8 -> wview usegs m' (wa a) <> None) ->
  harness_pres LB SP m m'.
Proof.
  intros LB SP m m' H HW.
  exists (fun x : word => if (PDCTX <=? bv_unsigned x) && (bv_unsigned x <? PDCTX + 8) then m' x else m x). split; [| split].
  - intros x [Hx _]. destruct (Z.leb_spec PDCTX (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (PDCTX + 8)); cbn [andb]; try reflexivity.
    exfalso. apply Hx. lia.
  - intros x. unfold wview.
    destruct (Z.leb_spec PDCTX (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (PDCTX + 8)); cbn [andb]; try (intros W; exact W).
    intros _. specialize (HW (bv_unsigned x) ltac:(lia)). unfold wview, wa in HW. rewrite Z_to_bv_bv_unsigned in HW. exact HW.
  - intros a Ha Hc. assert (EA : bv_unsigned (wa a) = a).
    { unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. }
    unfold wview. rewrite EA.
    destruct (Z.leb_spec PDCTX a); destruct (Z.ltb_spec a (PDCTX + 8)); cbn [andb];
      try (split; [reflexivity| intros W; exact W]);
      (destruct (H a Ha Hc ltac:(lia)) as [E W]; split; [exact E| unfold wview in W; rewrite EA in W; exact W]).
Qed.

Lemma harness_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> harness_pres LB SP m m'.
Proof. intros LB SP m m' H. exists m. split; [apply munch_refl|]. split; [apply wmono_refl| exact H]. Qed.

(* [comment removed for export] *)
Definition stderr_file0 (m : mem) : Prop :=
  rw_cells usegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE RSTDERR_BUF 0 2 (wz 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)).

Lemma stderr_file0_file : forall m, stderr_file0 m -> stderr_file m.
Proof. intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOne.
  (* [comment removed for export] *)

  Definition fuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (AB lo : Z) (m : mem)
      (r : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ -2^31 <= r < 2^31
      /\ mem_inv usegs m' /\ frm0 fc'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
      /\ rauxv_ok m' AB
      /\ harness_pres LB (bv_unsigned sp) m m'                  (* [comment removed for export] *)
      /\ rw_cells usegs m' PDCTX [C8 (wz 0)]                      (* [comment removed for export] *)
      /\ RHEAP s' LB m'
      /\ ps_so s' = ps_so s.

  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
      RHEAP s LB m ->
      (* [comment removed for export] *)
      bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      D mod 16 = 0 -> 0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      (D + zlength payload <= PDCTX \/ PDCTX + 8 <= D) ->     (* [comment removed for export] *)
      (* [comment removed for export] *)
      harness_cells m -> stderr_file0 m ->
      (* [comment removed for export] *)
      rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->     (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] ->
      mem_inv usegs m -> frm0 fc ->
      tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = wz D -> a1 = wz (zlength payload) ->
      implM usegs (Prog.fuzz_one payload) s
            (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz PFUZZ_ENTRY) fc None m (seg_rom usegs)).
End FuzzOne.
End CANSEC1.
