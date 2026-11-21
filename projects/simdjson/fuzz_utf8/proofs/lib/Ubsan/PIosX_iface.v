(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PIosX_iface.v: module paths and target names, 85 image addresses, initial cell values read from the image for simdjson/fuzz_utf8's ubsan binary. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg F_syscalls StdioFiles Stdio_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition so_act (so : stdout_st) : stdout_st := mkStdout true (so_buf so) (so_lbf_nl so) (so_first so).
Definition so_inact (so : stdout_st) : stdout_st := mkStdout false [] (so_lbf_nl so) (so_first so).

Definition PFWRITE : Z := 0xc32d0.      (* [comment removed for export] *)
Definition PFFLUSH : Z := 0xc2428.      (* [comment removed for export] *)
Definition PWCRTOMB : Z := 0xc20bc.     (* [comment removed for export] *)
Definition PIOSX_DEPTH : Z := 512.      (* [comment removed for export] *)

Section Stmts.
  Definition icpt_post (W : list (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (P : mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ P m'.

  (* [comment removed for export] *)
  Definition fwrite0_out_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk usegs m lo (bv_unsigned sp) -> stdout_file m so_x -> ssp_cells m guard -> mem_inv usegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDOUT ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt usegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stdout_file m' (so_act so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFWRITE) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fwrite0_err_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk usegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> mem_inv usegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDERR ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt usegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFWRITE) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fflush_err_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk usegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> mem_inv usegs m ->
      a0 = Z_to_bv 64 RSTDERR ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt usegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition wcr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (P : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(P, P + 1)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' P [C1 (Z_to_bv 8 0)].

  Definition wcrtomb0_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (P : Z) (jb : list byte),
      stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m P [CB 1 jb] -> bv_unsigned sp <= P -> P + 4 <= bv_unsigned sp + 4096 ->
      mem_inv usegs m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 0 ->
      GLOBALS_TOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
      evt usegs (wcr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PWCRTOMB) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Section Out.
    Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Definition fflush_out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        (lo : Z) (guard : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
      fun _ st' ms' => exists (so' : stdout_st),
        st' = set_so so' st /\ so_buf so' = []
        /\ icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                     (fun m' => stdout_file m' (so_inact so')) ms'.

    Definition fflush_out_stmt : Prop :=
      forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
        stk usegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
        so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) ->
        so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->          (* [comment removed for export] *)
        ssp_cells m guard -> mem_inv usegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
        implM usegs (stdout_exit_flush get_so set_so) s
               (fflush_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom usegs)).
  End Out.
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_char_shared (m : mem) : Prop :=
  rw_cells usegs m 0xd77f0 [C8 (Z_to_bv 64 8)]                       (* [comment removed for export] *)
  /\ rw_cells usegs m 0xd7b28 [C8 (Z_to_bv 64 0x7fce8)]             (* [comment removed for export] *)
  /\ rw_cells usegs m 0xec5d0 [C8 (Z_to_bv 64 0xd8170)]             (* [comment removed for export] *)
  /\ rw_cells usegs m 0xd8198 [C8 (Z_to_bv 64 0xa762c)].            (* [comment removed for export] *)
Definition ios_cout (m : mem) : Prop :=
  rw_cells usegs m 0xebda8 [C8 (Z_to_bv 64 0xd7808)]
  /\ rw_cells usegs m 0xebdb8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0xebdd0 [C4 z64]
  /\ rw_cells usegs m 0xebdd8 [C8 (Z_to_bv 64 0xebb58)]
  /\ rw_cells usegs m 0xebe38 [C8 z64]
  /\ rw_cells usegs m 0xebb58 [C8 (Z_to_bv 64 0xd7af8)]
  /\ rw_cells usegs m 0xebb98 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xec5d0); C8 (Z_to_bv 64 0xebb24)].
Definition ios_clog (m : mem) : Prop :=
  rw_cells usegs m 0xec028 [C8 (Z_to_bv 64 0xd7808)]
  /\ rw_cells usegs m 0xec038 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0xec050 [C4 z64]
  /\ rw_cells usegs m 0xec058 [C8 (Z_to_bv 64 0xebbb8)]
  /\ rw_cells usegs m 0xec0b8 [C8 z64]
  /\ rw_cells usegs m 0xebbb8 [C8 (Z_to_bv 64 0xd7af8)]
  /\ rw_cells usegs m 0xebbf8 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xec5d0); C8 (Z_to_bv 64 0xebb2c)].

(* [comment removed for export] *)
Definition ios_wide_shared (m : mem) : Prop :=
  rw_cells usegs m 0xd7910 [C8 (Z_to_bv 64 8)]
  /\ rw_cells usegs m 0xd7c58 [C8 (Z_to_bv 64 0x8044c)]
  /\ rw_cells usegs m 0xec760 [C8 (Z_to_bv 64 0xd7ec0)]
  /\ rw_cells usegs m 0xd7ee8 [C8 (Z_to_bv 64 0xa7df8)]
  /\ rw_cells usegs m 0xec770 [C8 (Z_to_bv 64 0x21498)]
  /\ rw_cells usegs m 0xeda48 [C8 (Z_to_bv 64 0x10dd40)].
Definition ios_wcout (m : mem) : Prop :=
  rw_cells usegs m 0xebe48 [C8 (Z_to_bv 64 0xd7928)]
  /\ rw_cells usegs m 0xebe58 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0xebe70 [C4 z64]
  /\ rw_cells usegs m 0xebe78 [C8 (Z_to_bv 64 0xebc18)]
  /\ rw_cells usegs m 0xebed8 [C8 z64]
  /\ rw_cells usegs m 0xebc18 [C8 (Z_to_bv 64 0xd7c28)]
  /\ rw_cells usegs m 0xebc58 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xec760); C8 (Z_to_bv 64 0xebb3c)].
Definition ios_wclog (m : mem) : Prop :=
  rw_cells usegs m 0xec0c8 [C8 (Z_to_bv 64 0xd7928)]
  /\ rw_cells usegs m 0xec0d8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0xec0f0 [C4 z64]
  /\ rw_cells usegs m 0xec0f8 [C8 (Z_to_bv 64 0xebc78)]
  /\ rw_cells usegs m 0xec158 [C8 z64]
  /\ rw_cells usegs m 0xebc78 [C8 (Z_to_bv 64 0xd7c28)]
  /\ rw_cells usegs m 0xebcb8 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xec760); C8 (Z_to_bv 64 0xebb44)].
(* [comment removed for export] *)
Definition ios_cells (m : mem) : Prop :=
  ios_char_shared m /\ ios_cout m /\ ios_clog m /\ ios_wide_shared m /\ ios_wcout m /\ ios_wclog m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_addr (a : Z) : Prop :=
  0xd77f0 <= a < 0xd77f8 \/ 0xd7b28 <= a < 0xd7b30 \/ 0xd8198 <= a < 0xd81a0 \/ 0xd7910 <= a < 0xd7918 \/ 0xd7c58 <= a < 0xd7c60 \/ 0xd7ee8 <= a < 0xd7ef0
  \/ 0xebb58 <= a < 0xec160 \/ 0xec5d0 <= a < 0xec5d8 \/ 0xec760 <= a < 0xec778 \/ 0xeda48 <= a < 0xeda50.

Lemma ios_cells_magree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, ios_addr a -> P a) -> ios_cells m -> ios_cells m'.
Proof.
  intros P m m' HP HA IOS.
  assert (T : forall A cs, rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ios_addr a) -> rw_cells usegs m' A cs).
  { intros A cs H HR. eapply rw_cells_magree; [exact HP | exact H |]. intros a Ha. apply HA, HR, Ha. }
  unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply T; [eassumption | cbn [cells_size csize Nat.add]; unfold ios_addr; intros a Ha; lia]).
Qed.

(* [comment removed for export] *)
Lemma ios_cells_munch : forall W m m', ios_cells m -> munch W m m' -> wmono usegs m m' ->
  (forall a, ios_addr a -> outside W a) -> ios_cells m'.
Proof.
  intros W m m' IOS MU WM HW. eapply (ios_cells_magree (fun a => outside W a) m m'); [apply magree_of_munch; [exact MU | exact WM] | exact HW | exact IOS].
Qed.
