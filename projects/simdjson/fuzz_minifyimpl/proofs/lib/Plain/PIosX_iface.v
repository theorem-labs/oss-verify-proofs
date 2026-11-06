(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls StdioFiles Stdio_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition so_act (so : stdout_st) : stdout_st := mkStdout true (so_buf so) (so_lbf_nl so) (so_first so).
Definition so_inact (so : stdout_st) : stdout_st := mkStdout false [] (so_lbf_nl so) (so_first so).

Definition PFWRITE : Z := 0xb9394.      (* [comment removed for export] *)
Definition PFFLUSH : Z := 0xb84ec.      (* [comment removed for export] *)
Definition PWCRTOMB : Z := 0xb8180.     (* [comment removed for export] *)
Definition PIOSX_DEPTH : Z := 512.      (* [comment removed for export] *)

Section Stmts.
  Definition icpt_post (W : list (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (P : mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ P m'.

  (* [comment removed for export] *)
  Definition fwrite0_out_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk psegs m lo (bv_unsigned sp) -> stdout_file m so_x -> ssp_cells m guard -> mem_inv psegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDOUT ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt psegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stdout_file m' (so_act so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFWRITE) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition fwrite0_err_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk psegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> mem_inv psegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDERR ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt psegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFWRITE) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition fflush_err_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk psegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> mem_inv psegs m ->
      a0 = Z_to_bv 64 RSTDERR ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo ->
      evt psegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                           (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition wcr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (P : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(P, P + 1)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp) /\ rw_cells psegs m' P [C1 (Z_to_bv 8 0)].

  Definition wcrtomb0_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (P : Z) (jb : list byte),
      stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m P [CB 1 jb] -> bv_unsigned sp <= P -> P + 4 <= bv_unsigned sp + 4096 ->
      mem_inv psegs m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 0 ->
      GLOBALS_TOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
      evt psegs (wcr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PWCRTOMB) fc None m (seg_rom psegs)).

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
        stk psegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
        so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) ->
        so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->          (* [comment removed for export] *)
        ssp_cells m guard -> mem_inv psegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
        implM psegs (stdout_exit_flush get_so set_so) s
               (fflush_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom psegs)).
  End Out.
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_char_shared (m : mem) : Prop :=
  rw_cells psegs m 0xcdac8 [C8 (Z_to_bv 64 8)]                       (* [comment removed for export] *)
  /\ rw_cells psegs m 0xcde00 [C8 (Z_to_bv 64 0x75e6c)]             (* [comment removed for export] *)
  /\ rw_cells psegs m 0xe2580 [C8 (Z_to_bv 64 0xce448)]             (* [comment removed for export] *)
  /\ rw_cells psegs m 0xce470 [C8 (Z_to_bv 64 0x9d6f0)].            (* [comment removed for export] *)
Definition ios_cout (m : mem) : Prop :=
  rw_cells psegs m 0xe1d58 [C8 (Z_to_bv 64 0xcdae0)]
  /\ rw_cells psegs m 0xe1d68 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe1d80 [C4 z64]
  /\ rw_cells psegs m 0xe1d88 [C8 (Z_to_bv 64 0xe1b08)]
  /\ rw_cells psegs m 0xe1de8 [C8 z64]
  /\ rw_cells psegs m 0xe1b08 [C8 (Z_to_bv 64 0xcddd0)]
  /\ rw_cells psegs m 0xe1b48 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xe2580); C8 (Z_to_bv 64 0xe1ad4)].
Definition ios_clog (m : mem) : Prop :=
  rw_cells psegs m 0xe1fd8 [C8 (Z_to_bv 64 0xcdae0)]
  /\ rw_cells psegs m 0xe1fe8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe2000 [C4 z64]
  /\ rw_cells psegs m 0xe2008 [C8 (Z_to_bv 64 0xe1b68)]
  /\ rw_cells psegs m 0xe2068 [C8 z64]
  /\ rw_cells psegs m 0xe1b68 [C8 (Z_to_bv 64 0xcddd0)]
  /\ rw_cells psegs m 0xe1ba8 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xe2580); C8 (Z_to_bv 64 0xe1adc)].

(* [comment removed for export] *)
Definition ios_wide_shared (m : mem) : Prop :=
  rw_cells psegs m 0xcdbe8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xcdf30 [C8 (Z_to_bv 64 0x765d0)]
  /\ rw_cells psegs m 0xe2710 [C8 (Z_to_bv 64 0xce198)]
  /\ rw_cells psegs m 0xce1c0 [C8 (Z_to_bv 64 0x9debc)]
  /\ rw_cells psegs m 0xe2720 [C8 (Z_to_bv 64 0x22238)]
  /\ rw_cells psegs m 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)].
Definition ios_wcout (m : mem) : Prop :=
  rw_cells psegs m 0xe1df8 [C8 (Z_to_bv 64 0xcdc00)]
  /\ rw_cells psegs m 0xe1e08 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe1e20 [C4 z64]
  /\ rw_cells psegs m 0xe1e28 [C8 (Z_to_bv 64 0xe1bc8)]
  /\ rw_cells psegs m 0xe1e88 [C8 z64]
  /\ rw_cells psegs m 0xe1bc8 [C8 (Z_to_bv 64 0xcdf00)]
  /\ rw_cells psegs m 0xe1c08 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xe2710); C8 (Z_to_bv 64 0xe1aec)].
Definition ios_wclog (m : mem) : Prop :=
  rw_cells psegs m 0xe2078 [C8 (Z_to_bv 64 0xcdc00)]
  /\ rw_cells psegs m 0xe2088 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe20a0 [C4 z64]
  /\ rw_cells psegs m 0xe20a8 [C8 (Z_to_bv 64 0xe1c28)]
  /\ rw_cells psegs m 0xe2108 [C8 z64]
  /\ rw_cells psegs m 0xe1c28 [C8 (Z_to_bv 64 0xcdf00)]
  /\ rw_cells psegs m 0xe1c68 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xe2710); C8 (Z_to_bv 64 0xe1af4)].
(* [comment removed for export] *)
Definition ios_cells (m : mem) : Prop :=
  ios_char_shared m /\ ios_cout m /\ ios_clog m /\ ios_wide_shared m /\ ios_wcout m /\ ios_wclog m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_addr (a : Z) : Prop :=
  0xcdac8 <= a < 0xcdad0 \/ 0xcde00 <= a < 0xcde08 \/ 0xce470 <= a < 0xce478 \/ 0xcdbe8 <= a < 0xcdbf0 \/ 0xcdf30 <= a < 0xcdf38 \/ 0xce1c0 <= a < 0xce1c8
  \/ 0xe1b08 <= a < 0xe2110 \/ 0xe2580 <= a < 0xe2588 \/ 0xe2710 <= a < 0xe2728 \/ 0xe39f8 <= a < 0xe3a00.

Lemma ios_cells_magree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, ios_addr a -> P a) -> ios_cells m -> ios_cells m'.
Proof.
  intros P m m' HP HA IOS.
  assert (T : forall A cs, rw_cells psegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ios_addr a) -> rw_cells psegs m' A cs).
  { intros A cs H HR. eapply rw_cells_magree; [exact HP | exact H |]. intros a Ha. apply HA, HR, Ha. }
  unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply T; [eassumption | cbn [cells_size csize Nat.add]; unfold ios_addr; intros a Ha; lia]).
Qed.

(* [comment removed for export] *)
Lemma ios_cells_munch : forall W m m', ios_cells m -> munch W m m' -> wmono psegs m m' ->
  (forall a, ios_addr a -> outside W a) -> ios_cells m'.
Proof.
  intros W m m' IOS MU WM HW. eapply (ios_cells_magree (fun a => outside W a) m m'); [apply magree_of_munch; [exact MU | exact WM] | exact HW | exact IOS].
Qed.
