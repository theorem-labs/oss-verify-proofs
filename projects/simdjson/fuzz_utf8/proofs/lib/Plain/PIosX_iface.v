(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Plain/PIosX_iface.v: module paths and target names, 85 image addresses, initial cell values read from the image for simdjson/fuzz_utf8's plain binary. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg F_syscalls StdioFiles Stdio_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition so_act (so : stdout_st) : stdout_st := mkStdout true (so_buf so) (so_lbf_nl so) (so_first so).
Definition so_inact (so : stdout_st) : stdout_st := mkStdout false [] (so_lbf_nl so) (so_first so).

Definition PFWRITE : Z := 0xb911c.      (* [comment removed for export] *)
Definition PFFLUSH : Z := 0xb8274.      (* [comment removed for export] *)
Definition PWCRTOMB : Z := 0xb7f08.     (* [comment removed for export] *)
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
  rw_cells psegs m 0xcd640 [C8 (Z_to_bv 64 8)]                       (* [comment removed for export] *)
  /\ rw_cells psegs m 0xcd978 [C8 (Z_to_bv 64 0x75b34)]             (* [comment removed for export] *)
  /\ rw_cells psegs m 0xe2120 [C8 (Z_to_bv 64 0xcdfc0)]             (* [comment removed for export] *)
  /\ rw_cells psegs m 0xcdfe8 [C8 (Z_to_bv 64 0x9d478)].            (* [comment removed for export] *)
Definition ios_cout (m : mem) : Prop :=
  rw_cells psegs m 0xe18f8 [C8 (Z_to_bv 64 0xcd658)]
  /\ rw_cells psegs m 0xe1908 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe1920 [C4 z64]
  /\ rw_cells psegs m 0xe1928 [C8 (Z_to_bv 64 0xe16a8)]
  /\ rw_cells psegs m 0xe1988 [C8 z64]
  /\ rw_cells psegs m 0xe16a8 [C8 (Z_to_bv 64 0xcd948)]
  /\ rw_cells psegs m 0xe16e8 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xe2120); C8 (Z_to_bv 64 0xe1674)].
Definition ios_clog (m : mem) : Prop :=
  rw_cells psegs m 0xe1b78 [C8 (Z_to_bv 64 0xcd658)]
  /\ rw_cells psegs m 0xe1b88 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe1ba0 [C4 z64]
  /\ rw_cells psegs m 0xe1ba8 [C8 (Z_to_bv 64 0xe1708)]
  /\ rw_cells psegs m 0xe1c08 [C8 z64]
  /\ rw_cells psegs m 0xe1708 [C8 (Z_to_bv 64 0xcd948)]
  /\ rw_cells psegs m 0xe1748 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xe2120); C8 (Z_to_bv 64 0xe167c)].

(* [comment removed for export] *)
Definition ios_wide_shared (m : mem) : Prop :=
  rw_cells psegs m 0xcd760 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xcdaa8 [C8 (Z_to_bv 64 0x76298)]
  /\ rw_cells psegs m 0xe22b0 [C8 (Z_to_bv 64 0xcdd10)]
  /\ rw_cells psegs m 0xcdd38 [C8 (Z_to_bv 64 0x9dc44)]
  /\ rw_cells psegs m 0xe22c0 [C8 (Z_to_bv 64 0x21798)]
  /\ rw_cells psegs m 0xe3598 [C8 (Z_to_bv 64 0x103890)].
Definition ios_wcout (m : mem) : Prop :=
  rw_cells psegs m 0xe1998 [C8 (Z_to_bv 64 0xcd778)]
  /\ rw_cells psegs m 0xe19a8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe19c0 [C4 z64]
  /\ rw_cells psegs m 0xe19c8 [C8 (Z_to_bv 64 0xe1768)]
  /\ rw_cells psegs m 0xe1a28 [C8 z64]
  /\ rw_cells psegs m 0xe1768 [C8 (Z_to_bv 64 0xcda78)]
  /\ rw_cells psegs m 0xe17a8 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0xe22b0); C8 (Z_to_bv 64 0xe168c)].
Definition ios_wclog (m : mem) : Prop :=
  rw_cells psegs m 0xe1c18 [C8 (Z_to_bv 64 0xcd778)]
  /\ rw_cells psegs m 0xe1c28 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m 0xe1c40 [C4 z64]
  /\ rw_cells psegs m 0xe1c48 [C8 (Z_to_bv 64 0xe17c8)]
  /\ rw_cells psegs m 0xe1ca8 [C8 z64]
  /\ rw_cells psegs m 0xe17c8 [C8 (Z_to_bv 64 0xcda78)]
  /\ rw_cells psegs m 0xe1808 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0xe22b0); C8 (Z_to_bv 64 0xe1694)].
(* [comment removed for export] *)
Definition ios_cells (m : mem) : Prop :=
  ios_char_shared m /\ ios_cout m /\ ios_clog m /\ ios_wide_shared m /\ ios_wcout m /\ ios_wclog m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_addr (a : Z) : Prop :=
  0xcd640 <= a < 0xcd648 \/ 0xcd978 <= a < 0xcd980 \/ 0xcdfe8 <= a < 0xcdff0 \/ 0xcd760 <= a < 0xcd768 \/ 0xcdaa8 <= a < 0xcdab0 \/ 0xcdd38 <= a < 0xcdd40
  \/ 0xe16a8 <= a < 0xe1cb0 \/ 0xe2120 <= a < 0xe2128 \/ 0xe22b0 <= a < 0xe22c8 \/ 0xe3598 <= a < 0xe35a0.

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
