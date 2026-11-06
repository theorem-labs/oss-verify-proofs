(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F9 Require Import F_memcpy F_fmt_fp_lib F_printf_iface.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJMB Require Import ShZero QcF IcptCells IcptCellsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition icpt_cells (m : word -> option byte) : Prop :=
  rdn rsegs m (Z_to_bv 64 0x1544f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ef828))
  /\ rdn rsegs m (Z_to_bv 64 0x1563a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13dcd8))
  /\ rdn rsegs m (Z_to_bv 64 0x1563b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x143fd8)).

Lemma icpt_cells_munch : forall W m m', aapp_all W -> munch W m m' -> icpt_cells m -> icpt_cells m'.
Proof.
  intros W m m' HW MU (H1 & H2 & H3). unfold icpt_cells.
  split; [|split]; (eapply rdn_munch_a; [exact HW | exact MU | | eassumption]); rewrite unsigned_lit by lia; cbn; lia.
Qed.

Definition PCOM_DEPTH : Z := 2400.
Definition pcom_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).
Definition pcom_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A VA lo : Z),
    let q := bv_unsigned sp in
    a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    bytes_at rsegs m A (zb FMT_G) -> 65536 <= A -> A + 6 <= 0x150000 -> shk rsegs m A 6 ->
    stk rsegs m lo q -> lo <= q - PCOM_DEPTH -> 0x10007fff8000 <= lo -> q <= 0x7fffffffff00 ->
    aenv m -> mem_inv rsegs m ->
    evt rsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6e528) fc None m (seg_rom rsegs)).
