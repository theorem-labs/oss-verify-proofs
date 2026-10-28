(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Export Layout.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation bgusegs := ImageBg.bgusegs.

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells bgusegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells bgusegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bgusegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x351670 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x31e3a8); (RSTDOUT_BUF, 0x351eb8)]%Z m m'
      /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
      /\ stk bgusegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ rw_cells bgusegs m' 0x31ca98 [C8 (Z_to_bv 64 0x350fd8)] /\ rw_cells bgusegs m' 0x350fd8 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bgusegs m lo (bv_unsigned sp) ->
      rw_cells bgusegs m 0x351228 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      rw_cells bgusegs m 0x351660 [C8 z64] ->
      rw_cells bgusegs m 0x31e2b8 [C8 (Z_to_bv 64 0x31e1d0)] ->
      rw_cells bgusegs m (0x31e1d0 + 8) [C8 z64; C8 z64] ->
      rw_cells bgusegs m (0x31e1d0 + 40) [C8 z64; C8 z64; C8 z64] ->
      rw_cells bgusegs m (0x31e1d0 + 140) [C4 (Z_to_bv 64 0xffffffff)] ->
      rw_cells bgusegs m 0x31e3a8 [C8 (Z_to_bv 64 RSTDOUT)] ->
      rw_cells bgusegs m 0x31e1c8 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells bgusegs m 0x31ca98 [C8 (Z_to_bv 64 0x350fd8)] -> rw_cells bgusegs m 0x350fd8 [C8 guard] ->
      mem_inv bgusegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x353000 <= lo)%Z ->
      implM bgusegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b440c) fc None m (seg_rom bgusegs)).
End StdioExitStatement.

Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  impl segs (at_node segs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros segs St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
