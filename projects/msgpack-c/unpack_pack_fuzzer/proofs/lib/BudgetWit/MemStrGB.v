(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Br/MemcpyG.v and Br/StrG.v: the memcpy and strnlen bridges restated over BudgetWit.Rzb.rzb *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Image ITree Nodes NodesM Decode Arr Omono.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls F_memcpyA F_memcpy F_memchr F_strnlen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG MemcpyG StrG.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb RegsEqvB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ShapeAlg(TSet).
Open Scope Z_scope.
Unset Lia Cache.

Local Notation rom := (seg_rom rsegs).
Theorem memcpy_G_b :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (mo : Model) (d s n : Z) (src junk : list byte) (K : TSet),
    getr R 10 = Z_to_bv 64 d -> getr R 11 = Z_to_bv 64 s -> getr R 12 = Z_to_bv 64 n ->
    0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    ret_pc (getr R 1) = getr R 1 ->
    bytes_at rsegs M s src -> length src = Z.to_nat n ->
    rw_cells rsegs M d [CB (Z.to_nat n) junk] ->
    (s + n <= d \/ d + n <= s) ->
    mem_inv rsegs M -> m_halted mo = None -> m_vm_lazy mo = [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte),
        (forall r, In r kept_regs -> getr R' r = getr R r) -> getr R' 10 = Z_to_bv 64 d ->
        munch [(d, d + n)] M M' -> wmono rsegs M M' -> mem_inv rsegs M' ->
        rw_cells rsegs M' d [CB (Z.to_nat n) src] -> bytes_at rsegs M' s src ->
        omono M M' ->
        rzb rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo) K) ->
    rzb rsegs (mkCfg (MS R F (Z_to_bv 64 RMEMCPY_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo d s n src junk K Hd Hs Hn Rd Rs Rn Hra SRC LEN DST SEP MI HH HL HK.
  assert (Ud : bv_unsigned (getr R 10) = d) by (rewrite Hd; apply unsigned_lit; lia).
  assert (Us : bv_unsigned (getr R 11) = s) by (rewrite Hs; apply unsigned_lit; lia).
  assert (Un : bv_unsigned (getr R 12) = n) by (rewrite Hn; apply unsigned_lit; lia).
  apply rzb_to_mkR. unfold mkR_of.
  eapply (evt_rzb rsegs _ _ mo K).
  - apply evt_omono. apply (memcpy_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
             (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
             (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
             (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
             F fc M src junk); rewrite ?Ud, ?Us, ?Un; assumption.
  - exact HH.
  - exact HL.
  - intros ms' [(t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M' & -> & MU & WM & MI' & RW & BA) OM].
    cbn [ms_mem MS] in OM.
    rewrite Hra. rewrite ?Ud, ?Us, ?Un in MU. rewrite ?Ud, ?Us, ?Un in RW. rewrite ?Ud, ?Us, ?Un in BA.
    apply (HK _ M'); try assumption.
    intros r Hr. apply kept_mkR. exact Hr.
Qed.
Theorem strnlen_G_b :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (mo : Model) (s n lo : Z) (buf : list byte) (K : TSet),
    getr R 10 = Z_to_bv 64 s -> getr R 11 = Z_to_bv 64 n ->
    0 < s < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    ret_pc (getr R 1) = getr R 1 ->
    stk F_syscalls.rsegs M lo (bv_unsigned (getr R 2)) -> lo <= bv_unsigned (getr R 2) - RSTRNLEN_STACK ->
    bytes_at F_syscalls.rsegs M s buf -> memchr_ok s 0 n buf ->
    (s + Z.of_nat (length buf) <= bv_unsigned (getr R 2) - RSTRNLEN_STACK \/ bv_unsigned (getr R 2) <= s) ->
    mem_inv F_syscalls.rsegs M -> m_halted mo = None -> m_vm_lazy mo = [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte),
        (forall r, In r kept_regs -> getr R' r = getr R r) -> getr R' 10 = Z_to_bv 64 (strnlen_res n buf) ->
        munch [(bv_unsigned (getr R 2) - RSTRNLEN_STACK, bv_unsigned (getr R 2))] M M' -> wmono F_syscalls.rsegs M M' ->
        mem_inv F_syscalls.rsegs M' -> stk F_syscalls.rsegs M' lo (bv_unsigned (getr R 2)) -> bytes_at F_syscalls.rsegs M' s buf ->
        omono M M' ->
        rzb F_syscalls.rsegs (mkCfg (MS R' F (getr R 1) fc None M' (seg_rom F_syscalls.rsegs)) mo) K) ->
    rzb F_syscalls.rsegs (mkCfg (MS R F (Z_to_bv 64 RSTRNLEN_SYM) fc None M (seg_rom F_syscalls.rsegs)) mo) K.
Proof.
  intros R F fc M mo s n lo buf K Hs Hn Rs Rn Hra STK LO BUF OK SEP MI HH HL HK.
  assert (Us : bv_unsigned (getr R 10) = s) by (rewrite Hs; apply unsigned_lit; lia).
  assert (Un : bv_unsigned (getr R 11) = n) by (rewrite Hn; apply unsigned_lit; lia).
  apply rzb_to_mkR. unfold mkR_of.
  eapply (evt_rzb F_syscalls.rsegs _ _ mo K).
  - apply evt_omono.
    apply (strnlen_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
             (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
             (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
             (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
             F fc M buf lo); rewrite ?Us, ?Un; try assumption; unfold RSTRNLEN_STACK in *; try assumption; lia.
  - exact HH.
  - exact HL.
  - intros ms' [(t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M' & -> & MU & WM & MI' & STK' & BA) OM].
    cbn [ms_mem MS] in OM.
    rewrite Hra. rewrite ?Us, ?Un in MU. rewrite ?Us, ?Un in BA.
    apply (HK _ M'); try assumption.
    + intros r Hr. apply kept_mkR. exact Hr.
    + cbn. rewrite Un. reflexivity.
Qed.
