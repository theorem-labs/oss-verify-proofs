(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PZD_BITINIT : Z := 0x1d904.

Definition seqd_bit_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (BD SRC n : Z) (src junk : list byte),
  mem_inv usegs m ->
  rw_cells usegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  bytes_at usegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  evt usegs (bit_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc BD SRC n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_BITINIT) fc None m (seg_rom usegs)).

Theorem seqd_bit_init_proof : seqd_bit_init_stmt.
Proof.
  unfold seqd_bit_init_stmt, PZD_BITINIT.
  intros until junk. intros MI BDC BDA SRCB SRCL B0 B1 S0 S1 DJ.
  assert (MU : munch [(BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  destruct (Z.eq_dec n 1) as [N1|N1]; [rewrite N1 in *|].
  1: kx_auto [] 120%nat
    [KZImg 0x10000 0x14000; KZRange BD 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + 1) 4096 (2^47);
    KZAlign BD 8; KZWr BD 40; KZDisj BD 40 SRC 1]
    [(SRC, 1); (0x10780, 24)].
  all: lazymatch goal with
       | N1 : _ <> 1 |- _ =>
           kx_auto_v 8 [] 120%nat
             [KZImg 0x10000 0x14000; KZRange BD 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^47);
             KZRange (SRC + n) 4096 (2^47); KZAlign BD 8; KZWr BD 40; KZDisj BD 40 SRC n]
             [(SRC, n); (0x10780, 24)]
       | _ => idtac
       end.
  all: lazymatch goal with |- context [Z_to_bv 64 0x1db94] => kx_trap_fast | _ => idtac end.
  all: try solve [exfalso; clear - N1 SRCL KXBR KXBR0 KXBR1; lia].
  all: kx_mem.
  all: zstep.
  all: try bi_enum.
  all: kx_abs.
  all: (apply evt_done; unfold bit_init_post; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]).
  all: first
    [       left; split; [first [reflexivity | lia]|]; split; [lia|];
      lazymatch type of BDC with
      | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
      | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
      end;
      split; [lia|]; split; [intros; lia|]; rewrite KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned; unfold bitd_cells, bitd_ptr;
      first [ replace (8 <=? n) with true by (symmetry; apply Z.leb_le; lia);
              replace (SRC + n - 8) with (SRC + n + -8) by lia; exact BDC
            | replace (8 <=? n) with false by (symmetry; apply Z.leb_gt; lia); exact BDC
            | exact BDC ]
    |       right; split; [vm_compute; reflexivity|]; split; [reflexivity|];
      destruct (rw_cells_forget usegs _ _ _ BDC) as [bs Hbs]; exists bs; exact Hbs ].
Qed.
