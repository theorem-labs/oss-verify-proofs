(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac bi_enum :=
  let BCE := fresh "BCE" in
  lazymatch goal with
  | BDC : rw_cells _ _ _ _ |- _ =>
    lazymatch type of BDC with
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 8))%bool
                | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 64))%bool ] end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 8))%bool
                | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool ] end
    | context [C4 (edenot ?E ?e)] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 8))%bool
                | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool ] end
    end;
    cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
  end.

Lemma bit_init_proof : bit_init_stmt.
Proof.
  unfold bit_init_stmt, bit_init_stmt_at, PHUF_BITINIT.
  intros until junk. intros MI BDC BDA SRCB SRCL B0 B1 S0 S1 N32 DJ.
  assert (MU : munch [(BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  destruct (Z.eq_dec n 1) as [N1|N1]; [rewrite N1 in *|].
  1: kx_auto [] 120%nat
    [KZImg 0x10000 0x14000; KZRange BD 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + 1) 4096 (2^47);
    KZAlign BD 8; KZWr BD 40; KZDisj BD 40 SRC 1]
    [(SRC, 1); (0x110f8, 24)].
  all: lazymatch goal with
       | N1 : _ <> 1 |- _ =>
           kx_auto_v 8 [] 120%nat
             [KZImg 0x10000 0x14000; KZRange BD 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
             KZRange (SRC + n) 4096 (2^47); KZAlign BD 8; KZWr BD 40; KZDisj BD 40 SRC n]
             [(SRC, n); (0x110f8, 24)]
       | _ => idtac
       end.
  all: lazymatch goal with |- context [Z_to_bv 64 0x25c9c] => kx_trap_fast | _ => idtac end.
  all: try solve [exfalso; clear - N1 SRCL KXBR KXBR0 KXBR1; lia].
  all: kx_mem.
  all: zstep.
  all: try bi_enum.
  all: kx_abs.
  all: (apply evt_done; unfold bit_init_post; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]).
  all: first
    [ (* [comment removed for export] *)
      left; split; [first [reflexivity | lia]|]; split; [lia|];
      lazymatch type of BDC with
      | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
      | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
      end;
      split; [lia|]; split; [intros; lia|]; rewrite KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned; unfold bitd_cells, bitd_ptr;
      first [ replace (8 <=? n) with true by (symmetry; apply Z.leb_le; lia);
              replace (SRC + n - 8) with (SRC + n + -8) by lia; exact BDC
            | replace (8 <=? n) with false by (symmetry; apply Z.leb_gt; lia); exact BDC
            | exact BDC ]
    | (* [comment removed for export] *)
      right; split; [vm_compute; reflexivity|]; split; [reflexivity|];
      destruct (rw_cells_forget usegs _ _ _ BDC) as [bs Hbs]; exists bs; exact Hbs ].
Qed.
