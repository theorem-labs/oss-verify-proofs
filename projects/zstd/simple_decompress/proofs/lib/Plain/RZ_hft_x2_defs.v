(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition x2_cells (m : fmem) (DT : Z) (cw : list Z) : Prop :=
  u8arr psegs m (DT + 4) (u16s (map (Z_to_bv 64) cw)) /\ Z.of_nat (length cw) = 8192.

(* [comment removed for export] *)
Definition x2_l1_post (gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPF DT : Z) (m : fmem) (cw : list Z) (pos n v : Z) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x21 x22 x25 x26 x27 x28 x29 m' cw',
    ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1d24c) fc None m' (seg_rom psegs)
    /\ munch [(DT + 4, DT + 16388)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ x2_cells m' DT cw' /\ cells_written cw cw' pos n v.

(* [comment removed for export] *)
Ltac znth_upd :=
  repeat match goal with |- context [Znth ?j (Zupd ?i ?v ?l)] =>
    first [ rewrite (Znth_Zupd_other i j v l) by lia
          | replace j with i by lia; rewrite (Znth_Zupd_same i v l) by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia) ] end.

(* [comment removed for export] *)
Ltac cw_round :=
  lazymatch goal with |- cells_written ?cw ?cw' ?c ?k ?v =>
    split; [unfold FseNCount.Zlength; rewrite !Zupd_length; reflexivity|]; split;
    [ let k0 := fresh "k0" in let H1 := fresh in let H2 := fresh in intros k0 H1 H2; rewrite !Znth_Zupd_other by lia; reflexivity
    | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      let E := fresh "E" in
      assert (E : i = c \/ i = c + 1 \/ i = c + 2 \/ i = c + 3 \/ i = c + 4 \/ i = c + 5 \/ i = c + 6 \/ i = c + 7) by lia;
      repeat (destruct E as [E|E]; [first [exfalso; lia | subst i; znth_upd; reflexivity]|]); first [exfalso; lia | subst i; znth_upd; reflexivity] ]
  end.

(* [comment removed for export] *)
Definition x2_l2_post (gp tp x1 x6 x7 x11 x12 x13 x15 x16 x18 x19 x20 x22 x23 x24 x27 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPF DT : Z) (m : fmem) (cw : list Z) (pos n v : Z) : machine_state -> Prop :=
  fun ms' => exists x5 x8 x9 x10 x14 x17 x21 x25 x26 x28 m' cw',
    ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1d610) fc None m' (seg_rom psegs)
    /\ munch [(DT + 4, DT + 16388)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ x2_cells m' DT cw' /\ cells_written cw cw' pos n v.

(* [comment removed for export] *)
Definition x2_sk_post (gp tp x1 x5 x6 x7 x11 x13 x14 x15 x16 x18 x19 x20 x23 x24 x25 x26 x27 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPF DT : Z) (m : fmem) (cw : list Z) (pos n v : Z) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x10 x12 x17 x21 x22 x28 m' cw',
    ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1d5fc) fc None m' (seg_rom psegs)
    /\ munch [(DT + 4, DT + 16388)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ x2_cells m' DT cw' /\ cells_written cw cw' pos n v.
