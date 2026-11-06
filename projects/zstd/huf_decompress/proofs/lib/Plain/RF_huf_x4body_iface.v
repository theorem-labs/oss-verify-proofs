(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).

Definition x4_body_stmt : Prop :=
  forall (Q : machine_state -> Prop) (mm : fmem) (F : bvmap 5 word) (fc : bv 32)
         (sp gp tp a0 s7 s9 : word) (b0 b1 b2 b3 : word)
         (j9 j11 j12 j13 j15 j16 j18 j20 j22 j28 : word)
         (DT4 DST dcap SS n IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 : Z) (obuf tbl sbuf : list byte),
    mem_inv psegs mm ->
    bytes_at psegs mm DT4 tbl -> length tbl = 4096%nat ->
    u8arr psegs mm DST obuf -> Z.of_nat (length obuf) = dcap ->
    bytes_at psegs mm SS sbuf -> Z.of_nat (length sbuf) = n ->
    0 < DT4 -> DT4 + 4096 <= 2^47 -> 0 < DST -> DST + dcap <= 2^47 -> 0 < SS -> SS + n <= 2^47 ->
    (DST + dcap <= DT4 \/ DT4 + 4096 <= DST) -> (DST + dcap <= SS \/ SS + n <= DST) ->
    SS + 7 <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 -> OP0 + 5 <= DST + dcap -> DST <= OP1 -> OP1 + 5 <= DST + dcap ->
    DST <= OP2 -> OP2 + 5 <= DST + dcap -> DST <= OP3 -> OP3 + 5 <= DST + dcap ->
    (forall (mm' : fmem) (b0' b1' b2' b3' : word) (nb0 nb1 nb2 nb3 : Z)
            (j9' j11' j12' j13' j15' j16' j18' j20' j22' j28' : word),
       munch [(DST, DST + dcap)] mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
       (exists obuf', u8arr psegs mm' DST obuf' /\ length obuf' = length obuf) ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       evt psegs Q (MS (mkR b2' sp gp tp (Z_to_bv 64 (IP2 - nb2)) (Z_to_bv 64 (IP1 - nb1)) (Z_to_bv 64 (IP0 - nb0)) b3' j9' a0
                            j11' j12' j13' (Z_to_bv 64 0x10510) j15' j16' (Z_to_bv 64 (IP3 - nb3)) j18' (Z_to_bv 64 DT4) j20'
                            (Z_to_bv 64 (OP3 + 5)) j22' s7 (Z_to_bv 64 0x1082c) s9 b1' b0' j28'
                            (Z_to_bv 64 (OP0 + 5)) (Z_to_bv 64 (OP1 + 5)) (Z_to_bv 64 (OP2 + 5)))
                       F (Z_to_bv 64 0x18ce0) fc None mm' (seg_rom psegs))) ->
    evt psegs Q (MS (mkR b2 sp gp tp (Z_to_bv 64 IP2) (Z_to_bv 64 IP1) (Z_to_bv 64 IP0) b3 j9 a0 j11 j12 j13
                         (Z_to_bv 64 0x10510) j15 j16 (Z_to_bv 64 IP3) j18 (Z_to_bv 64 DT4) j20 (Z_to_bv 64 OP3) j22 s7
                         (Z_to_bv 64 0x1082c) s9 b1 b0 j28 (Z_to_bv 64 OP0) (Z_to_bv 64 OP1) (Z_to_bv 64 OP2))
                    F (Z_to_bv 64 0x1888c) fc None mm (seg_rom psegs)).
