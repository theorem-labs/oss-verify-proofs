(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr RunConst Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).

Definition x4_body_stmt : Prop :=
  forall (Q : machine_state -> Prop) (mm : fmem) (F : bvmap 5 word) (fc : bv 32)
         (gp tp s5 s9 : word) (b0 b1 b2 b3 : word)
         (j9 j14 j15 j18 j19 j20 j22 j26 j27 : word)
         (SP DT4 DST dcap SS n IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 : Z) (obuf tbl sbuf : list byte) (cells : list deltX1)
         (fa : list word),
    mem_inv usegs mm ->
    bytes_at usegs mm DT4 tbl -> length tbl = 4096%nat ->
    x1_table_ok cells 11 -> tbl = firstn 4096 (x1_bytes' cells) ->
    u8arr usegs mm DST obuf -> Z.of_nat (length obuf) = dcap ->
    bytes_at usegs mm SS sbuf -> Z.of_nat (length sbuf) = n ->
    0 < DT4 -> DT4 + 4096 <= 2^47 -> 0 < DST -> DST + dcap <= 2^47 -> 0 < SS -> SS + n <= 2^47 ->
    (DST + dcap <= DT4 \/ DT4 + 4096 <= DST) -> (DST + dcap <= SS \/ SS + n <= DST) ->
    DT4 mod 2 = 0 -> 512 <= SP <= 2^47 ->
    DT4 + 4096 <= SP - 512 -> DST + dcap <= SP - 512 -> SS + n <= SP - 512 ->
    u64arr usegs mm (SP - 224) fa -> length fa = 15%nat ->
    nth_error fa 0 = Some (Z_to_bv 64 OP0) -> nth_error fa 1 = Some (Z_to_bv 64 OP1) ->
    nth_error fa 2 = Some (Z_to_bv 64 OP2) -> nth_error fa 3 = Some (Z_to_bv 64 OP3) ->
    nth_error fa 5 = Some (Z_to_bv 64 IP0) -> nth_error fa 6 = Some (Z_to_bv 64 IP1) ->
    nth_error fa 7 = Some (Z_to_bv 64 IP2) -> nth_error fa 8 = Some (Z_to_bv 64 IP3) ->
    nth_error fa 10 = Some b0 -> nth_error fa 11 = Some b1 -> nth_error fa 12 = Some b2 -> nth_error fa 13 = Some b3 ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    SS + 7 <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 -> OP0 + 5 <= DST + dcap -> DST <= OP1 -> OP1 + 5 <= DST + dcap ->
    DST <= OP2 -> OP2 + 5 <= DST + dcap -> DST <= OP3 -> OP3 + 5 <= DST + dcap ->
    (forall (mm' : fmem) (fa' : list word) (b0' b1' b2' b3' : word) (nb0 nb1 nb2 nb3 : Z)
            (j9' j15' j18' j19' j20' j22' j27' : word),
       munch [(DST, DST + dcap); (SP - 224, SP - 104)] mm mm' ->
       wmono usegs mm mm' -> mem_inv usegs mm' ->
       (exists obuf', u8arr usegs mm' DST obuf' /\ length obuf' = length obuf) ->
       u64arr usegs mm' (SP - 224) fa' -> length fa' = 15%nat ->
       nth_error fa' 0 = Some (Z_to_bv 64 (OP0 + 5)) -> nth_error fa' 1 = Some (Z_to_bv 64 (OP1 + 5)) ->
       nth_error fa' 2 = Some (Z_to_bv 64 (OP2 + 5)) -> nth_error fa' 3 = Some (Z_to_bv 64 (OP3 + 5)) ->
       nth_error fa' 5 = Some (Z_to_bv 64 (IP0 - nb0)) -> nth_error fa' 6 = Some (Z_to_bv 64 (IP1 - nb1)) ->
       nth_error fa' 7 = Some (Z_to_bv 64 (IP2 - nb2)) -> nth_error fa' 8 = Some (Z_to_bv 64 (IP3 - nb3)) ->
       nth_error fa' 10 = Some b0' -> nth_error fa' 11 = Some b1' -> nth_error fa' 12 = Some b2' -> nth_error fa' 13 = Some b3' ->
       bv_unsigned b0' mod 512 <> 0 -> bv_unsigned b1' mod 512 <> 0 -> bv_unsigned b2' mod 512 <> 0 -> bv_unsigned b3' mod 512 <> 0 ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       evt usegs Q (MS (mkR (Z_to_bv 64 (SP - 184)) (Z_to_bv 64 (SP - 512)) gp tp (Z_to_bv 64 (-16)) (Z_to_bv 64 (SP - 224))
                            (Z_to_bv 64 (-25)) b0' j9' (Z_to_bv 64 0x104e0) (Z_to_bv 64 DT4) (Z_to_bv 64 0xffc8) (Z_to_bv 64 (- DT4 - 1))
                            (Z_to_bv 64 (OP3 + 5)) j15' (Z_to_bv 64 (SP - 144)) (Z_to_bv 64 (-17)) j18' j19' j20' s5 j22'
                            (Z_to_bv 64 5) (Z_to_bv 64 6) s9 (Z_to_bv 64 (IP0 - nb0)) j27' (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4))
                       F (Z_to_bv 64 0x18cd0) fc None mm' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR (Z_to_bv 64 (SP - 184)) (Z_to_bv 64 (SP - 512)) gp tp (Z_to_bv 64 (-16)) (Z_to_bv 64 (SP - 224))
                         (Z_to_bv 64 (-25)) b0 j9 (Z_to_bv 64 0x104e0) (Z_to_bv 64 DT4) (Z_to_bv 64 0xffc8) (Z_to_bv 64 (- DT4 - 1))
                         j14 j15 (Z_to_bv 64 (SP - 144)) (Z_to_bv 64 (-17)) j18 j19 j20 s5 j22
                         (Z_to_bv 64 5) (Z_to_bv 64 6) s9 j26 j27 (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4))
                    F (Z_to_bv 64 0x18384) fc None mm (seg_rom usegs)).
