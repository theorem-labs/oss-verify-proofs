(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs RotUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2 Require Import T_Ubs2.

Definition ROOT : sstate := (t_st T_Ubs2.HEAD_E2).
Definition CUTS : IMap.t template := imap_of [(10%uint63, T_Ubs2.HEAD_E2); (20%uint63, T_Ubs2.HEAD_P2)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition CONTRACTS : IMap.t contract := IMap.empty.
Definition CTX : ctx := Ctx ITAB CUTS ECALLS CONTRACTS (t_measure T_Ubs2.HEAD_E2).
Definition PLAN : plan :=
  (PRun [297336%uint63]
    (PRun [297332%uint63; 297528%uint63]
      (PCase
        (PAssume (FULt (VP 64%uint63 (wp 15%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))
          (PAssume (FULt (VP 64%uint63 (wp 8%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))
            (PAssume (FULe (VP 64%uint63 (wp 8%uint63)) (VL (wp 2048%uint63)))
              (PAssume (FULt (VAlu ALU_SUB (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 8%uint63))) (VAlu ALU_SUB (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 0%uint63))))
                (PCutDec 10%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (10%uint63, (VP 10%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VP 64%uint63 (wp 8%uint63))); (65%uint63, (VBlob false 2%uint63 (VP 64%uint63 (wp 0%uint63)) 8%uint63))])))))
        (PAssume (FEq (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VP 64%uint63 (wp 8%uint63))) (VP 3%uint63 (wp 0%uint63)))
          (PSetReg X9 (VP 3%uint63 (wp 0%uint63))
            (PSetReg X10 (VL (wp 0%uint63))
              (PRun [297332%uint63; 297528%uint63]
                (PCut 20%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (10%uint63, (VP 10%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VL (wp 0%uint63))); (65%uint63, (VP 6%uint63 (wp 0%uint63)))])))))))).
Definition OBLS : list obligation := [

  (((FNe (VBlob false 2%uint63 (VP 64%uint63 (wp 0%uint63)) 8%uint63) (VL (wp 0%uint63))) :: (s_facts (t_st T_Ubs2.HEAD_E2))),
   (FULt (VP 64%uint63 (wp 15%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)));

  (((FEq (VBlob false 2%uint63 (VP 64%uint63 (wp 0%uint63)) 8%uint63) (VL (wp 0%uint63))) :: (s_facts (t_st T_Ubs2.HEAD_E2))),
   (FEq (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VP 64%uint63 (wp 8%uint63))) (VP 3%uint63 (wp 0%uint63)))) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2.HEAD_E2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.
