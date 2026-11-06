(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc RotSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2 Require Import T_Src2.

Definition ROOT : sstate := (t_st T_Src2.HEAD_P2).
Definition CUTS : IMap.t template := imap_of [(20%uint63, T_Src2.HEAD_P2)].
Definition ECALLS : IMap.t sstate := imap_of [(30%uint63, T_Src2.T_SETTID2)].
Definition CONTRACTS : IMap.t contract := IMap.empty.
Definition CTX : ctx := Ctx ITAB CUTS ECALLS CONTRACTS (t_measure T_Src2.HEAD_P2).
Definition PLAN : plan :=
  (PRun [291384%uint63]
    (PRun [291380%uint63]
      (PCase
        (PRun [291380%uint63]
          (PAssume (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
            (PAssume (FULe (VP 64%uint63 (wp 1%uint63)) (VL (wp 131071%uint63)))
              (PAssume (FULt (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 1%uint63))) (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 0%uint63))))
                (PCutDec 20%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (10%uint63, (VP 10%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VP 64%uint63 (wp 1%uint63))); (65%uint63, (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)))])))))
        (PRun [291380%uint63]
          (PCase
            (PRun [291380%uint63]
              (PAssume (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                (PAssume (FULe (VP 64%uint63 (wp 1%uint63)) (VL (wp 131071%uint63)))
                  (PAssume (FULt (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 1%uint63))) (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 0%uint63))))
                    (PCutDec 20%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (10%uint63, (VP 10%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VP 64%uint63 (wp 1%uint63))); (65%uint63, (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)))])))))
            (PSetReg X13 (VL (wp 0%uint63))
              (PRun [291380%uint63]
                (PEcall 30%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (10%uint63, (VP 10%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63)))])))))))).
Definition OBLS : list obligation := [

  (((FEq (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 47%uint63))) :: (s_facts (t_st T_Src2.HEAD_P2))),
   (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63)));

  (((FNe (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) :: (FNe (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 47%uint63))) :: (s_facts (t_st T_Src2.HEAD_P2))),
   (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2.HEAD_P2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.
