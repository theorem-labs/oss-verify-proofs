(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (a start state and a template per CONFIG_RSEQ value, the template computed in the build from this certificate's own run; the 27/29-pair auxv). *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc RotSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Regen Auxv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN Require Import T_SrcN.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN Require C_LE.

Definition ROOT (b : bool) : sstate := t_st (C_LE.HEAD_PN b).
Definition CONTRACTS : IMap.t contract := IMap.empty.
Definition PLAN0 : plan :=
  (PRun [291384%uint63]
    (PRun [291380%uint63]
      (PCase
        (PRun [291380%uint63]
          (PAssume (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
            (PAssume (FULe (VP 64%uint63 (wp 1%uint63)) (VL (wp 131071%uint63)))
              (PAssume (FULt (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 1%uint63))) (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 0%uint63))))
                (PCutDec 20%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (4%uint63, (VP 4%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VP 64%uint63 (wp 1%uint63))); (65%uint63, (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)))])))))
        (PRun [291380%uint63]
          (PCase
            (PRun [291380%uint63]
              (PAssume (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                (PAssume (FULe (VP 64%uint63 (wp 1%uint63)) (VL (wp 131071%uint63)))
                  (PAssume (FULt (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 1%uint63))) (VAlu ALU_SUB (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VP 64%uint63 (wp 0%uint63))))
                    (PCutDec 20%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (4%uint63, (VP 4%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63))); (64%uint63, (VP 64%uint63 (wp 1%uint63))); (65%uint63, (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)))])))))
            (PSetReg X13 (VL (wp 0%uint63))
              (PRun [291380%uint63]
                (PEcall 30%uint63 [(0%uint63, (VP 0%uint63 (wp 0%uint63))); (1%uint63, (VP 1%uint63 (wp 0%uint63))); (2%uint63, (VP 2%uint63 (wp 0%uint63))); (3%uint63, (VP 3%uint63 (wp 0%uint63))); (4%uint63, (VP 4%uint63 (wp 0%uint63))); (5%uint63, (VP 5%uint63 (wp 0%uint63))); (6%uint63, (VP 6%uint63 (wp 0%uint63))); (7%uint63, (VP 7%uint63 (wp 0%uint63))); (8%uint63, (VP 8%uint63 (wp 0%uint63))); (12%uint63, (VP 12%uint63 (wp 0%uint63)))])))))))).

Definition RUN0 : ctx := Ctx ITAB IMap.empty IMap.empty CONTRACTS (VL (wp 0%uint63)).
(* the state this plan's own run reaches at ecall 30, per flag, and the recorded sstate rebuilt against it *)
Definition HIT_0 := Eval vm_compute in Regen.Regen.ecall_at 30%uint63 (Regen.Regen.reach SEGS RotSrc.ROT RUN0 PLAN0 (ROOT false)).
Definition HIT_1 := Eval vm_compute in Regen.Regen.ecall_at 30%uint63 (Regen.Regen.reach SEGS RotSrc.ROT RUN0 PLAN0 (ROOT true)).
Definition HIT (b : bool) := if b then HIT_1 else HIT_0.
Definition T_SETTIDN_0 : sstate := Eval vm_compute in Regen.Regen.remake_st T_SrcN.T_SETTIDN HIT_0.
Definition T_SETTIDN_1 : sstate := Eval vm_compute in Regen.Regen.remake_st T_SrcN.T_SETTIDN HIT_1.
Definition T_SETTIDN (b : bool) : sstate := if b then T_SETTIDN_1 else T_SETTIDN_0.
Definition PLAN (b : bool) : plan := Regen.Regen.rebind_plan 30%uint63 (Regen.Regen.rebinds T_SrcN.T_SETTIDN (HIT b)) PLAN0.
Definition CUTS (b : bool) : IMap.t template := imap_of [(20%uint63, C_LE.HEAD_PN b)].
Definition ECALLS (b : bool) : IMap.t sstate := imap_of [(30%uint63, T_SETTIDN b)].
Definition CTX (b : bool) : ctx := Ctx ITAB (CUTS b) (ECALLS b) CONTRACTS (t_measure (C_LE.HEAD_PN b)).
Definition OBLS (b : bool) : list obligation := [

  (((FEq (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 47%uint63))) :: (s_facts (t_st (C_LE.HEAD_PN b)))),
   (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63)));

  (((FNe (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) :: (FNe (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) (VL (wp 47%uint63))) :: (s_facts (t_st (C_LE.HEAD_PN b)))),
   (FULt (VP 64%uint63 (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))) ].

Lemma WF : forall b, ctx_wfb (CTX b) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : forall b, check SEGS (CTX b) (PLAN b) (ROOT b) = Some (OBLS b).
Proof.
  intros [|]; rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok);
    [vm_cast_no_check (eq_refl (Some (OBLS true))) | vm_cast_no_check (eq_refl (Some (OBLS false)))].
Qed.
