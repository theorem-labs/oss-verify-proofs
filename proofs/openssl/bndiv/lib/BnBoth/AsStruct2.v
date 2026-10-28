(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AsStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac shl_with ACC AL :=
  let ad := cur_mem_addr in
  let X := sh_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch type of ACC with
    | acc segs ?mb ?a ?n =>
        lazymatch goal with
        | MU : munch ?W mb mc |- _ =>
            let RD := fresh "RDsh" in
            pose proof (acc_rdX segs W mb mc a n X ad ACC MU ltac:(shl_off) AL ltac:(lia) ltac:(shl_gran AL) ltac:(lia) ltac:(lia)
                                ltac:(sh_addr_s)) as RD;
            step; clear RD
        | _ => fail "shl_with: no [munch W mb mc] from the acc fact's memory to the current memory"
        end
    | _ => fail "shl_with: the first argument is not an [acc] fact on this image"
    end
  end.

(* [comment removed for export] *)
Ltac shl_limb ACC AL BD k :=
  let ad := cur_mem_addr in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch type of ACC with
    | acc segs ?mb ?p (8 * ?n)%Z =>
        lazymatch goal with
        | MU : munch ?W mb mc |- _ =>
            let RD := fresh "RDsh" in
            pose proof (acc_rd_limb segs W mb mc p n 0%Z k ad ACC MU ltac:(shl_off) AL BD eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                                    ltac:(unfold wa, shad; f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftr_div_pow2 by (clear; lia);
                                          change (2 ^ 3)%Z with 8%Z; unfold SHB; clear; Z.div_mod_to_equations; lia)) as RD;
            step; clear RD
        | _ => fail "shl_limb: no [munch W mb mc] from the acc fact's memory to the current memory"
        end
    | _ => fail "shl_limb: the first argument is not of the form [acc segs mb p (8 * n)]"
    end
  end.
