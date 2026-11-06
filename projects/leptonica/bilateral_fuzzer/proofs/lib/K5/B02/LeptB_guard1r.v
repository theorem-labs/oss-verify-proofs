(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import LeptB_guard.

Ltac shbr ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru _ _ =>
                (* [comment removed for export] *)
                let szm1 := constr:(0%Z) in
                let S4 := eval vm_compute in (SLOW + 4)%Z in
                instr_at segs S4 ltac:(fun i2 =>
                  let szm1 := lazymatch i2 with
                              | OpImm ALU_ADD _ _ ?imm => eval vm_compute in (bv_unsigned imm)
                              | _ => constr:(0%Z) end in
                  let sz := eval vm_compute in (szm1 + 1)%Z in
                  let OK := fresh "SHOK" in
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        assert (OK : sh_ok b (X + sz - 1)) by (apply (shk_ok m a n X sz b ACC K); lia)
                    end
                  | fail 1 "shbr: cannot prove the access addressable:" X sz ];
                  let BB := fresh "BB" in
                  assert (BB : 0 <= bv_unsigned b < 8)
                    by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                  rewrite ?(sxb_small b) by lia;
                  shbr_merge ru FAST OK; clear K BB)
            | _ =>
                (* [comment removed for export] *)
                let OK := fresh "SHOK" in
                first [
                  match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr: cannot prove the 8-byte access addressable:" X ];
                apply sh_ok_8 in OK; [ | lia ];
                rewrite ?(sxb_small b) by lia;
                brF; clear K OK
            end)
      | _ => fail "shbr: no shk fact for" b
      end
  end.

Ltac guard_fix ::= try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix.

Ltac gwalk1 ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br | progress guard_fix; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
