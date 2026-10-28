(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_wkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac gforget_junk1 n :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := greg_val R n in
    lazymatch x with
    | context [Z.lor] => let j := fresh "jk" in generalize x; intro j
    | context [Z.shiftl] => let j := fresh "jk" in generalize x; intro j
    | context [bv_swrap] => let j := fresh "jk" in generalize x; intro j
    | context [sx32] => let j := fresh "jk" in generalize x; intro j
    | _ => idtac
    end
  end.
Ltac gforget_junk :=
  gforget_junk1 1%Z; gforget_junk1 5%Z; gforget_junk1 6%Z; gforget_junk1 7%Z; gforget_junk1 10%Z; gforget_junk1 11%Z; gforget_junk1 12%Z; gforget_junk1 13%Z;
  gforget_junk1 14%Z; gforget_junk1 15%Z; gforget_junk1 16%Z; gforget_junk1 17%Z; gforget_junk1 28%Z; gforget_junk1 29%Z; gforget_junk1 30%Z; gforget_junk1 31%Z.
Ltac gexplore_f stop fin :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => stop pc
          | _ => idtac end;
          first [ gguard | (gstep; gforget_junk) ]);
  first [ fin tt | (let KB := fresh "KB" in if_cases KB; clear KB; gexplore_f stop fin) ].

Ltac grun_f := repeat first [ gguard | (gstep; gforget_junk) ].
Ltac grun_f_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | (gstep; gforget_junk) ]).

Ltac wrun_f := repeat first [ gguard | (wstep; gforget_junk) ].
Ltac wrun_f_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | (wstep; gforget_junk) ]).
