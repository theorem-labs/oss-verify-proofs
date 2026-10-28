(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numkitr Sj_stage2_numr_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac r_s0_sown :=
  lazymatch goal with |- context [Z.land (Z.modulo (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 8 (sown ?c))) 63))) 63) _) 9] =>
    let SR := fresh "SR" in pose proof (sown_range c) as SR;
    let S0 := fresh "S0" in let S1 := fresh "S1" in
    destruct (Z.eq_dec (sown c) 0) as [S0|S1]; [rewrite S0 | replace (sown c) with 1%Z by lia] end;
  match goal with |- context [Z.land ?X 9] => let v := eval vm_compute in (Z.land X 9) in change (Z.land X 9) with v end.

Ltac r_s0_b2z :=
  lazymatch goal with |- context [Z.land ((Z.b2z ?c + -1) mod 18446744073709551616) 9] => destruct c end;
  change (Z.land ((Z.b2z true + -1) mod 18446744073709551616) 9) with 0%Z;
  change (Z.land ((Z.b2z false + -1) mod 18446744073709551616) 9) with 9%Z.

Ltac r_leaf KXA KXB KF0 KF9 :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 0x43990%Z => eapply KXA; s2_close_memx
    | 0x46de8%Z => eapply KXB; [s2_errok_code | s2_close_memx]
    | 0x47014%Z =>
        first [ r_s0_b2z; [ (s2_tape2; s2_kvr KF0; [s2_num_word|]; eapply MEMI_DSL; [s2_close_mem0 | reflexivity ..]) | (eapply (KF9 9%Z); [lia | s2_close_memx]) ]
              | r_s0_sown; [ (s2_tape2; s2_kvr KF0; [s2_num_word|]; eapply MEMI_DSL; [s2_close_mem0 | reflexivity ..]) | (eapply (KF9 9%Z); [lia | s2_close_memx]) ]
              | (eapply KF9; [lia | s2_close_memx]) ]
    end end.
Ltac r_cuts pc := lazymatch pc with 0x47014%Z => fail | 0x46de8%Z => fail | 0x43990%Z => fail | _ => idtac end.
