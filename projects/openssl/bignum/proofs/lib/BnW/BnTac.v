(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Ltac show_state :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ _ ?m _) =>
      idtac "pc =" pc; idtac "mem =" m;
      let v := reg_val 1%Z in idtac "ra =" v;
      let v := reg_val 2%Z in idtac "sp =" v;
      let v := reg_val 8%Z in idtac "s0 =" v;
      let v := reg_val 10%Z in idtac "a0 =" v;
      let v := reg_val 11%Z in idtac "a1 =" v;
      let v := reg_val 12%Z in idtac "a2 =" v;
      let v := reg_val 13%Z in idtac "a3 =" v;
      let v := reg_val 14%Z in idtac "a4 =" v;
      let v := reg_val 15%Z in idtac "a5 =" v;
      let v := reg_val 16%Z in idtac "a6 =" v;
      let v := reg_val 17%Z in idtac "a7 =" v;
      let v := reg_val 5%Z in idtac "t0 =" v;
      let v := reg_val 6%Z in idtac "t1 =" v;
      let v := reg_val 7%Z in idtac "t2 =" v;
      let v := reg_val 28%Z in idtac "t3 =" v;
      let v := reg_val 29%Z in idtac "t4 =" v;
      let v := reg_val 30%Z in idtac "t5 =" v;
      let v := reg_val 31%Z in idtac "t6 =" v
  | |- _ => idtac "(goal is not an evt state)"
  end.

Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

Ltac addr_tac := unfold wa; first [ reflexivity | f_equal; lia ].

From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
Ltac ld_hd H :=
  lazymatch type of H with
  | limbs_at ?segs ?m ?A (?x :: ?ls) =>
      let a := cur_mem_addr in
      let RD := fresh "RD" in
      pose proof (limbs_at_read_hd segs m A x ls a H ltac:(addr_tac)) as RD;
      zstep; clear RD
  end.
