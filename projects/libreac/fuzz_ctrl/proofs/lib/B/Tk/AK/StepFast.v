(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Lib/Mh_0039.v; 20 of its 47 lines of code are new or changed and 2575 lines of the source are left out. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import PropExec MState Mem Cells Exec ZBridge Step Frame Arr Image Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Ltac zsimp_fast :=
  (match goal with |- context [v_sltu _ _] => rewrite ?v_sltu_b2z | _ => idtac end);
  (match goal with |- context [v_slt _ _] => rewrite ?v_slt_b2z | _ => idtac end);
  (match goal with |- context [v_sltiu _ _] => rewrite ?v_sltiu_b2z | _ => idtac end);
  (match goal with |- context [v_slti _ _] => rewrite ?v_slti_b2z | _ => idtac end);
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange
            | zs_wrap e ]
  | |- _ => progress zs_idioms
  end; zb_fold_lits.

Ltac step_core_fast segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        (* [comment removed for export] *)
        eapply (evt_step_gen segs _ R F (Z_to_bv 64 pc) fc rv m ro w i sz);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | hide_rhs ltac:(fun _ =>      (* [comment removed for export] *)
            exec_pre i;
            exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
            try solve_load; try solve_store);
          reflexivity
        | lazymatch i with
          | Load _ _ _ _ _ => simp_regs; vnorm_for i
          | FLoad _ _ _ _ => simp_regs; vnorm_for i
          | _ => idtac
          end;
          mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.
