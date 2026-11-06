From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
Import ListNotations.
Open Scope Z_scope.

Lemma amo_al4 : forall z, 0 <= z < 2^64 -> z mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 z) = true.
Proof.
  intros z Hz H4. unfold amo_aligned, amo_bytes.
  rewrite Z_to_bv_unsigned, (bv_wrap_small 64 z Hz). apply Z.eqb_eq. exact H4.
Qed.

Ltac fix_amo :=
  repeat match goal with
  | |- context [amo_aligned ?w ?a] =>
      replace (amo_aligned w a) with true by (symmetry; apply amo_al4; [lia | Z.div_mod_to_equations; lia])
  end;
  rewrite ?Z.eqb_refl; cbv beta iota delta [negb].

Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_cbv; simp_is_x0; simp_regs; vnorm_tail; fix_amo; exec_cbv; simp_regs; vnorm_tail;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_tail; mem_after_store_opt ]
      end
    end
  end.

Ltac is_zlit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac fold_x32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_zlit z;
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_zlit z;
      let v := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
      replace (zx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
