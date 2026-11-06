(* reac-pw/fuzz_link, PLAIN build: small tactics the walks of __fseeko_unlocked and rewind share.
   - `getr_simp`: read a register of a concrete map (an `mkR` or its tree) in the goal;
   - `regs_pres`: the callee-saved registers of two concrete maps agree (`regs_preserved`);
   - `hold`: a fact the walk tactics must not carry across a store (they would drop it); the walk moves it
     itself at the end. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK11.
Local Open Scope Z_scope.

Definition hold (P : Prop) : Prop := P.

Ltac getr_simp :=
  repeat match goal with
  | |- context [getr ?R ?r] =>
      is_concrete_map R;
      let b := eval vm_compute in (bv_eqb r (Z_to_bv 5 0)) in
      lazymatch b with false => change (getr R r) with (reg_get R r) end
  | |- context [YK11.getr ?R ?r] =>
      is_concrete_map R;
      let b := eval vm_compute in (bv_eqb r (Z_to_bv 5 0)) in
      lazymatch b with false => change (YK11.getr R r) with (reg_get R r) end
  end; simp_regs.

Ltac regs_pres :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|];
  assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
