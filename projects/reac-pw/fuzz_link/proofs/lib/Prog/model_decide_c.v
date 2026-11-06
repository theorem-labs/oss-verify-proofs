(* model_decide (fuzz_link.c:423-431) and reac_served_decide (reac_served_mark.c:26-36): the verdict
   on an interface, from its alias and then its link kind.

   The two functions are byte-identical in both builds (link/donors/REPORT.md section 5), so there is
   ONE contract here and it is instantiated at each entry. a0 = kind, a1 = alias; either may be
   NULL. The answer is the enum of reac_served_mark.h:39-44, which link_spec`s `decide` spells.
   The function reads the two .rodata strings "reac-pw:" and "vlan" and calls strncmp and strcmp,
   neither of which uses the stack, so K = 16 (its own frame).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition MODEL_DECIDE : Z := 0x15eac.
Lemma MODEL_DECIDE_is_entry : MODEL_DECIDE = P_model_decide. Proof. reflexivity. Qed.

Definition REAC_SERVED_DECIDE : Z := 0x16404.
Lemma REAC_SERVED_DECIDE_is_entry : REAC_SERVED_DECIDE = P_reac_served_decide.
Proof. reflexivity. Qed.

Definition decide_contract (pc : Z) : Prop :=
  leaf pc 16
    (fun regs m => exists k a,
       str_arg m (arg regs 0) k /\ str_arg m (arg regs 1) a /\
       (forall t, k = Some t -> apart_frame regs 16 (arg regs 0) (Z.of_nat (length t) + 1)) /\
       (forall t, a = Some t -> apart_frame regs 16 (arg regs 1) (Z.of_nat (length t) + 1)) /\
       cstr_at m A_PREFIX S_PREFIX /\ cstr_at m A_VLAN S_VLAN)
    writes_nothing
    (fun regs m regs' m' =>
       forall k a, str_arg m (arg regs 0) k -> str_arg m (arg regs 1) a ->
         getr regs' 10 = wz (decide k a)).

Definition model_decide_contract : Prop := decide_contract MODEL_DECIDE.
Definition reac_served_decide_contract : Prop := decide_contract REAC_SERVED_DECIDE.
