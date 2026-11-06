(* remember (reac_served_mark.c:38-47): keep the name of an interface this run marked, once, at
   most 32 of them.

   a0 = m, a1 = ifname. It searches the names already kept by strcmp, and on a miss writes the
   name into the next 16-byte slot with snprintf, which stores the first 15 bytes and a NUL.
   Nothing is written once 32 names are kept. link_spec`s `remember` is the whole of it, and
   model_remember (fuzz_link.c:433-440) is the same function, which is what makes check_marks
   never fire.
   This contract uses the leaf_fp shape because snprintf runs the printf layer: printf_core leaves
   fa0 free and promises only that the rounding mode is still 0, so the contract gives the same
   freedom (the form of the released snprintf contract, lib/Prog/printf_facts_c.v printf_post).
   K = 6400 (48 of its own, then snprintf`s 6352, which is the whole printf chain including the
   float arm that link`s formats never take).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c.
Local Open Scope Z_scope.

Definition REMEMBER : Z := 0x166b4.
Lemma REMEMBER_is_entry : REMEMBER = P_remember. Proof. reflexivity. Qed.

Definition remember_contract : Prop :=
  leaf_fp REMEMBER 6400
    (fun regs m => exists gbs nm,
       marks_at m (arg regs 0) gbs /\ marks_wf gbs
       /\ arg regs 1 <> 0 /\ cstr_at m (arg regs 1) nm
       /\ (length nm <= 15)%nat
       /\ cstr_at m A_FMT_S (map (Z_to_bv 8) [37; 115])
       /\ (arg regs 1 + Z.of_nat (length nm) + 8 <= arg regs 0
           \/ arg regs 0 + MK_SIZE <= arg regs 1)
       /\ pf_img_free (arg regs 0) MK_SIZE
       /\ (exists slack, bytes_at rsegs m (arg regs 1 + Z.of_nat (length nm) + 1) slack
             /\ Z.of_nat (length slack) = (- (arg regs 1 + Z.of_nat (length nm) + 1)) mod 8)
       /\ apart_frame regs 6400 (arg regs 0) MK_SIZE
       /\ apart_frame regs 6400 (arg regs 1) (Z.of_nat (length nm) + 8))
    (fun regs m => [(arg regs 0, arg regs 0 + MK_SIZE)])
    (fun regs m regs' m' => forall gbs nm,
       marks_at m (arg regs 0) gbs -> cstr_at m (arg regs 1) nm ->
       exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs'
       /\ mk_names gbs' = remember (mk_names gbs) nm
       /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm))).
