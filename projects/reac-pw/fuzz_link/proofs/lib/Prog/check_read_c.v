(* check_read (fuzz_link.c:533-552): a read answered the reply`s code, and on 0 the kind and the
   alias of the reply.

   a0 = rc, a1 = want, a2 = kind, a3 = want_kind, a4 = alias, a5 = want_alias.
   `if (!same_rc(rc,want) || (rc == 0 && (strcmp(kind,want_kind) || strcmp(alias,want_alias))))
   abort();`. Claim (d) of plain_halts. The two strcmp calls run only when rc == 0, but the four
   pointers are always real buffers at the one call site (op_read, fuzz_link.c:686-697), so the
   contract asks for all four strings; that keeps the premise simple and still satisfiable.
   K = 32 (own frame; strcmp uses no stack).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_READ : Z := 0x15210.
Lemma CHECK_READ_is_entry : CHECK_READ = P_check_read. Proof. reflexivity. Qed.

Definition check_read_contract : Prop :=
  leaf CHECK_READ 32
    (fun regs m => exists k k' a a',
       cstr_at m (arg regs 2) k /\ cstr_at m (arg regs 3) k' /\
       cstr_at m (arg regs 4) a /\ cstr_at m (arg regs 5) a' /\
       apart_frame regs 32 (arg regs 2) (Z.of_nat (length k) + 1) /\
       apart_frame regs 32 (arg regs 3) (Z.of_nat (length k') + 1) /\
       apart_frame regs 32 (arg regs 4) (Z.of_nat (length a) + 1) /\
       apart_frame regs 32 (arg regs 5) (Z.of_nat (length a') + 1) /\
       (getr regs 11 = wz RC_FAILS -> getr regs 10 <> wz 0) /\
       (getr regs 11 <> wz RC_FAILS -> getr regs 10 = getr regs 11) /\
       (getr regs 10 = wz 0 -> k = k' /\ a = a'))
    writes_nothing
    only_frame.
