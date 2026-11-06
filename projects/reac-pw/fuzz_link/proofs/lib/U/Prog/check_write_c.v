(* check_write (fuzz_link.c:568-577) and check_mark (:595-606), UBSAN build: the code the call
   answered is the code the model owes, under the harness own comparison same_rc (:471-475).

   The twin of lib/Prog/check_write_c.v, with the same premise and the same Post. The two functions
   are byte-identical in the ubsan build too (link/ct/dis/ubsan/check_write.s and check_mark.s
   differ only in the pc-relative offset of the call to abort), so there is ONE contract here and
   it is instantiated at each entry. The body is `if (!same_rc(rc, want)) abort();`, compiled as:
   `want == 1000000` ? `rc == 0` : `rc != want`, on the whole registers. The contract says the
   abort is NOT taken. Claims (f) and (h) of the halting theorem; the caller gets the premise from
   link_spec write_agree / mark_agree. The returning path uses no stack (the 16-byte frame is pushed
   only on the abort path, +0x24), so K = 0.
   UBSan guards: link/donors/ubsan-checks.tsv gives neither function a guard branch. Each has one
   `unimp` (0x163e8, 0x1649c) after its call to abort, reached only through it, so no premise is
   added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_WRITE : Z := 0x163b8.
Lemma CHECK_WRITE_is_entry : CHECK_WRITE = P_check_write. Proof. reflexivity. Qed.

Definition CHECK_MARK : Z := 0x1646c.
Lemma CHECK_MARK_is_entry : CHECK_MARK = P_check_mark. Proof. reflexivity. Qed.

(* the register-level reading of same_rc(got, want) = 1 *)
Definition same_rc_regs (regs : bvmap 5 word) : Prop :=
  (getr regs 11 = wz RC_FAILS -> getr regs 10 <> wz 0)
  /\ (getr regs 11 <> wz RC_FAILS -> getr regs 10 = getr regs 11).

Definition check_rc_contract (pc : Z) : Prop :=
  leaf pc 0 (fun regs m => same_rc_regs regs) writes_nothing unchanged.

Definition check_write_contract : Prop := check_rc_contract CHECK_WRITE.
Definition check_mark_contract : Prop := check_rc_contract CHECK_MARK.
