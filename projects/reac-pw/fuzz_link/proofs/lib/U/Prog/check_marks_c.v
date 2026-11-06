(* check_marks (fuzz_link.c:608-623), UBSAN build: the marks kept are the interfaces this daemon
   marked, each once, in the model order.

   The twin of lib/Prog/check_marks_c.v, with its premises, its Post, and the premises the UBSan
   guards below need. a0 = got, a pointer to struct reac_served_marks; a1 = m, a pointer to struct
   model. The body is `if (got->n != m->n_mark) abort(); for i < n: if (strcmp(got->name[i],
   m->mark[i])) abort();`. Claims (h) and (i) of the halting theorem. Each strcmp needs a NUL inside
   its 16-byte slot, which `marks_wf` and `model_marks_wf` give. K = 64 (own frame of 64; strcmp
   uses no stack). The Post is `only_frame`: the prologue stores ra and s0-s6 into [sp-64, sp)
   and nothing restores those bytes; `leaf` already says only that window changed.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/check_marks.s); every guard
   branches to the `unimp` at 0x1655c:
   - branch 0x164c8 (fuzz_link.c:646, `andi a2, a0, 3` at +0x24): traps unless `got` is 4-aligned.
     ADDED: `arg regs 0 mod 4 = 0`.
   - branch 0x164d0 (fuzz_link.c:646, `andi a2, a1, 7` at +0x2c): traps unless `m` is 8-aligned.
     ADDED: `arg regs 1 mod 8 = 0`.
   - branch 0x16514 (fuzz_link.c:649, `beq s0, s6` with s6 = 0x210): traps when the loop reaches
     i = 33. ANSWERED BY THE PLAIN PREMISES: marks_wf gives got->n <= 32, so i <= 31.
   - branch 0x16510 (`bltu s3, s0`): traps when got + 4 + 16i passes 2^64 - 1; branch 0x16518
     (`bltu s5, s0`): traps when m + 8340 + 16i passes 2^64 - 1. ANSWERED BY THE PLAIN PREMISES:
     marks_at and model_at are u8arr blocks, so bytes_at gives got + MK_SIZE <= 2^64 and
     m + MD_SIZE <= 2^64, and both sums stay inside their blocks for i <= 31.
   - the `unimp` at 0x16564 follows the call to abort and is reached only through it.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_MARKS : Z := 0x164a0.
Lemma CHECK_MARKS_is_entry : CHECK_MARKS = P_check_marks. Proof. reflexivity. Qed.

Definition check_marks_contract : Prop :=
  leaf CHECK_MARKS 64
    (fun regs m => exists gbs mbs,
       marks_at m (arg regs 0) gbs /\ model_at m (arg regs 1) mbs
       /\ marks_wf gbs /\ model_marks_wf mbs /\ marks_are gbs mbs
       /\ apart_frame regs 64 (arg regs 0) MK_SIZE
       /\ apart_frame regs 64 (arg regs 1) MD_SIZE
       /\ arg regs 0 mod 4 = 0 /\ arg regs 1 mod 8 = 0)
    writes_nothing
    only_frame.
