(* remember (reac_served_mark.c:38-47), UBSAN build: keep the name of an interface this run marked,
   once, at most 32 of them.

   The twin of lib/Prog/remember_c.v, with its premises, its Post, and the premise the UBSan
   guards below need. a0 = m, a1 = ifname. It searches the names already kept by strcmp, and on a
   miss stores n + 1 into m->n and writes the name into slot n with snprintf, which stores the
   first 15 bytes and a NUL. Nothing is written once 32 names are kept. link_spec`s `remember` is
   the whole of it. This contract uses the leaf_fp shape because snprintf runs the printf layer,
   as in the plain twin.
   K = 6432 (80 of its own, then snprintf`s 6352). SURPRISE OF THE BINARY: the ubsan build calls
   snprintf as a TAIL CALL (+0x114, `j` after the epilogue has popped the 80-byte frame), so
   snprintf runs at the entry sp and the true depth is max(80, 6352) = 6352; 6432 is the measured
   bound and is kept, because it is also true.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/remember.s); every guard branches
   to the `unimp` at 0x16f74:
   - branch 0x16e8c (reac_served_mark.c:40, `andi a0, a0, 3` before the read of m->n): traps
     unless m is 4-aligned. ADDED: `arg regs 0 mod 4 = 0`.
   - branch 0x16eb8 (reac_served_mark.c:41, `not s6, s4; bltu s6, s5` with s4 = m + 4 and
     s5 = 16 i): traps when m->name[i] passes 2^64 - 1. ANSWERED BY THE PLAIN PREMISES:
     marks_wf gives i < m->n <= 32, so the sum is below m + MK_SIZE, and marks_at`s u8arr gives
     m + MK_SIZE <= 2^64.
   - branch 0x16f20 (reac_served_mark.c:45, `beqz a0` with a0 = m + 4 + 16 n): traps when
     m->name[n] is NULL, and branch 0x16f34 (the same line, `sltu; slti; xor; xori; beqz`): traps
     when the sum wrapped against the sign of n. Both run only when n <= 31 (`bge 31, n` at
     +0x84). ANSWERED BY THE PLAIN PREMISES: n >= 0 (marks_wf) and 4 <= m + 4 + 16 n < m + MK_SIZE
     <= 2^64 (marks_at), so the sum neither wraps nor is 0.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import printf_facts_c.
Local Open Scope Z_scope.

Definition REMEMBER : Z := 0x16e5c.
Lemma REMEMBER_is_entry : REMEMBER = P_remember. Proof. reflexivity. Qed.

Definition remember_contract : Prop :=
  leaf_fp REMEMBER 6432
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
       /\ apart_frame regs 6432 (arg regs 0) MK_SIZE
       /\ apart_frame regs 6432 (arg regs 1) (Z.of_nat (length nm) + 8)
       /\ arg regs 0 mod 4 = 0)
    (fun regs m => [(arg regs 0, arg regs 0 + MK_SIZE)])
    (fun regs m regs' m' => forall gbs nm,
       marks_at m (arg regs 0) gbs -> cstr_at m (arg regs 1) nm ->
       exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs'
       /\ mk_names gbs' = remember (mk_names gbs) nm
       /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm))).
