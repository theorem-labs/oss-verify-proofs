(* name_of (projects/reac-pw/fuzz_link/source/fuzz_link.c:102-110, with fuzz_u8 of
   projects/reac-pw/fuzz_link/source/fuzz.h:37-43 inlined): the harness takes one byte of its input
   and names an interface with it. UBSAN BUILD ONLY: the plain build inlines name_of into
   LLVMFuzzerTestOneInput, so it has no plain twin.

   a0 = in, a struct fuzz_in: the cursor p at +0 and the count n at +8, two 8-byte fields. When
   n = 0 the byte is 0, nothing is written, and the answer is g_names[0]. Otherwise the cursor
   becomes (p + 1, n - 1) and s is the byte at p: the answer is NULL for s = 255, g_names[s] =
   A_G_NAMES + 8 * s for s < 64, and else the pointer the table odd holds at entry s mod 6.
   THE POST IS THE REAL VALUE: the agreement reads the name both sides receive.

   The UBSan guards (link/donors/ubsan-checks.tsv, name_of, 1 trap at 0x14400, 4 guard branches),
   and the premise that answers each:
   - 0x14350 (fuzz.h:39, `andi a1, a0, 7` then bnez): the cursor is 8-aligned. Premise
     `arg regs 0 mod 8 = 0`.
   - 0x14370 (fuzz.h:42, the pointer-overflow test of `in->p++`, `bgeu 1, p + 1`): p is not 0 and
     p + 1 does not wrap. Premise `0 < p` and `p + 1 < 2 ^ 64`, needed only when n is not 0.
   - 0x143ac (fuzz_link.c:108, g_names + 8 * s does not wrap) and 0x143f0 (fuzz_link.c:109,
     odd + 8 * (s mod 6) does not wrap): both bases are constants of the image and the offsets are
     at most 504, so these hold with no premise.
   The other premises are what a provable statement needs, not guards: the cursor is readable and
   writable; the byte at p is readable and is not inside the cursor (n and p are stored before
   that byte is read); the six odd entries are readable (odd lies in .data.rel.ro, which the
   image loads in a segment marked read-write) and the cursor is not inside them, so the answer
   can be stated over the memory at entry.
   K = 0 (frame 0, no call: link/donors/premises-ubsan.txt).
   Entry read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NAME_OF : Z := 0x1434c.
Lemma NAME_OF_is_entry : NAME_OF = P_name_of. Proof. reflexivity. Qed.

Definition name_of_contract : Prop :=
  leaf NAME_OF 0
    (fun regs m => exists wp wn : word,
       rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn]
       /\ arg regs 0 mod 8 = 0
       /\ (arg regs 0 + 16 <= A_ODD \/ A_ODD + 48 <= arg regs 0)
       /\ (forall i, 0 <= i < 6 -> exists v, u64_at m (A_ODD + 8 * i) v)
       /\ (bv_unsigned wn <> 0 ->
             0 < bv_unsigned wp /\ bv_unsigned wp + 1 < 2 ^ 64
             /\ (bv_unsigned wp + 1 <= arg regs 0 \/ arg regs 0 + 16 <= bv_unsigned wp)
             /\ exists s, bytes_at rsegs m (bv_unsigned wp) [s]))
    (fun regs m => [(arg regs 0, arg regs 0 + 16)])
    (fun regs m regs' m' => forall wp wn : word,
       rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn] ->
       (bv_unsigned wn = 0 -> m' = m /\ res regs' = A_G_NAMES)
       /\ (bv_unsigned wn <> 0 ->
             rw_cells rsegs m' (arg regs 0)
               [C8 (wz (bv_unsigned wp + 1)); C8 (wz (bv_unsigned wn - 1))]
             /\ forall s, bytes_at rsegs m (bv_unsigned wp) [s] ->
                  (bz s = 255 -> res regs' = 0)
                  /\ (bz s < 64 -> res regs' = A_G_NAMES + 8 * bz s)
                  /\ (64 <= bz s < 255 -> u64_at m (A_ODD + 8 * (bz s mod 6)) (res regs')))).
