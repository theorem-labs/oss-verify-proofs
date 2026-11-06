(* attr_text (fuzz_link.c:168-172): the harness puts one attribute holding a text into the reply it
   is building.

   a0 = w (a struct nl_w), a1 = type, a2 = s, a3 = bare. It is
   `nl_attr_put(w, type, s, strlen(s) + !bare)`, which writes a 4-byte header, the text and the
   NL_ALIGN padding into w->b, and raises w->full when the 4096 bytes are full.
   THE WEAKEST FORM THE CALLER NEEDS: plain_halts does not need to know WHICH reply bytes
   msg_build makes. Both readers walk the same chunk, whatever it holds, so the agreement does not
   depend on the grammar of the reply. The contract therefore says only that the writer stays a
   writer: it touches no byte outside the structure, its length never passes 4096, and it never
   shrinks. This is NOT the strongest true statement; a lane that later wants the reply`s shape can
   strengthen the Post without touching the premises. K = 64 (own frame; strlen, memcpy and memset
   use no stack). In the UBSan build attr_text is inlined into kernel and has no contract.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition ATTR_TEXT : Z := 0x1534c.
Lemma ATTR_TEXT_is_entry : ATTR_TEXT = P_attr_text. Proof. reflexivity. Qed.

Definition attr_text_contract : Prop :=
  leaf ATTR_TEXT 64
    (fun regs m => exists bs s,
       nlw_at m (arg regs 0) bs /\ nlw_wf bs
       /\ arg regs 2 <> 0 /\ cstr_at m (arg regs 2) s
       /\ (exists slack, bytes_at rsegs m (arg regs 2 + Z.of_nat (length s) + 1) slack
             /\ (- (arg regs 2 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))
       /\ (arg regs 0 + NW_SIZE <= arg regs 2 \/ arg regs 2 + Z.of_nat (length s) + 1 <= arg regs 0)
       /\ apart_frame regs 64 (arg regs 0) NW_SIZE
       /\ apart_frame regs 64 (arg regs 2) (Z.of_nat (length s) + 1))
    (fun regs m => [(arg regs 0, arg regs 0 + NW_SIZE)])
    (fun regs m regs' m' => forall bs, nlw_at m (arg regs 0) bs ->
       exists bs', nlw_at m' (arg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').
