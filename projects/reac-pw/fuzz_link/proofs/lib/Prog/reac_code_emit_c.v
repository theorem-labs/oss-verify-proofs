(* reac_code_emit (reac_code.h:103-108): write the daemon`s code line and then the caller`s format
   on the policy`s stream.

   a0 = f, a1 = prefix, a2 = code, a3 = fmt, a4..a7 = the varargs.
   SURPRISE OF THE BINARY: a1 and a2 are DEAD. The compiler constant-folded the only call pattern,
   so the function always writes `fprintf(f, "%s: %s ", "reac-pw", "E_NOT_MARKED")` from three
   .rodata addresses of its own (+0x28 to +0x3c), and only then `vfprintf(f, fmt, ap)` with the
   four saved varargs at sp+0x20 as the va_list (+0x18..+0x24 store a4..a7, +0x48..+0x50 pass
   ap = sp+0x20).
   THE FILE (link/ct/AMEND-mark.md gaps 1 and 2): the stream is link's one memory FILE, stated with
   lib/Prog/memfile_c.v's `memfile_k m f k` (the FILE at f with k bytes pending in its 1024-byte
   buffer), the SAME predicate the fprintf and vfprintf contracts (lib/Prog/fprintf_c.v,
   vfprintf_c.v) state; both of those walk the `__fwritex` FIT branch only, so the Pre bounds the
   pending bytes plus all the text by the buffer: 22 bytes of the first line ("reac-pw:
   E_NOT_MARKED ", from "%s: %s " at 0x10558 with 0x10520 and 0x103a8) and the T of the caller`s
   format. The format must parse (printf_facts_c.v `pf_parse`) and the four registers a4..a7 must
   be its arguments (`pf_args_ok`, with the floor the callees need): with "%s" and an unmapped a4,
   or with a conversion that stores, the call would not return, so the old Pre was false.
   The FILE block must lie BELOW the callees' windows, as fprintf and vfprintf ask
   (`f + MF_BLOCK <= sp - K`), and the stack floor and the stack-protector words come from
   `leaf_fp`.
   Nothing in the harness reads what this writes; the Post says only how many bytes are pending.
   K = 6112 (64 of its own, then fprintf`s 6048).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition REAC_CODE_EMIT : Z := 0x16640.
Lemma REAC_CODE_EMIT_is_entry : REAC_CODE_EMIT = P_reac_code_emit. Proof. reflexivity. Qed.

(* the length of the first line, "reac-pw: E_NOT_MARKED " *)
Definition EMIT_HEAD : Z := 22.

(* the caller`s format at `fp` parses into `ps`, the four varargs registers are its `args`, and its
   text is T *)
Definition emit_fmt (m : word -> option byte) (regs : bvmap 5 word) (fp : Z)
    (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) : Prop :=
  bytes_at rsegs m fp (pf_bytes (fmt ++ [0]))
  /\ RO_LO <= fp /\ fp + Z.of_nat (length fmt) + 1 <= RO_END
  /\ pf_parse fmt = Some ps /\ pf_text ps args = Some T
  /\ pf_args_ok m (spZ regs) (spZ regs - 6112) (arg regs 0) MemFile.MF_BLOCK
       [getr regs 14; getr regs 15; getr regs 16; getr regs 17] args.

Definition reac_code_emit_contract : Prop :=
  leaf_fp REAC_CODE_EMIT 6112
    (fun regs m => exists fmt ps args T k,
       arg regs 0 <> 0 /\ arg regs 3 <> 0
       /\ emit_fmt m regs (arg regs 3) fmt ps args T
       /\ memfile_k m (arg regs 0) k
       /\ k + EMIT_HEAD + Z.of_nat (length T) <= MemFile.MF_BUFSIZ
       /\ arg regs 0 + FILE_BLOCK <= spZ regs - 6112)
    (fun regs m => [mf_block (arg regs 0)])
    (fun regs m regs' m' => forall fmt ps args T k,
       emit_fmt m regs (arg regs 3) fmt ps args T -> memfile_k m (arg regs 0) k ->
       memfile_k m' (arg regs 0) (k + EMIT_HEAD + Z.of_nat (length T))).
