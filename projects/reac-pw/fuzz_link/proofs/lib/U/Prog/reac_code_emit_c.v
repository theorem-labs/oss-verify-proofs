(* reac_code_emit (reac_code.h:103-108), UBSAN build: write the daemon`s code line and then the
   caller`s format on the policy`s stream.

   The twin of lib/Prog/reac_code_emit_c.v, with the same premises and the same Post.
   a0 = f, a1 = prefix, a2 = code, a3 = fmt, a4..a7 = the varargs. As in the plain build, a1 and
   a2 are DEAD: the function always writes fprintf(f, `%s: %s `, `reac-pw`, `E_NOT_MARKED`) from
   three .rodata addresses of its own (+0x28 to +0x3c: 0x10556, 0x1051e, 0x103a8 in this image),
   and only then vfprintf(f, fmt, ap) with the four saved varargs at sp + 0x20 as the va_list.
   THE FILE, as in the plain twin (link/ct/AMEND-mark.md gaps 1 and 2): the stream is link`s one
   memory FILE, stated with lib/U/Prog/memfile_c.v`s `memfile_k m f k`, the predicate the output
   path and the three marking contracts share. The Pre bounds the pending bytes plus the 22 bytes
   of the first line and the text of the caller`s format by the 1024-byte buffer, asks the format
   to parse and the four registers a4..a7 to be its arguments, and puts the FILE block below the
   callees` windows; otherwise the call need not return, and the old Pre was false.
   K = 6112 (64 of its own, then fprintf`s 6048; vfprintf`s depth is inside fprintf`s).
   UBSan guards: link/donors/ubsan-checks.tsv gives this function no trap and no guard branch
   (link/ct/dis/ubsan/reac_code_emit.s has no `unimp`), and the libc functions it reaches are not
   instrumented, so no premise is added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require MemFile.
Local Open Scope Z_scope.

Definition REAC_CODE_EMIT : Z := 0x16de8.
Lemma REAC_CODE_EMIT_is_entry : REAC_CODE_EMIT = P_reac_code_emit. Proof. reflexivity. Qed.

(* the length of the first line, "reac-pw: E_NOT_MARKED " *)
Definition EMIT_HEAD : Z := 22.

(* the caller`s format at `fp` parses into `ps`, the four varargs registers are its `args`, and its
   text is T; the same text as the plain twin, at this build`s K *)
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
