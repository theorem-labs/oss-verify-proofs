(* vfprintf (musl src/stdio/vfprintf.c; plain 0x19ff4, 432 bytes) on link's memory FILE.

   a0 = f, a1 = fmt, a2 = ap (the va_list: the address of the next 8-byte argument slot). It runs
   printf_core once with no FILE to check the format (+0x64), skips the lock (lock = -1, +0x70),
   clears F_ERR and keeps the old bit (+0x90..+0x9c), takes the buffered arm (buf_size = 1024 <> 0,
   +0xa0), calls __towrite when the window is empty (wend = 0, +0xa4 / +0xd8: wbase = wpos = buf,
   wend = buf + 1024, orientation -1), runs printf_core on f (+0x104), and puts the old F_ERR back
   (+0x14c..+0x164). printf_core writes each piece through __fwritex. THE FIT PREMISE: the k bytes
   already pending plus the n bytes of this text fit the 1024-byte buffer (k + n <= 1024), so every
   piece is copied into the buffer and f->write (mwrite) is not called; the text then sits in the
   buffer after the k pending bytes, and the next rewind moves it to g_said.
   The format is a .rodata string `pf_parse` reads (link's formats use %s and %d only); the args are
   the 8-byte slots at ap, as printf_facts_c's `pf_args_ok` takes them (D, n = the FILE block).
   K = 5968 (368 of its own, then printf_core's 5600; link/ct/stack.json). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI14.
Local Open Scope Z_scope.

(* the n argument slots at ap: 8 bytes each, little-endian *)
Definition va_slots (m : word -> option byte) (ap : Z) (slots : list word) : Prop :=
  bytes_at rsegs m ap (flat_map le8 slots).

(* what vfprintf and fprintf leave on the FILE: the text after the pending bytes, the window active
   with k + n pending, the flags as they were, the orientation -1 when __towrite ran *)
Definition pf_file_post (m' : word -> option byte) (f k : Z) (pb : list byte) (T : list Z)
    (fl om wend pos len : Z) : Prop :=
  memfile_k m' f (k + Z.of_nat (length T)) /\
  mf_dyn m' f fl (if wend =? 0 then YI14.U32M1 else om)
    (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ) (f + MemFile.MF_BUF + k + Z.of_nat (length T))
    (f + MemFile.MF_BUF) pos len /\
  mf_pend_bytes m' f (pb ++ pf_bytes T).

Definition vfprintf_contract : Prop :=
  forall (f k fl om wend wpos wbase pos len : Z) (pb : list byte)
         (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) (slots : list word),
  leaf_fp VFPRINTF VFPRINTF_K
    (fun regs m =>
       arg regs 0 = f /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       bytes_at rsegs m (arg regs 1) (pf_bytes (fmt ++ [0])) /\
       RO_LO <= arg regs 1 /\ arg regs 1 + Z.of_nat (length fmt) + 1 <= RO_END /\
       pf_parse fmt = Some ps /\ pf_text ps args = Some T /\
       va_slots m (arg regs 2) slots /\ spZ regs <= arg regs 2 /\
       arg regs 2 + 8 * Z.of_nat (length slots) <= 2 ^ 63 /\
       pf_args_ok m (spZ regs) (spZ regs - VFPRINTF_K) f MemFile.MF_BLOCK slots args /\
       k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ /\
       f + MemFile.MF_BLOCK <= spZ regs - VFPRINTF_K /\ IMG_TOP <= spZ regs - VFPRINTF_K /\
       guard_words m)
    (fun regs m => [mf_block f])
    (fun regs m regs' m' =>
       res regs' = Z.of_nat (length T) /\ pf_file_post m' f k pb T fl om wend pos len).

Lemma vfprintf_avoids_g_say : forall f, mf_place_ok f -> avoids_g_say [mf_block f].
Proof.
  intros f Hp. avoids_split; unfold mf_block in *; cbn [fst snd];
    unfold mf_place_ok, IMG_LO, IMG_TOP, A_G_SAY, MemFile.MF_BLOCK in *; lia.
Qed.
