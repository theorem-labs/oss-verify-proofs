(* fprintf (musl src/stdio/fprintf.c; plain 0x196fc, 100 bytes) on link's memory FILE.

   a0 = f, a1 = fmt, a2..a7 = the arguments. It saves a2..a7 in its frame at sp+0x20..+0x48 (+0xc..+0x28),
   points the va_list at sp+0x20 (+0x3c) and calls vfprintf (+0x40); the stack protector reads the guard
   through the GOT (+0x14..+0x34). So its contract is vfprintf's with the slots in a2..a7.
   K = 6048 (80 of its own, then vfprintf's 5968). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c vfprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition fprintf_contract : Prop :=
  forall (f k fl om wend wpos wbase pos len : Z) (pb : list byte)
         (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z),
  leaf_fp FPRINTF FPRINTF_K
    (fun regs m =>
       arg regs 0 = f /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       bytes_at rsegs m (arg regs 1) (pf_bytes (fmt ++ [0])) /\
       RO_LO <= arg regs 1 /\ arg regs 1 + Z.of_nat (length fmt) + 1 <= RO_END /\
       pf_parse fmt = Some ps /\ pf_text ps args = Some T /\
       pf_args_ok m (spZ regs) (spZ regs - FPRINTF_K) f MemFile.MF_BLOCK
         [getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args /\
       k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ /\
       f + MemFile.MF_BLOCK <= spZ regs - FPRINTF_K /\ IMG_TOP <= spZ regs - FPRINTF_K /\
       guard_words m)
    (fun regs m => [mf_block f])
    (fun regs m regs' m' =>
       res regs' = Z.of_nat (length T) /\ pf_file_post m' f k pb T fl om wend pos len).
