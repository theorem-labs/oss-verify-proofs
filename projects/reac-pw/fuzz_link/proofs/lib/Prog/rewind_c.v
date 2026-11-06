(* rewind (musl src/stdio/rewind.c; plain 0x19bc4, 144 bytes) on link's memory FILE: what mark_quietly does
   before every mark (fuzz_link.c:162).

   a0 = f. lock = -1 (fmemopen's, __libc.threaded = 0) so +0x18 skips __lockfile; it calls
   __fseeko_unlocked(f, 0, SEEK_SET) (+0x6c) and then clears F_ERR (+0x70..+0x78). So the k pending
   bytes go to g_said at the cookie's pos (all of them when they fit before its end, else up to the
   end), the window is empty, and pos is 0 when they fit (else it stays at g_said's end); the flags
   are F_NORD again either way.
   K = 160 (32 of its own, then __fseeko_unlocked's 128). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition rewind_contract : Prop :=
  forall (f k fl om wend wpos wbase pos len : Z) (pb : list byte),
  leaf REWIND REWIND_K
    (fun regs m =>
       arg regs 0 = f /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       apart_frame regs REWIND_K f MemFile.MF_BLOCK /\ apart_frame regs REWIND_K A_G_SAID SAID_SIZE /\
       errno_ok regs m REWIND_K f /\ IMG_TOP <= spZ regs - REWIND_K /\ guard_words m)
    (fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' =>
       let n1 := mf_n1 k pos in
       memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
       bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
       mf_dyn m' f MemFile.F_NORD om 0 0 0 (if n1 <? k then pos + n1 else 0) (Z.max len (pos + n1))).

Lemma rewind_avoids_g_say : forall f regs m, mf_place_ok f -> errno_ok regs m REWIND_K f ->
  avoids_g_say [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)].
Proof.
  intros f regs m Hp (_ & _ & _ & _ & He).
  avoids_split; unfold mf_hdr, mf_said in *; cbn [fst snd];
    unfold mf_place_ok, rapart, IMG_LO, IMG_TOP, A_G_SAY, A_G_SAID, SAID_SIZE, MemFile.MF_BLOCK, MemFile.MF_ZEROED in *;
    lia.
Qed.
