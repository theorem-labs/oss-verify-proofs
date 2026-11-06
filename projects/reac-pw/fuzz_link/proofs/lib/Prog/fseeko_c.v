(* __fseeko_unlocked (musl src/stdio/fseek.c; plain 0x19c54, 216 bytes) at off 0, SEEK_SET, on link's
   memory FILE: the call rewind makes (+0x30 / +0x6c).

   a0 = f, a1 = off, a2 = whence. whence < 3 (+0x18) and not SEEK_CUR (+0x34). When wpos <> wbase
   (+0x54) it flushes through f->write(f, 0, 0) (+0x70: mwrite) and returns -1 if wpos is then 0
   (+0x80: the flush passed g_said's end). Otherwise it zeroes wend / wpos / wbase (+0x88..+0x90),
   calls f->seek(f, off, whence) (+0x98: mseek), and on a non-negative answer clears F_EOF and zeroes
   rpos / rend (+0xa4..+0xb4) and returns 0.
   K = 128 (32 of its own, then mwrite's 96). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition fseeko0_contract : Prop :=
  forall (f k fl om wend wpos wbase pos len : Z) (pb : list byte),
  leaf FSEEKO FSEEKO_K
    (fun regs m =>
       arg regs 0 = f /\ arg regs 1 = 0 /\ arg regs 2 = 0 /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       apart_frame regs FSEEKO_K f MemFile.MF_BLOCK /\ apart_frame regs FSEEKO_K A_G_SAID SAID_SIZE /\
       errno_ok regs m FSEEKO_K f /\ IMG_TOP <= spZ regs - FSEEKO_K /\ guard_words m)
    (fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' =>
       let n1 := mf_n1 k pos in
       memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
       bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
       (n1 < k ->
          getr regs' 10 = wz (-1) /\
          mf_dyn m' f (Z.lor fl MemFile.F_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
       (n1 = k ->
          getr regs' 10 = wz 0 /\
          mf_dyn m' f fl om 0 0 0 0 (Z.max len (pos + k)))).

Lemma fseeko0_avoids_g_say : forall f regs m, mf_place_ok f -> errno_ok regs m FSEEKO_K f ->
  avoids_g_say [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)].
Proof.
  intros f regs m Hp (_ & _ & _ & _ & He).
  avoids_split; unfold mf_hdr, mf_said in *; cbn [fst snd];
    unfold mf_place_ok, rapart, IMG_LO, IMG_TOP, A_G_SAY, A_G_SAID, SAID_SIZE, MemFile.MF_BLOCK, MemFile.MF_ZEROED in *;
    lia.
Qed.
