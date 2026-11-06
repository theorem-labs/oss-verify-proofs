(* mwrite (musl src/stdio/fmemopen.c; plain 0x19544, 276 bytes): the write function of link's memory FILE.

   a0 = f, a1 = buf, a2 = len. When k = wpos - wbase bytes are pending, mwrite first sets wpos = wbase
   and calls itself on them (+0x3c, +0x4c): the k bytes go to g_said at the cookie's pos. When that
   inner call stores fewer than k (they pass g_said's end), it returns 0 at once (+0x54). Otherwise it
   stores up to len bytes of buf at the new pos. A store that passes g_said's end (len > size - pos,
   +0x80) sets errno = ENOSPC, F_ERR and wend = wpos = wbase = 0 (+0x84..+0xa4), then still stores the
   bytes that fit (+0xac). pos moves by the bytes stored; len rises to pos, with a NUL after it while
   it is below the size (+0xc4..+0xec). Mode 'a' (+0x5c) is not link's ('w', cookie +32 = 119).
   Callers: __fseeko_unlocked's flush, f->write(f, 0, 0) (+0x70), which rewind reaches before every
   mark; close_file at exit (MemFileT06.v). The general buf / len form is stated. The inner call is NOT
   an instance of this contract (its K window is 48 bytes lower): a walk proves the no-flush case
   (k = 0, one frame of 48) first and uses it there (PfContractReview 10:2xZ).
   K = 96: two frames of 48 (the one recursive call; memcpy and ___errno_location push none). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Lemma MWRITE_is_entry : MemFile.mf_write MemFile.link_mf = MWRITE. Proof. reflexivity. Qed.

(* What one call leaves, from k pending bytes pb, the cookie's pos / len, and n data bytes:
   n1 = mf_n1 k pos of the pending bytes are stored (0 when k = 0); if n1 < k the call stops there;
   else n2 = min n (size - pos1) data bytes follow. *)
Definition mw_pos1 (k pos : Z) : Z := pos + mf_n1 k pos.
Definition mw_n2 (k pos n : Z) : Z := Z.min n (SAID_SIZE - mw_pos1 k pos).

Definition mwrite_contract : Prop :=
  forall (f k fl om wend wpos wbase pos len : Z) (pb ds : list byte),
  leaf MWRITE MWRITE_K
    (fun regs m =>
       arg regs 0 = f /\ arg regs 2 = Z.of_nat (length ds) /\
       memfile_k m f k /\ mf_dyn m f fl om wend wpos wbase pos len /\
       mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k /\
       bytes_at rsegs m (arg regs 1) ds /\
       rapart (arg regs 1) (Z.of_nat (length ds)) A_G_SAID SAID_SIZE /\
       (* the data is read after the header stores and errno's store (PfContractReview 10:2xZ) *)
       rapart (arg regs 1) (Z.of_nat (length ds)) f MemFile.MF_ZEROED /\
       rapart (errno_at regs) 4 (arg regs 1) (Z.of_nat (length ds)) /\
       apart_frame regs MWRITE_K (arg regs 1) (Z.of_nat (length ds)) /\
       apart_frame regs MWRITE_K f MemFile.MF_BLOCK /\ apart_frame regs MWRITE_K A_G_SAID SAID_SIZE /\
       IMG_TOP <= spZ regs - MWRITE_K /\
       errno_ok regs m MWRITE_K f)
    (fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' =>
       let n1 := mf_n1 k pos in
       let pos1 := mw_pos1 k pos in
       let n2 := mw_n2 k pos (Z.of_nat (length ds)) in
       memfile_k m' f 0 /\
       mf_pend_bytes m' f pb /\
       (n1 < k ->
          res regs' = 0 /\
          mf_dyn m' f (Z.lor fl MemFile.F_ERR) om 0 0 0 pos1 (Z.max len pos1) /\
          bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb)) /\
       (n1 = k ->
          res regs' = n2 /\
          exists fl' wend' wpos' wbase',
            mf_dyn m' f fl' om wend' wpos' wbase' (pos1 + n2) (Z.max len (pos1 + n2)) /\
            (n2 < Z.of_nat (length ds) -> fl' = Z.lor fl MemFile.F_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
            (n2 = Z.of_nat (length ds) -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase) /\
            bytes_at rsegs m' (A_G_SAID + pos) (pb ++ firstn (Z.to_nat n2) ds))).

(* the flush form __fseeko_unlocked and close_file use: f->write(f, 0, 0) *)
Lemma mwrite_avoids_g_say : forall f regs m, mf_place_ok f -> errno_ok regs m MWRITE_K f ->
  avoids_g_say [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)].
Proof.
  intros f regs m Hp (_ & _ & _ & _ & He).
  avoids_split; unfold mf_hdr, mf_said in *; cbn [fst snd];
    unfold mf_place_ok, rapart, IMG_LO, IMG_TOP, A_G_SAY, A_G_SAID, SAID_SIZE, MemFile.MF_BLOCK, MemFile.MF_ZEROED in *;
    lia.
Qed.
