(* reac-pw/fuzz_link, PLAIN build: link's memory FILE as the contracts of its output path see it.

   The harness opens one FILE, `fmemopen(g_said, 4096, "w")` (fuzz_link.c:150-164), rewinds it before
   every mark, and the library writes its lines on it with fprintf / vfprintf (reac_served_mark.c,
   reac_code.h). lib/MemFile.v states that FILE for the frame (`memfile_at`). This file adds what the
   contracts of fmemopen, mwrite, mseek, __fseeko_unlocked, rewind, vfprintf and fprintf (one file each,
   `lib/Prog/<f>_c.v`) and their callers (reac_code_emit, reac_served_mark, mark_quietly) share:
   - `mf_win m f k`: the buffer window, with k bytes pending (0 when the window is empty);
   - `memfile_k m f k`: the FILE at f, k bytes pending, its block and g_said writable, and the block
     outside the image's address range;
   - `mf_dyn`: the seven FILE words the path changes (flags, orientation, wend, wpos, wbase, and the
     cookie's pos and len); every other byte `memfile_at` reads stays as fmemopen wrote it;
   - the entry and the stack bound K of each function of the path (plain image).
   Every address and K below was read from the image the proofs load (the unstripped twin of the pin
   ebe34b259b9f; link/pf/dis/plain/*.s and link/ct/stack.json). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Entries and stack bounds (plain image)
   ========================================================================== *)

Definition FMEMOPEN : Z := 0x192a0.
Definition MWRITE : Z := 0x19544.
Definition MSEEK : Z := 0x19658.
Definition FSEEKO : Z := 0x19c54.     (* __fseeko_unlocked *)
Definition REWIND : Z := 0x19bc4.
Definition FPRINTF : Z := 0x196fc.
Definition VFPRINTF : Z := 0x19ff4.

(* the FILE's function pointers are these entries (fmemopen +0x168..+0x19c, MemFile.link_mf) *)
Lemma mf_entries : MemFile.mf_write MemFile.link_mf = MWRITE /\ MemFile.mf_seek MemFile.link_mf = MSEEK.
Proof. split; reflexivity. Qed.

(* K: the function's own frame plus the deepest frame of every callee on the path its contract covers.
   mwrite calls itself once (the flush, +0x4c) and memcpy (no frame); __fseeko_unlocked (32) calls
   mwrite through f->write (+0x70) and mseek through f->seek (+0x98); rewind (32) calls
   __fseeko_unlocked; fmemopen (48) reaches malloc, whose bound is the frame's ALLOC_STACK (8192);
   fprintf (80) and vfprintf (368) reach printf_core (link/ct/stack.json, all static callees). *)
Definition MWRITE_K : Z := 96.
Definition MSEEK_K : Z := 48.
Definition FSEEKO_K : Z := 128.
Definition REWIND_K : Z := 160.
Definition FMEMOPEN_K : Z := 8240.
Definition VFPRINTF_K : Z := 5968.
Definition FPRINTF_K : Z := 6048.

(* the image's address range: its first page and the page after its last byte (0x960e0) *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_TOP : Z := 0x97000.

(* .rodata, where every format link prints lies (the first PT_LOAD, 0x10000..0x11eb4) *)
Definition RO_LO : Z := 0x10000.
Definition RO_END : Z := 0x11eb4.

(* the stack protector: the GOT slot and the guard word it names *)
Definition GOT_GUARD : Z := 0x208d8.
Definition GUARD : Z := 0x95878.

(* errno values the path stores *)
Definition E_NOSPC : Z := 28.

(* ==========================================================================
   2. The FILE
   ========================================================================== *)

(* a field of the FILE block, in MemFile.v's form *)
Definition mf_fld (m : word -> option byte) (f off : Z) (n : nat) (v : Z) : Prop :=
  YI04.val_mem rsegs m (f + off) n v.

(* The buffer window. Empty: wend = wpos = wbase = 0 (after fmemopen, rewind, or a write past g_said's
   end), and then k = 0. Active (after __towrite): wbase = buf, wend = buf + 1024, wpos = buf + k. *)
Definition mf_win (m : word -> option byte) (f k : Z) : Prop :=
  (k = 0 /\ mf_fld m f 32 8 0 /\ mf_fld m f 40 8 0 /\ mf_fld m f 56 8 0) \/
  (0 <= k <= MemFile.MF_BUFSIZ /\
   mf_fld m f 32 8 (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ) /\
   mf_fld m f 40 8 (f + MemFile.MF_BUF + k) /\
   mf_fld m f 56 8 (f + MemFile.MF_BUF)).

(* Where the block may lie: wholly below the image or wholly above it. malloc's `fresh_block` gives
   4096 <= f and no byte in the image; lib/Prog/memfile_place.v (`mf_place_of_fresh`) turns that into
   this, from the image's reserved segments, which cover [IMG_LO, IMG_TOP) without a gap. *)
Definition mf_place_ok (f : Z) : Prop :=
  f + MemFile.MF_BLOCK <= IMG_LO \/ IMG_TOP <= f.

(* The one predicate the path and its callers share: link's memory FILE at f with k bytes pending,
   its 1304-byte block and g_said writable, and the block outside the image. *)
Definition memfile_k (m : word -> option byte) (f k : Z) : Prop :=
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f /\ mf_win m f k /\
  wr_at rsegs m f MemFile.MF_BLOCK /\ wr_at rsegs m A_G_SAID SAID_SIZE /\ mf_place_ok f.

(* The seven words the path changes: flags (+0), orientation (+136), wend (+32), wpos (+40),
   wbase (+56), and the cookie's pos (+232) and len (+240). *)
Definition mf_dyn (m : word -> option byte) (f fl om wend wpos wbase pos len : Z) : Prop :=
  (* the values as the code reads them (val_mem stores each one mod 2^32 / 2^64), PfMwrite 10:0xZ *)
  0 <= fl < 2 ^ 32 /\ 0 <= om < 2 ^ 32 /\ 0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64 /\
  0 <= pos <= len /\ len <= SAID_SIZE /\
  mf_fld m f 0 4 fl /\ mf_fld m f 136 4 om /\ mf_fld m f 32 8 wend /\ mf_fld m f 40 8 wpos /\
  mf_fld m f 56 8 wbase /\ mf_fld m f MemFile.MF_COOKIE 8 pos /\ mf_fld m f (MemFile.MF_COOKIE + 8) 8 len.

(* the k pending bytes, at the start of the buffer *)
Definition mf_pend_bytes (m : word -> option byte) (f : Z) (pb : list byte) : Prop :=
  bytes_at rsegs m (f + MemFile.MF_BUF) pb.

(* the bytes of the FILE block the path writes: the first 272 (FILE and cookie) and the buffer *)
Definition mf_hdr (f : Z) : ivl := (f, f + MemFile.MF_ZEROED).
Definition mf_block (f : Z) : ivl := (f, f + MemFile.MF_BLOCK).
Definition mf_said : ivl := (A_G_SAID, A_G_SAID + SAID_SIZE).

(* g_say (reac_served_mark.c:14, plain 0x75530): a Theorem Labs lane's obligation (b) is that only the harness's
   say_to store (0x163fc) writes it. Each contract of the path writes inside its `Wr` list only; a
   list that `avoids_g_say` shows the obligation for that function. *)
Definition avoids_g_say (W : list ivl) : Prop :=
  Forall (fun iv => snd iv <= A_G_SAY \/ A_G_SAY + 8 <= fst iv) W.

(* two byte ranges apart *)
Definition rapart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

(* errno (tp - 164, link_mem `errno_at`) as the path writes it: 4 writable bytes, outside the callee's
   frame, the FILE block, g_said, the GOT slot of the stack protector (writable in rsegs; mseek reads it
   after mwrite may have stored errno, PfRewind 10:2xZ) and g_say *)
Definition errno_ok (regs : bvmap 5 word) (m : word -> option byte) (K f : Z) : Prop :=
  wr_at rsegs m (errno_at regs) 4 /\ apart_frame regs K (errno_at regs) 4 /\
  rapart (errno_at regs) 4 f MemFile.MF_BLOCK /\ rapart (errno_at regs) 4 A_G_SAID SAID_SIZE /\
  rapart (errno_at regs) 4 GOT_GUARD 8 /\ rapart (errno_at regs) 4 A_G_SAY 8.

(* the stack protector's two words, as mseek, fprintf and vfprintf read them *)
Definition guard_words (m : word -> option byte) : Prop :=
  bytes_at rsegs m GOT_GUARD (le8 (wz GUARD)) /\ exists g : word, bytes_at rsegs m GUARD (le8 g).

(* A flush of k pending bytes at the cookie's pos (mwrite's inner call, +0x4c) stores n1 of them:
   all k when they fit before g_said's end, else up to the end (and then sets F_ERR). *)
Definition mf_n1 (k pos : Z) : Z := Z.min k (SAID_SIZE - pos).

(* ==========================================================================
   3. Facts every user needs
   ========================================================================== *)

(* split an `avoids_g_say` goal into one arithmetic goal per range *)
Ltac avoids_split := unfold avoids_g_say; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].

Lemma mf_said_avoids_g_say : avoids_g_say [mf_said].
Proof. avoids_split; unfold mf_said, A_G_SAID, SAID_SIZE, A_G_SAY; cbn [fst snd]; lia. Qed.

Lemma mf_block_avoids_g_say : forall f, mf_place_ok f -> avoids_g_say [mf_block f; mf_hdr f].
Proof.
  intros f H. avoids_split; unfold mf_block, mf_hdr in *; cbn [fst snd];
    unfold mf_place_ok, IMG_LO, IMG_TOP, A_G_SAY, MemFile.MF_BLOCK, MemFile.MF_ZEROED in *; lia.
Qed.

Lemma memfile_k_at : forall m f k, memfile_k m f k -> MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m f.
Proof. intros m f k (H & _). exact H. Qed.

Lemma memfile_k_place : forall m f k, memfile_k m f k -> mf_place_ok f.
Proof. intros m f k (_ & _ & _ & _ & H). exact H. Qed.

Lemma memfile_k_range : forall m f k, memfile_k m f k -> 0 <= k <= MemFile.MF_BUFSIZ.
Proof.
  intros m f k (_ & [(-> & _) | (H & _)] & _); [unfold MemFile.MF_BUFSIZ; lia | exact H].
Qed.
