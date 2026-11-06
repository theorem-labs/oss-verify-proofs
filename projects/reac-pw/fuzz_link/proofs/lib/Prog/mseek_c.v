(* mseek (musl src/stdio/fmemopen.c; plain 0x19658, 156 bytes): the seek function of link's memory FILE,
   at whence SEEK_SET.

   a0 = f, a1 = off, a2 = whence. It reads the cookie c = f->cookie (+0x24), builds base[] = {0, c->pos,
   c->len} in its frame (+0x34..+0x3c), takes base[whence] (+0x48), and when -base <= off <= c->size -
   base (+0x50..+0x5c) stores c->pos = base + off (+0x90) and returns it; else errno = EINVAL and -1.
   At SEEK_SET base is 0. __fseeko_unlocked calls it through f->seek (+0x98) with the off and whence
   rewind gives, 0 and SEEK_SET. The stack protector reads the guard through the GOT (+0xc..+0x1c).
   K = 48 (its own frame; ___errno_location, on the refused arm only, pushes none). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Lemma MSEEK_is_entry : MemFile.mf_seek MemFile.link_mf = MSEEK. Proof. reflexivity. Qed.

Definition mseek_set_contract : Prop :=
  forall (f off pos len : Z),
  leaf MSEEK MSEEK_K
    (fun regs m =>
       arg regs 0 = f /\ arg regs 1 = off /\ arg regs 2 = 0 /\ 0 <= off <= SAID_SIZE /\
       0 < f /\ f + MemFile.MF_BLOCK <= 2 ^ 64 /\
       mf_fld m f 152 8 (f + MemFile.MF_COOKIE) /\
       mf_fld m f MemFile.MF_COOKIE 8 pos /\ mf_fld m f (MemFile.MF_COOKIE + 8) 8 len /\
       mf_fld m f (MemFile.MF_COOKIE + 16) 8 SAID_SIZE /\
       wr_at rsegs m (f + MemFile.MF_COOKIE) 8 /\
       apart_frame regs MSEEK_K f MemFile.MF_BLOCK /\
       IMG_TOP <= spZ regs - MSEEK_K /\ mf_place_ok f /\   (* frame and cookie clear of the guard word *)
       guard_words m)
    (fun regs m => [(f + MemFile.MF_COOKIE, f + MemFile.MF_COOKIE + 8)])
    (fun regs m regs' m' =>
       res regs' = off /\ mf_fld m' f MemFile.MF_COOKIE 8 off).
