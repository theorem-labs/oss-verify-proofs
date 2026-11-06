(* reac-pw/fuzz_link, PLAIN build: the memory-FILE output path, closed.

   The walks of the path prove their contracts (lib/Prog/<f>_c.v) one by one; here the chain is closed:
   __fseeko_unlocked from mwrite and mseek, rewind from __fseeko_unlocked. fmemopen (SR form) keeps the
   frame's own premises (the allocator pins, malloc's contract, libc_no_locks, AllocExtra), which the frame
   instance discharges for every allocator-facing walk of link (fmemopen.v `fmemopen_w_holds`).
   a Theorem Labs lane's obligation (b): every store of these functions lies in its contract's write list or its stack
   frame, and both miss g_say (0x75530): `*_writes_avoid_g_say` below, from each contract's premises. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require
  mwrite_c mseek_c fseeko_c rewind_c vfprintf_c fprintf_c
  mwrite mseek fseeko rewind vfprintf fprintf fmemopen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Theorem pf_mwrite : mwrite_c.mwrite_contract.
Proof. exact mwrite.mwrite_proof. Qed.

Theorem pf_mseek : mseek_c.mseek_set_contract.
Proof. exact mseek.mseek_set_proof. Qed.

Theorem pf_fseeko : fseeko_c.fseeko0_contract.
Proof. exact (fseeko.fseeko0_proof pf_mwrite pf_mseek). Qed.

Theorem pf_rewind : rewind_c.rewind_contract.
Proof. exact (rewind.rewind_proof pf_fseeko). Qed.

Theorem pf_vfprintf : vfprintf_c.vfprintf_contract.
Proof. exact vfprintf.vfprintf_proof. Qed.

Theorem pf_fprintf : fprintf_c.fprintf_contract.
Proof. exact fprintf.fprintf_proof_closed. Qed.

(* obligation (b): a stack frame above the image misses g_say *)
Lemma frame_avoids_g_say : forall s K, IMG_TOP <= s - K -> avoids_g_say [(s - K, s)].
Proof. intros s K H. avoids_split; unfold IMG_TOP, A_G_SAY in *; lia. Qed.

Lemma avoids_g_say_app : forall W1 W2, avoids_g_say W1 -> avoids_g_say W2 -> avoids_g_say (W1 ++ W2).
Proof. intros W1 W2 H1 H2. unfold avoids_g_say in *. apply Forall_app. split; assumption. Qed.

(* the write set of each leaf / leaf_fp call (its frame, then its Wr list) misses g_say whenever the
   premises its contract states hold *)
Lemma mwrite_writes_avoid_g_say : forall f regs m,
  mf_place_ok f -> errno_ok regs m MWRITE_K f -> IMG_TOP <= spZ regs - MWRITE_K ->
  avoids_g_say ((spZ regs - MWRITE_K, spZ regs) :: [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)]).
Proof.
  intros f regs m Hp He Hs. apply (avoids_g_say_app [_] _); [exact (frame_avoids_g_say _ _ Hs)|].
  exact (mwrite_c.mwrite_avoids_g_say f regs m Hp He).
Qed.

Lemma mseek_writes_avoid_g_say : forall f regs,
  mf_place_ok f -> IMG_TOP <= spZ regs - MSEEK_K ->
  avoids_g_say ((spZ regs - MSEEK_K, spZ regs) :: [(f + MemFile.MF_COOKIE, f + MemFile.MF_COOKIE + 8)]).
Proof.
  intros f regs Hp Hs. apply (avoids_g_say_app [_] _); [exact (frame_avoids_g_say _ _ Hs)|].
  avoids_split; unfold mf_place_ok, IMG_LO, IMG_TOP, A_G_SAY, MemFile.MF_COOKIE, MemFile.MF_BLOCK in *; lia.
Qed.

Lemma fseeko_writes_avoid_g_say : forall f regs m,
  mf_place_ok f -> errno_ok regs m FSEEKO_K f -> IMG_TOP <= spZ regs - FSEEKO_K ->
  avoids_g_say ((spZ regs - FSEEKO_K, spZ regs) :: [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)]).
Proof.
  intros f regs m Hp He Hs. apply (avoids_g_say_app [_] _); [exact (frame_avoids_g_say _ _ Hs)|].
  exact (fseeko_c.fseeko0_avoids_g_say f regs m Hp He).
Qed.

Lemma rewind_writes_avoid_g_say : forall f regs m,
  mf_place_ok f -> errno_ok regs m REWIND_K f -> IMG_TOP <= spZ regs - REWIND_K ->
  avoids_g_say ((spZ regs - REWIND_K, spZ regs) :: [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)]).
Proof.
  intros f regs m Hp He Hs. apply (avoids_g_say_app [_] _); [exact (frame_avoids_g_say _ _ Hs)|].
  exact (rewind_c.rewind_avoids_g_say f regs m Hp He).
Qed.

Lemma vfprintf_writes_avoid_g_say : forall f s K, mf_place_ok f -> IMG_TOP <= s - K ->
  avoids_g_say ((s - K, s) :: [mf_block f]).
Proof.
  intros f s K Hp Hs. apply (avoids_g_say_app [_] _); [exact (frame_avoids_g_say _ _ Hs)|].
  exact (vfprintf_c.vfprintf_avoids_g_say f Hp).
Qed.
