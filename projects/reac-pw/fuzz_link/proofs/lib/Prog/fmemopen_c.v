(* fmemopen (musl src/stdio/fmemopen.c; plain 0x192a0, 464 bytes) as the harness calls it:
   fmemopen(g_said, 4096, "w") (fuzz_link.c:156; mark_quietly 0x15db0..0x15dc4).

   It mallocs the 1304-byte block (+0x94), zeroes its first 272 bytes (+0xbc memset), fills the cookie
   (buf = g_said, size = 4096, mode = 'w') and the FILE (buf = block + 280, buf_size = 1024, fd = -1,
   lbf = EOF, flags = F_NORD for "w" without '+', read / write / seek / close = mread / mwrite / mseek /
   mclose), sets lock = -1 because __libc.threaded is 0 (+0x18c..+0x1a8; a Theorem Labs lane's obligation (a):
   `stdio_ok` carries that byte, __libc + 1, as 0), and tail-calls __ofl_add (+0x1cc), which makes the
   FILE the head of the open-file list. Mode "w" reads nothing of g_said and writes nothing there.
   The released walk of the same code (libreac/fuzz_pcap lib/Prog/fmemopen*.v) states mode "rb"; this
   contract is the "w" arm, and its post is lib/MemFile.v's FILE (`memfile_k`, `mf_dyn`).
   K = 8240 (48 of its own, then malloc's ALLOC_STACK of 8192). The block it returns is the one
   `mark_quietly` keeps in g_sink; the writes are the block and the list head only. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require link_spec link_mem memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Import ListNotations.
Local Open Scope Z_scope.

(* the mode string "w" in .rodata (MemFile.link_mf_mode_bytes) *)
Definition A_MODE_W : Z := 0x10564.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition fmemopen_w_writes (h : Z) (a : Z) : Prop :=
  A_OFL_HEAD <= a < A_OFL_HEAD + 8 \/ h <= a < h + MemFile.MF_BLOCK.

Definition fmemopen_w_contract : Prop :=
  forall L A regs mem md (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR memfile_c.FMEMOPEN_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 link_mem.A_G_SAID -> getr regs 11 = Z_to_bv 64 link_spec.SAID_SIZE ->
    getr regs 12 = Z_to_bv 64 A_MODE_W ->
    wr_at rsegs mem link_mem.A_G_SAID link_spec.SAID_SIZE ->
    stdio_ok mem -> ofl_empty mem -> guard_ok mem -> ro_agree segs mem ->
    res_ok_slots A b0 -> room_slots b0 MemFile.MF_BLOCK ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 memfile_c.FMEMOPEN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' h,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR memfile_c.FMEMOPEN_K L A regs mem md (fmemopen_w_writes h) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 h /\ h <> 0 /\ h mod 16 = 0 /\ fresh_block B h MemFile.MF_BLOCK /\
         (exists b1 b2, blocks L' A' = b1 ++ (h, MemFile.MF_BLOCK) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
         st_init_done A' = true /\ (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b0 MemFile.MF_BLOCK) /\
         memfile_c.memfile_k mem' h 0 /\
         memfile_c.mf_dyn mem' h MemFile.F_NORD 0 0 0 0 0 0 /\
         ofl_one mem' h /\ stdio_ok mem' /\ guard_ok mem' /\ ro_agree segs mem').

End K.

(* a Theorem Labs lane's obligation (b) for fmemopen: its writes miss g_say *)
Lemma fmemopen_w_avoids_g_say : forall h a, memfile_c.mf_place_ok h -> fmemopen_w_writes h a ->
  ~ (link_mem.A_G_SAY <= a < link_mem.A_G_SAY + 8).
Proof.
  intros h a Hp [Ha | Ha]; unfold memfile_c.mf_place_ok, memfile_c.IMG_LO, memfile_c.IMG_TOP, A_OFL_HEAD,
    link_mem.A_G_SAY, MemFile.MF_BLOCK in *; lia.
Qed.
