(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the contracts of the functions rewind(f) reaches on
   link's memory FILE, below the wrapper's arewind_mf_realizes (LinkMfDefs.v section 3).

   Every contract here has the form of arewind_mf_realizes and of the frame's runtime-wrapper contracts (Reusable/YG0d.v
   aintrin_realizes): ecall_pre, a stack window of K present bytes below sp, the return to ra with AR kept at the same
   ly S W, the callee-saved registers kept, every byte outside the window and the written set kept, presence kept.
   They are the A twins of the plain lib/Prog/mseek_c.v, mwrite_c.v, fseeko_c.v and rewind_c.v (all in this unit): the
   same cases, the same post, over LinkMfDefs.v's FILE words (amf_k, amf_dyn, amf_pend, azbytes, amf_n1, amf_buf_ok).
   Listings of image A: link-a/listings/runtime/{mseek,mwrite,__fseeko_unlocked,rewind,wrapper_rewind}.fuzz_link.asan.s
   (internal records, sha256 9d30009753d4, 0f1962ed05d4, db254527920b, 08b36455316c and 7dd0e084a483). The
   definitions take any segs, B and MS; they are true at link's image and FILE: segs = tfibsegs, a B with PcapSyms
   B (as_code B = Tfib_code makes 0x52d74 the runtime's memcpy entry; as_errno B = as_tp B - 164 puts mwrite's
   ENOSPC store in the excepted errno range) and MS = link_amf (its mode 119 decides mwrite +0x64; its write / seek
   entries decide __fseeko_unlocked's two jalr). The walks take exactly these.

   1. amseek_set_realizes: mseek 0x96dd4 (frame 48) at whence = SEEK_SET.
      +0x0c..+0x1c  s0 = *LA_GOT_GUARD; 0x18(sp) = *s0; +0x70..+0x78 the re-check   -> the two guard premises
      +0x20 bgeu a2,3 (not taken)                                                    -> a2 = 0
      +0x24 ld a3,0x98(a0): the cookie                                               -> the word at f + 152 is f + 232
      +0x28 / +0x2c ld c->pos, c->len (stored to base[1], base[2]; not used)         -> the words at f + 232, f + 240
      +0x48 a0 = base[0] = 0; +0x50 blt a1,-0 (not taken); +0x54 ld c->size;
      +0x5c bge size - 0, a1 (taken)                                                 -> 0 <= off <= size < 2^63, the
                                                                                        word at f + 248 is the size
      +0x90 sd a0,0(a3): c->pos = off                                                -> the FILE block is live (its
                                                                                        bytes writable, not the
                                                                                        runtime's, off the window)
      returns off. K = 48: its frame; the EINVAL arm (+0x60 ___errno_location) and __stack_chk_fail (+0x98) are not
      reached, and K <= ESTACK, so ecall_pre's window covers it.

   2. amwrite_mf_at K kmax: mwrite 0x96cc0 (frame 48), a0 = f, a1 = x, a2 = n.
      +0x24 / +0x28 ld wpos, wbase; +0x34 beq                    -> amf_k, amf_dyn: k = wpos - wbase pending bytes
      +0x2c ld s4,0x98(f): the cookie                            -> amemfile_at (cookie pointer, size, buf, mode
                                                                    amf_mode MS)
      k > 0: +0x3c sd f->wpos = wbase; +0x4c jal mwrite(f, wbase, k), one frame lower (sp - 48): the k = 0 instance
             (amwrite_mf_k0_realizes) on the pending bytes [f + 280, f + 280 + k) (amf_pend);
             +0x50 bgeu a0,k, else return 0 (+0x54)
      +0x5c lw c->mode; +0x64 bne 'a' (taken)                    -> amemfile_at fixes the mode to amf_mode MS, 'w'
                                                                    (119) at link_amf
      +0x74..+0x80 s3 = size - pos; bgeu s3,n                    -> amf_dyn: pos <= len <= size
      n > size - pos: +0x84 jal ___errno_location (0x90a7c: a0 = tp - 164 = as_errno B); +0x8c sw errno = ENOSPC;
             +0x90..+0x98 flags |= F_ERR; +0x9c..+0xa4 wend = wpos = wbase = 0; n2 = size - pos
      +0xc0 jal 0x52d74 = pc_wrap_memcpy (c->buf + pos, x, n2): the AsanAPI's aa_memcpy_icpt (aintrin_realizes OCpy,
             window ESTACK)                                      -> the destination [buf + pos, + n2) lies in g_said:
                                                                    amf_buf_ok K; the source [x, x + n): azbytes,
                                                                    0 <= x, x + n <= 2^63, amem_range,
                                                                    range_addressable, shadow_hull_vis, and apart
                                                                    from g_said (the copy's destination), from the
                                                                    FILE's first 272 bytes and errno (stored before
                                                                    the copy reads them) and from the window
      +0xc4..+0xd0 pos += n2; +0xd4 bgeu old len, pos: when the old len < pos, +0xdc len = pos and, when also
      pos < size, +0xe0..+0xec buf[pos] = 0 (in g_said); so len becomes max len pos
      returns n2. Window: one frame of 48 when k = 0, two when k > 0 (the inner call), then the copy's ESTACK.
      amwrite_mf_k0_realizes = amwrite_mf_at (48 + ESTACK) 0; amwrite_mf_realizes = amwrite_mf_at (96 + ESTACK) 1024.
      The inner call is not an instance of amwrite_mf_realizes (its window is 48 bytes lower): the walk proves the
      k = 0 contract first and applies it there, as the plain mwrite.v does (mw_k0 / mw_gen).

   3. amwrite_mf_flush_realizes: f->write(f, 0, 0), the call of __fseeko_unlocked +0x70 and of close_file at exit
      (AMemFileT06.v): amwrite_mf_realizes at x = 0, n = 0, its post read at n = 0 (it returns 0; the n1 pending
      bytes are at g_said + pos; F_ERR and the empty window when n1 < k, else wpos = wbase).

   4. afseeko0_mf_realizes: __fseeko_unlocked 0x96e78 (frame 32) at off = 0, whence = SEEK_SET.
      +0x18 bltu a2,3 (taken); +0x34 bne a2,1 (taken)            -> a2 = 0 (a1 = 0: the off mseek gets)
      +0x4c / +0x50 ld wpos, wbase; +0x54 beq                    -> amf_k, amf_dyn
      wpos <> wbase: +0x58 ld a3,0x48(f); +0x70 jalr a3          -> amemfile_at: f->write = amf_write MS = LA_MWRITE
             (la_mf_entries): amwrite_mf_flush_realizes at sp - 32 (window K - 32 = 96 + ESTACK);
             +0x7c / +0x80 ld wpos; beqz: return -1 (n1 < k: the flush passed g_said's end)
      +0x84 ld a3,0x50(f); +0x88..+0x90 wend = wpos = wbase = 0; +0x98 jalr a3
                                                                 -> amemfile_at: f->seek = LA_MSEEK:
                                                                    amseek_set_realizes (off 0) at sp - 32; the guard
                                                                    premises
      +0x9c bltz (not taken); +0xa4..+0xac flags &= ~F_EOF (F_NORD and F_NORD|F_ERR have no F_EOF: amemfile_flags);
      +0xb0 / +0xb4 rpos = rend = 0 (already 0: amemfile_window); returns 0. K = 32 + 96 + ESTACK.

   5. musl rewind 0x97210 (frame 32) and ___interceptor_rewind 0x48ce8 (frame 16) are stated by LinkMfDefs.v's
      arewind_mf_realizes itself, at LA_REWIND and at LA_I_REWIND (the same premises, the same window ARW_STK =
      160 + ESTACK; the wrapper's trampoline LA_W_REWIND is the statement's own entry):
      rewind: +0x14 lw lock (f + 140 holds -1: amemfile_static); +0x18 bltz (taken) -> +0x60;
             +0x6c jal __fseeko_unlocked(f, 0, 0): afseeko0_mf_realizes at sp - 32; +0x70..+0x78 flags &= ~F_ERR.
      ___interceptor_rewind: +0x10 jal TryAsanInitFromRtl 0x5b214 (frame 16; asan_inited 0xab118 = 1, a cell of
             AR's const table, so it returns at +0x30); +0x14 / +0x18 ld t1 from LA_REAL_REWIND 0xa37d8, which AR's
             const law fixes to LA_REWIND 0x97210 (lib/A/AF0m.v row z8 (ANum 0xa37d8) 0x97210); +0x20..+0x28 pops
             its frame; +0x2c jr t1: musl rewind's contract at the caller's sp. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the windows *)
Definition AMS_STK : Z := 48.
Definition AMW0_STK : Z := 48 + ESTACK.
Definition AMW_STK : Z := 96 + ESTACK.
Definition AFS_STK : Z := 128 + ESTACK.

(* what one mwrite call leaves (mwrite_c.v mw_pos1 / mw_n2): the n1 = amf_n1 k pos pending bytes go first; if they
   all fit, n2 = min n (size - pos1) data bytes follow *)
Definition amw_pos1 (MS : amemfile_syms) (k pos : Z) : Z := pos + amf_n1 MS k pos.
Definition amw_n2 (MS : amemfile_syms) (k pos n : Z) : Z := Z.min n (amf_size MS - amw_pos1 MS k pos).

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* 1. mseek(f, off, SEEK_SET) *)
Definition amseek_set_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md (f off pos len : Z),
  ecall_pre segs B ly S W regs mem md ->
  getr regs 10 = w64 f -> getr regs 11 = w64 off -> getr regs 12 = w64 0 ->
  0 <= off <= amf_size MS -> amf_size MS < 2 ^ 63 ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  val_mem segs (rd W mem) (f + 152) 8 (f + AMF_COOKIE) ->
  val_mem segs (rd W mem) (f + AMF_COOKIE) 8 pos ->
  val_mem segs (rd W mem) (f + AMF_COOKIE + 8) 8 len ->
  val_mem segs (rd W mem) (f + AMF_COOKIE + 16) 8 (amf_size MS) ->
  rdword (aview segs (w_H W) mem) LA_GOT_GUARD = Some LA_GUARD ->
  (exists g, rdword (aview segs (w_H W) mem) LA_GUARD = Some g) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 off /\
       val_mem segs (rd W mem') (f + AMF_COOKIE) 8 off /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AMS_STK <= a < spZ regs) ->
          ~ (f + AMF_COOKIE <= a < f + AMF_COOKIE + 8) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - AMS_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* 2. mwrite(f, x, n) with k <= kmax pending bytes, window K *)
Definition amwrite_mf_at (K kmax pc : Z) : Prop :=
  forall ly S W regs mem md (f k fl om wend wpos wbase pos len x : Z) (pb ds : list Z),
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + K <= spZ regs ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 x -> getr regs 12 = w64 (Z.of_nat (length ds)) ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  amf_k segs MS (rd W mem) f k -> k <= kmax ->
  amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
  amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok segs B MS K ly S W regs mem ->
  azbytes segs (rd W mem) x ds -> 0 <= x -> x + Z.of_nat (length ds) <= 2 ^ 63 ->
  amem_range x (Z.of_nat (length ds)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ds)) ->
  (0 < Z.of_nat (length ds) -> shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length ds))) ->
  (forall a, x <= a < x + Z.of_nat (length ds) ->
     ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) /\ ~ (f <= a < f + AMF_ZEROED) /\
     ~ (as_errno B <= a < as_errno B + 4) /\ ~ (spZ regs - K <= a < spZ regs)) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       let n := Z.of_nat (length ds) in
       let n1 := amf_n1 MS k pos in
       let pos1 := amw_pos1 MS k pos in
       let n2 := amw_n2 MS k pos n in
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       amf_k segs MS (rd W mem') f 0 /\ amf_pend segs (rd W mem') f pb /\
       (n1 < k ->
          getr regs' 10 = w64 0 /\
          amf_dyn segs MS (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 pos1 (Z.max len pos1) /\
          azbytes segs (rd W mem') (amf_buf MS + pos) (firstn (Z.to_nat n1) pb)) /\
       (n1 = k ->
          getr regs' 10 = w64 n2 /\
          (exists fl' wend' wpos' wbase',
             amf_dyn segs MS (rd W mem') f fl' om wend' wpos' wbase' (pos1 + n2) (Z.max len (pos1 + n2)) /\
             (n2 < n -> fl' = Z.lor fl AF_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
             (n2 = n -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase)) /\
          azbytes segs (rd W mem') (amf_buf MS + pos) (pb ++ firstn (Z.to_nat n2) ds)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem' a)).

Definition amwrite_mf_k0_realizes (pc : Z) : Prop := amwrite_mf_at AMW0_STK 0 pc.
Definition amwrite_mf_realizes (pc : Z) : Prop := amwrite_mf_at AMW_STK AMF_BUFSIZ pc.

(* 3. the flush f->write(f, 0, 0) *)
Definition amwrite_mf_flush_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md (f k fl om wend wpos wbase pos len : Z) (pb : list Z),
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + AMW_STK <= spZ regs ->
  (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 0 -> getr regs 12 = w64 0 ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  amf_k segs MS (rd W mem) f k ->
  amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
  amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok segs B MS AMW_STK ly S W regs mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       let n1 := amf_n1 MS k pos in
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 0 /\
       amf_k segs MS (rd W mem') f 0 /\ amf_pend segs (rd W mem') f pb /\
       azbytes segs (rd W mem') (amf_buf MS + pos) (firstn (Z.to_nat n1) pb) /\
       (n1 < k -> amf_dyn segs MS (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
       (n1 = k -> amf_dyn segs MS (rd W mem') f fl om wend wbase wbase (pos + k) (Z.max len (pos + k))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AMW_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* 4. __fseeko_unlocked(f, 0, SEEK_SET) *)
Definition afseeko0_mf_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md (f k fl om wend wpos wbase pos len : Z) (pb : list Z),
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + AFS_STK <= spZ regs ->
  (forall a, spZ regs - AFS_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 0 -> getr regs 12 = w64 0 ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  amf_k segs MS (rd W mem) f k ->
  amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
  amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok segs B MS AFS_STK ly S W regs mem ->
  rdword (aview segs (w_H W) mem) LA_GOT_GUARD = Some LA_GUARD ->
  (exists g, rdword (aview segs (w_H W) mem) LA_GUARD = Some g) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       let n1 := amf_n1 MS k pos in
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       amf_k segs MS (rd W mem') f 0 /\ amf_pend segs (rd W mem') f pb /\
       azbytes segs (rd W mem') (amf_buf MS + pos) (firstn (Z.to_nat n1) pb) /\
       (n1 < k ->
          getr regs' 10 = w64 (-1) /\
          amf_dyn segs MS (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
       (n1 = k ->
          getr regs' 10 = w64 0 /\
          amf_dyn segs MS (rd W mem') f fl om 0 0 0 0 (Z.max len (pos + k))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AFS_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - AFS_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* A callee's window lies inside its caller's, at the caller's sp minus the callee's frame, so the caller's
   amf_buf_ok hands the callee the one it needs: only the window clause mentions the registers. *)
Lemma amf_buf_ok_sub : forall (K K' : Z) ly S W regs regs' mem,
  spZ regs - K <= spZ regs' - K' -> spZ regs' <= spZ regs ->
  amf_buf_ok segs B MS K ly S W regs mem -> amf_buf_ok segs B MS K' ly S W regs' mem.
Proof.
  intros K K' ly S W regs regs' mem Hlo Hhi (H0 & H1 & H2 & Hw & Hr & Hra & Hhull).
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  split; [| split; [exact Hr | split; [exact Hra | exact Hhull]]].
  intros a Ha. destruct (Hw a Ha) as (Hwa & Hoa & Hsa).
  split; [exact Hwa|]. split; [exact Hoa|]. intros Hin. apply Hsa. lia.
Qed.

End s.

(* the windows nest: rewind's frame (32) on __fseeko_unlocked's window, its frame (32) on mwrite's, mwrite's frame (48)
   on the k = 0 call's *)
Lemma arw_windows : ARW_STK = 32 + AFS_STK /\ AFS_STK = 32 + AMW_STK /\ AMW_STK = 48 + AMW0_STK /\
  AMS_STK <= AMW_STK /\ AMW0_STK = 48 + ESTACK.
Proof. unfold ARW_STK, AFS_STK, AMW_STK, AMW0_STK, AMS_STK, ESTACK. repeat split; lia. Qed.
