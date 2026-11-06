(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): link's memory FILE as the image-A contracts of its
   output path see it, and the contract of rewind on it at the wrapper the harness calls.

   The A twin of lib/Prog/memfile_c.v and lib/Prog/rewind_c.v (plain): the same
   FILE layout (lib/A/AMemFileSink.v, read off the asan fmemopen in AMemFile.v link_amf_code), the same words the
   path changes, the same post. The FILE predicate is the frame's amemfile_at (AMemFileSink.v); this file adds
   - amf_win m f k: the buffer window with k bytes pending (empty: wend = wpos = wbase = 0 and k = 0; active:
     wbase = f + 280, wend = f + 280 + 1024, wpos = f + 280 + k);
   - amf_dyn: the seven words the path changes (flags +0, orientation +136, wend +32, wpos +40, wbase +56, the
     cookie's pos +232 and len +240), as values the code reads (each in range, pos <= len <= size);
   - amf_pend m f pb: the k pending bytes at the start of the buffer (f + 280), as numbers 0..255;
   - azbytes m a l: bytes l at a (g_said's contents after a flush);
   - amf_n1 k pos: how many of k pending bytes a flush at the cookie's pos stores (all when they fit before
     g_said's end, else up to it);
   - arewind_mf_realizes: rewind(f) at the wrapper's 4-byte jump (0x430d4 j 0x48ce8), in the form of the frame's
     runtime-wrapper contracts (Reusable/YG0d.v aintrin_realizes / abcmp_realizes: ecall_pre, a stack window of K
     present bytes below sp, AR kept at the same ly S W, callee-saved registers kept, every byte outside the window
     and the written set kept, presence kept).

   The path of one call (neutral listings link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST)):
   - 0x430d4 j 0x48ce8; ___interceptor_rewind 0x48ce8: frame 16, jal TryAsanInitFromRtl (0x5b214), loads
     REAL(rewind) from the cell 0xa37d8 (image value 0x97210), pops its frame and jr t1;
   - musl rewind 0x97210 (frame 32): lock = -1 (amemfile_at, +140), so no __lockfile; jal __fseeko_unlocked(f, 0, 0)
     (+0x6c); then clears F_ERR (+0x70 lwu, +0x74 andi -0x21, +0x78 sw);
   - __fseeko_unlocked 0x96e78 (frame 32): when wpos <> wbase it calls f->write(f, 0, 0) (+0x70, jalr: mwrite
     0x96cc0), and returns -1 if wpos is then 0; else it zeroes wend / wpos / wbase and calls f->seek(f, 0, 0)
     (+0x98, jalr: mseek 0x96dd4);
   - mwrite 0x96cc0 (frame 48; calls itself once on the k pending bytes, then the memcpy wrapper 0x52d74 =
     pc_wrap_memcpy, whose contract is the AsanAPI's aa_memcpy_icpt with an ESTACK window, and on a write past the
     size ___errno_location 0x90a7c); its stores are exactly AMemFileT06.v link_amwrite_stores;
   - mseek 0x96dd4 (frame 48): reads the stack guard through the .got cell LA_GOT_GUARD, stores c->pos = 0.
   So the deepest point is rewind 32 + __fseeko_unlocked 32 + mwrite 48 + mwrite 48 + the memcpy wrapper's
   ESTACK window: ARW_STK = 160 + ESTACK. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Entries of image A (the unstripped twin's .symtab; same addresses as the pin)
   ========================================================================== *)

Definition LA_W_REWIND : Z := 0x430d4.     (* __interceptor_trampoline_rewind: j 0x48ce8 *)
Definition LA_I_REWIND : Z := 0x48ce8.     (* ___interceptor_rewind, 48 B *)
Definition LA_REAL_REWIND : Z := 0xa37d8.  (* _ZN14__interception11real_rewindE: holds 0x97210 *)
Definition LA_REWIND : Z := 0x97210.       (* musl rewind, 144 B *)
Definition LA_FSEEKO : Z := 0x96e78.       (* musl __fseeko_unlocked, 216 B *)
Definition LA_MWRITE : Z := 0x96cc0.       (* musl mwrite, 276 B *)
Definition LA_MSEEK : Z := 0x96dd4.        (* musl mseek, 156 B *)
Definition LA_W_FMEMOPEN : Z := 0x430a8.   (* __interceptor_trampoline_fmemopen: j 0x48024 *)
Definition LA_I_FMEMOPEN : Z := 0x48024.   (* ___interceptor_fmemopen, 80 B *)
Definition LA_FMEMOPEN : Z := 0x96a1c.     (* musl fmemopen, 464 B *)
Definition LA_W_VFPRINTF : Z := 0x4307c.   (* __interceptor_trampoline_vfprintf: j 0x46a7c *)
Definition LA_I_VFPRINTF : Z := 0x46a7c.   (* ___interceptor_vfprintf, 180 B *)
Definition LA_W_FPRINTF : Z := 0x43084.    (* __interceptor_trampoline_fprintf: j 0x46e48 *)
Definition LA_I_FPRINTF : Z := 0x46e48.    (* ___interceptor_fprintf, 216 B *)
Definition LA_VFPRINTF : Z := 0x973e0.     (* musl vfprintf, 432 B (the cell 0xa3738) *)
Definition LA_W_SNPRINTF : Z := 0x43088.   (* __interceptor_trampoline_snprintf: j 0x46f20 *)
Definition LA_MODE_W : Z := 0x21260.       (* the string "w" mark_quietly passes (AMemFile.v link_amf_mode_bytes) *)

(* the stack protector musl reads: the .got cell and the guard object it names (twin .symtab
   __stack_chk_guard 0x651c50; mseek +0xc..+0x14 loads it through 0xa2658) *)
Definition LA_GOT_GUARD : Z := 0xa2658.
Definition LA_GUARD : Z := 0x651c50.

(* the FILE's write and seek functions are these entries (AMemFile.v link_amf) *)
Lemma la_mf_entries : amf_write link_amf = LA_MWRITE /\ amf_seek link_amf = LA_MSEEK.
Proof. split; reflexivity. Qed.

(* ==========================================================================
   2. The FILE as the path's contracts state it
   ========================================================================== *)

Section c.
Variable segs : list Segment.
Variable MS : amemfile_syms.
Local Notation fld m f off n v := (val_mem segs m (f + off) n v).

(* the byte reader over a memory (link_amem.v ard; aview segs H mem = this reader over mrestrict H mem) *)
Definition amf_rd (m : word -> option byte) : Z -> option Z := fun a => option_map (fun b => bv_unsigned b) (mbyte segs m a).

(* the buffer window, k bytes pending (memfile_c.v mf_win) *)
Definition amf_win (m : word -> option byte) (f k : Z) : Prop :=
  (k = 0 /\ fld m f 32 8 0 /\ fld m f 40 8 0 /\ fld m f 56 8 0) \/
  (0 <= k <= AMF_BUFSIZ /\
   fld m f 32 8 (f + AMF_BUF + AMF_BUFSIZ) /\ fld m f 40 8 (f + AMF_BUF + k) /\ fld m f 56 8 (f + AMF_BUF)).

(* the seven words the path changes, as values the code reads (memfile_c.v mf_dyn) *)
Definition amf_dyn (m : word -> option byte) (f fl om wend wpos wbase pos len : Z) : Prop :=
  0 <= fl < 2 ^ 32 /\ 0 <= om < 2 ^ 32 /\ 0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64 /\
  0 <= pos <= len /\ len <= amf_size MS /\
  fld m f 0 4 fl /\ fld m f 136 4 om /\ fld m f 32 8 wend /\ fld m f 40 8 wpos /\
  fld m f 56 8 wbase /\ fld m f AMF_COOKIE 8 pos /\ fld m f (AMF_COOKIE + 8) 8 len.

(* bytes l (numbers 0..255) at a *)
Definition azbytes (m : word -> option byte) (a : Z) (l : list Z) : Prop :=
  forall i, (i < length l)%nat -> amf_rd m (a + Z.of_nat i) = Some (nth i l 0).

(* the k pending bytes, at the start of the buffer (memfile_c.v mf_pend_bytes) *)
Definition amf_pend (m : word -> option byte) (f : Z) (pb : list Z) : Prop :=
  azbytes m (f + AMF_BUF) pb.

(* link's memory FILE at f with k bytes pending *)
Definition amf_k (m : word -> option byte) (f k : Z) : Prop :=
  amemfile_at segs MS m f /\ amf_win m f k.

(* how many of k pending bytes a flush at the cookie's pos stores (memfile_c.v mf_n1) *)
Definition amf_n1 (k pos : Z) : Z := Z.min k (amf_size MS - pos).

End c.

(* ==========================================================================
   3. rewind at the wrapper (rewind_c.v, image A)
   ========================================================================== *)

Definition ARW_STK : Z := 160 + ESTACK.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the cookie's buffer as mwrite's checked copy needs it: every byte writable, not the runtime's, outside the
   window; the range in application memory, addressable in the shadow map, its shadow hull readable (aintrin_realizes'
   destination premises, YG0d.v:330-331, over the whole buffer [buf, buf + size)) *)
Definition amf_buf_ok (K : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : Prop :=
  0 <= amf_buf MS /\ amf_buf MS + amf_size MS <= 2 ^ 63 /\ 0 < amf_size MS < 2 ^ 32 /\
  (forall a, amf_buf MS <= a < amf_buf MS + amf_size MS ->
     writable_at segs (rd W mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - K <= a < spZ regs)) /\
  amem_range (amf_buf MS) (amf_size MS) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (amf_buf MS) (amf_size MS) /\
  shadow_hull_vis (aview segs (w_H W) mem) (amf_buf MS) (amf_size MS).

(* rewind(f) on link's memory FILE: the k pending bytes go to g_said at the cookie's pos (all of them when they fit
   before its end, else up to the end), the window is empty, pos is 0 when they fit (else it stays at g_said's
   end), the flags are F_NORD again. The bytes it may change: its window, the FILE's first 272 bytes, g_said and
   errno (mwrite's ENOSPC arm). The cell REAL(rewind) the wrapper jumps through (0x48d00 ld t1,-0x524(a0);
   0x48d14 jr t1) is a runtime-owned .data word; at link's instance AR's const law fixes it (lib/A/AF0m.v
   Tfib_const_abs row `z8 (ANum 0xa37d8) 0x97210`), so it is no premise. *)
Definition arewind_mf_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md (f k fl om wend wpos wbase pos len : Z) (pb : list Z),
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + ARW_STK <= spZ regs ->
  (forall a, spZ regs - ARW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 f ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  amf_k segs MS (rd W mem) f k ->
  amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
  amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok ARW_STK ly S W regs mem ->
  rdword (aview segs (w_H W) mem) LA_GOT_GUARD = Some LA_GUARD ->
  (exists g, rdword (aview segs (w_H W) mem) LA_GUARD = Some g) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       amf_k segs MS (rd W mem') f 0 /\ amf_pend segs (rd W mem') f pb /\
       azbytes segs (rd W mem') (amf_buf MS + pos) (firstn (Z.to_nat (amf_n1 MS k pos)) pb) /\
       amf_dyn segs MS (rd W mem') f AF_NORD om 0 0 0
         (if amf_n1 MS k pos <? k then pos + amf_n1 MS k pos else 0) (Z.max len (pos + amf_n1 MS k pos)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ARW_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - ARW_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

End s.
