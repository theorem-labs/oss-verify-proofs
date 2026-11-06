(* reac_code_emit (reac_code.h:103-108) on image A (fuzz_link.asan 0x89be4, 464 bytes; listing
   (internal path) (internal record, sha256 102ac6881148)): write the daemon's code line
   and then the caller's format on the policy's stream. a0 = f, a1 = prefix, a2 = code, a3 = fmt, a4..a7 = the
   varargs. The plain contract is lib/Prog/reac_code_emit_c.v; this file states the SAME result (the stream has
   EMIT_HEAD + |T| more bytes pending) in link_amem.v's `aleaf_fx` form (the read-set shape for a function that
   reaches the printf family: rounding mode 0 at entry, a Post at SOME fx' related to the entry's by BoxBase.v
   `fxr`, and a Pre that also sees the call's block list).

   THE IMAGE-A FILE. link's harness opens one FILE, `fmemopen(g_said, 4096, "w")` (mark_quietly 0x88410), and
   every line of the marking policy goes on it. This file states it with the frame's own predicate,
   lib/A/AMemFileSink.v `amemfile_at` at the instance lib/A/AMemFile.v `link_amf` (both of the lib/A
   frame, merged into this branch on 2026-10-30), and adds the
   window with k bytes pending, `amf_win`, whose text is lib/A/Rt/LinkMfDefs.v's
   `amf_win`. `amemfile_k m f k` is that file's
   `amf_k m f k` plus the FILE block and g_said writable. The three contracts of this slice that name a FILE
   (this one, reac_served_mark_c.v, mark_quietly_c.v) take it from here only.

   SURPRISE OF THE BINARY, unchanged from the plain build: a1 and a2 are DEAD. The compiler constant-folded the
   only call pattern, so the function always writes `fprintf(f, "%s: %s ", "reac-pw", "E_NOT_MARKED")` from three
   .rodata addresses of its own (+0x104..+0x114: 0x21640 "%s: %s ", 0x212e0 "reac-pw", 0x21660 "E_NOT_MARKED";
   bytes read from the pin with pyelftools), and only then `vfprintf(f, fmt, ap)`.

   The image-A code, in order:
     +0x00..+0x2c  push a 128-byte frame; sd zero, 0(sp); save ra, s0..s7; s0 := sp + 0x60
     +0x30  andi sp, sp, -0x20                                  (realignment: up to 16 more bytes of window)
     +0x34..+0x38  s1 := sp; s2 := a3 (fmt); s4 := a0 (the stream)
     +0x3c..+0x54  s5 := the shadow base (.got 0xa19d0 -> 0xaa438 -> base); a0 := the side-stack switch cell
                   (.got 0xa1a28 -> 0xaa440)
     +0x58..+0x64  sd a4, 0(s0); sd a5, 8(s0); sd a6, 0x10(s0); sd a7, 0x18(s0)   (the va_list's four slots, in
                   this function's OWN frame)
     +0x68..+0x74  beqz a0 -> the real-stack arm; else a0 := 0x40; jal frame_alloc_0 (0x3d914); s3 := a0
     +0x88..+0xa0  the real-stack arm (not taken under `aside_room`: AR's const law holds the switch cell at 1
                   and `aside_room Sc [(0, 1)]` makes frame_alloc_0 hand out a frame, link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2)
     +0xa4..+0x11c the frame's header words and the shadow bytes of its redzones (meta bytes -0xf, -0xe, -0xd,
                   -8), then the three .rodata addresses; `jal wrapper_fprintf` (0x43084) with
                   a0 = f, a1 = 0x21640, a2 = 0x212e0, a3 = 0x21660
     +0x120..+0x138 unpoison the first slot's shadow; ap := s0; `jal wrapper_vfprintf` (0x4307c) with
                   a0 = f, a1 = fmt, a2 = ap
     +0x13c..+0x19c re-poison, write the frame's magic word, release the class-0 frame inline (+0x174
                   `ld a0, 0x38(s3); sb zero, 0(a0)`, the flag store; the real-stack arm zeroes the shadow)
     +0x1a0..+0x1cc restore, pop, ret.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x2c and +0x58..+0x64 (inside [sp - K, sp));
     frame_alloc_0, wrapper_fprintf and wrapper_vfprintf take ecall_pre-style premises that the walk derives
     from the journal; +0x1cc ret.
   - K = 128 + 16 + 9216 = 9360: the 128-byte frame, the realignment slack of `andi sp, sp, -0x20` (link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 5), then the deepest callee window. The fprintf interceptor's window
     on link's own frame is FPI_STK = 9216 (lib/A/AE2t.v:36, AE2u, AE2v, AE2w, the relocated pcap kit), which covers musl
     vfprintf's VF_STK = 912 + 2 * ESTACK = 9104 (AE3h.v:58); frame_alloc_0's is ESTACK = 4096. The vfprintf WRAPPER has
     no released window on link (link-a/libc/table.tsv (internal record, sha256 52efb25e5b91): NEW); this contract takes
     the fprintf interceptor's 9216 for it, because its path is the fprintf path without the fprintf frame. When the
     libc slice states the vfprintf wrapper, this number is to be re-checked. The plain K (6112) does not carry over.
   - SIDE = [(0, 1)]: +0x74 takes one class-0 frame; neither fprintf nor vfprintf takes a side frame. With the
     room premise the frame address is >= 4096 and the `bnez s3` fallback arm at +0x84 is not reached.
   - the stream: `aarg regs 0 <> 0` (+0x118 passes it to fprintf), `amemfile_k m (aarg regs 0) k` (the FILE the
     printf layer walks: its static fields, its flags, its window and its cookie, its block and g_said
     writable), `k + EMIT_HEAD + |T| <= AMF_BUFSIZ` (both calls walk the `__fwritex` FIT branch only, so the
     pending bytes and all the text must fit the 1024-byte buffer; with that the flush through mwrite into
     g_said is not reached), and the block's place: `apart_frame regs K (aarg regs 0) AMF_BLOCK` (the FILE block
     outside every callee window, which fprintf and vfprintf ask as `f + MF_BLOCK <= sp - K` on the plain side),
     `amem_range`, `range_addressable` and `shadow_hull_vis` over the block (the printf layer's checked writes
     into the buffer), and `In (aarg regs 0, AMF_BLOCK) bl` over the block list `aleaf_fx` hands the Pre: the
     FILE block is a block of the allocator's ledger, which the FILE contracts ask
     (lib/A/Rt/LinkMfDefs.v: AR then gives the block's range, its separation
     from the stack and the image, and its addressable shadow). The slot gives it from the frame's
     `amf_gi_ledger` (lib/A/AMemFileSink.v).
   - the caller's format: `aemit_fmt` = the bytes at a3 are `fmt ++ [0]`, `pf_parse fmt = Some ps`, the format
     not empty and made of literal, `%d` and `%s` pieces only (the vfprintf contract's format family asks
     `fmt <> []` and `Forall pf_link_piece ps`: the closed form of lib/A/Rt/LinkPfPiece.v, from disco
     lib/A/FMsnprintfFmI.v:36-40; found by LinkWalkMark.MkEmit; both call sites meet it, .str.3 has %s and %d,
     .str.5 has %s, %s, %d, %s), `pf_text ps args = Some T`, the format is in the read-only image below the .got
     cell of the stack guard
     (0x10000 <= fp, fp + |fmt| + 1 <= 0xa2658; the GXA route proves the printf layer only for such a format,
     boxreg A/Rt/SnprintfDef.v and the relocation table of link-a/libc/printf.md
     (internal record, sha256 7bbba2c3aa7f)), its own `astr_rt_ok`, and `apf_args_ok` on a4..a7: an integer argument is
     the register modulo 2^32, a string argument is a C string with everything a `%s` conversion reads (the span
     addressable, the shadow hull visible, the 8-byte band in memory, the rest of the NUL's word visible, apart from the
     callee windows and from the FILE block). With an unmapped a4 and a `%s`, or with a conversion that stores, the call
     would not return, so these are premises of the binary and not of the source (the plain lane's gap 1).
   - the three literals of the first line: `acstr_at` and `astr_rt_ok` for 0x21640, 0x212e0, 0x21660 (+0x104,
     +0x110, +0x114 form them; the printf layer reads them and their shadow). They are image bytes, so the
     journal keeps them, but the shadow of each registered global's granules is what the interceptor's range
     check reads.
   - the write set [f, f + AMF_BLOCK) and apre's `ajw` on it: everything the two calls write is inside the FILE
     block (the buffer, the window words, the cookie). That block is granted by `in_tmp_block` only in the target
     call whose first mark opened it; on every later target call it is a block of the journal's start, and the
     grant is the frame's: the harness journal's FP is `amf_harness_fp T` (lib/A/AMemFileSink.v:231,
     `sink_token` and every kept block), and `amf_harness_fp_grants` (lib/A/AMemFile.v:535) gives `awr_byte` of
     every byte of a kept block that is live in the ledger, which `In (aarg regs 0, AMF_BLOCK) bl` says.
     g_said is NOT in the write set: with `k + EMIT_HEAD + |T| <= AMF_BUFSIZ` no flush runs, which is why the
     plain write set is `[mf_block f]` too. The function's own class-0 frame and its shadow are not in the write
     set either: the frame is taken and released inside the call, and `apost`'s `frames S2 = frames Sc` says so
     (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 2).
   - the read set Rd (`aleaf_fx`'s): the caller's format, and the string of each vararg register the format makes
     a `%s` argument (`apf_rd`: an `APtr` of `args`, and only those, because a register the format does not
     consume holds whatever the caller left, e.g. a6 and a7 at 0x89870, and may point into this function's own
     window). They are read through pointer arguments and are not in the write set, and this function runs an
     allocator-facing callee (frame_alloc_0) before the two printf calls, so the caller must place them where
     `akb` keeps them. At the two call sites of reac_served_mark they are image bytes: at 0x89870 the format
     .str.3 and the name (a g_names or `odd` string; a5 = -rc is an integer); at 0x89b9c the format .str.5, the
     name, .str.4 "reac-pw:served" and .str.6 or .str.7 (a6 = -rc is an integer).
   EV = 0: no allocator event (the printf layer below fprintf / vfprintf allocates nothing on the FIT branch).

   What does NOT carry over from the plain text:
   - the `leaf_fp` shape with the printf floor `A_IMG_TOP <= lo` and the two stack-protector words: on image A
     the floating-point freedom and the guard words are the wrapper contract's, and the stack is the journal's.
   - `memfile_k` over the plain image: restated here as `amemfile_k` at image A's addresses (above).
   - the plain `arg regs 0 + FILE_BLOCK <= spZ regs - 6112`: now `apart_frame regs K`, with K = 9360.
   Nothing of the plain Post is false of image A.
   Released proofs (rule 24): none of reac_code_emit (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038));
   the fprintf and vfprintf wrappers are NEW for link's call sites (link-a/libc/printf.md
   (internal record, sha256 7bbba2c3aa7f) section 0). THE PURE PRINTF MODEL is lib/Prog/printf_facts_c.v's (`pf_piece`,
   `pf_arg`, `pf_parse`, `pf_text`): it is image-free, like link_spec.v, and is Required here, never Imported, so none
   of that file's plain-image definitions (`pf_img_free` and `printf_post` over `rsegs`) is used.
   THE FLOATING-POINT STATE is `aleaf_fx`'s. Entry: the shape takes `YK0o.frm_zero (fp_csr fx)`, which the
   released printf-family contracts ask and the plain mark_quietly states (lib/Prog/mark_quietly_c.v:151); it
   holds at every call site, because the start-up fcsr is 0 (`fp_frm_zero_fx0`, Reusable/YK0o.v:15) and none
   of the 36 listings of link's own functions holds an f* or csr* instruction (checked over
   link-a/listings/*.fuzz_link.asan.s (36 internal records, the sha256 of each in the records MANIFEST)). Exit: `apostF`
   returns at some fx' with `BoxBase.fxr fx fx'` (every f register but f10 kept, the fcsr kept or its rounding mode 0),
   which is what fprintf and vfprintf leave (pcap's fprintf kit AE2t..AE2w, the printf family's shared post).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0o YI04 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem model_decide_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_CODE_EMIT_A : Z := 0x89be4.
Lemma REAC_CODE_EMIT_A_is_entry : REAC_CODE_EMIT_A = LA_reac_code_emit. Proof. reflexivity. Qed.

(* ==========================================================================
   1. Image A's addresses this file needs (they belong in lib/A/Prog/link_aaddr.v; they are here until the lane
      that owns that file adds them). All from the unstripped twin's .symtab and the listings.
   ========================================================================== *)

(* the FILE's four function pointers and its cookie's buf, size and mode are the frame's `link_amf`
   (lib/A/AMemFile.v): mread 0x96bec, mwrite 0x96cc0, mseek 0x96dd4, mclose 0x96e70, g_said, 4096, 'w' *)
Lemma link_amf_globals : amf_sink_addr link_amf = LA_G_SINK /\ amf_say_addr link_amf = LA_G_SAY /\
  amf_buf link_amf = LA_G_SAID /\ amf_size link_amf = SAID_SIZE /\ amf_ofl_head link_amf = LA_OFL_HEAD.
Proof. repeat split; reflexivity. Qed.

(* the three .rodata literals of the first line (listing +0x104, +0x110, +0x114) *)
Definition LA_FMT_SS : Z := 0x21640.          (* "%s: %s " *)
Definition LA_S_REACPW : Z := 0x212e0.        (* "reac-pw" *)
Definition LA_S_E_NOT_MARKED : Z := 0x21660.  (* "E_NOT_MARKED" *)
Definition S_FMT_SS : list byte := map (Z_to_bv 8) [37; 115; 58; 32; 37; 115; 32].
Definition S_REACPW : list byte := map (Z_to_bv 8) [114; 101; 97; 99; 45; 112; 119].
Definition S_E_NOT_MARKED : list byte :=
  map (Z_to_bv 8) [69; 95; 78; 79; 84; 95; 77; 65; 82; 75; 69; 68].

(* the runtime entries this function calls *)
Definition LA_frame_alloc_0 : Z := 0x3d914.
Definition LA_wrapper_fprintf : Z := 0x43084.
Definition LA_wrapper_vfprintf : Z := 0x4307c.

(* the read-only image's first page and the .got cell that holds &__stack_chk_guard (0x651c50): the two bounds the released
   printf route puts on a format (link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f), relocation table) *)
Definition LA_RO_LO : Z := 0x10000.
Definition LA_GOT_GUARD : Z := 0xa2658.

(* ==========================================================================
   2. link's memory FILE on image A: the frame's AMemFileSink.amemfile_at at link_amf, and the window with k
      bytes pending (LinkMfDefs.v amf_win; plain memfile_c.v mf_win)
   ========================================================================== *)

(* the most bytes one line of this unit puts on the stream (reac_served_mark_c.v uses it too) *)
Definition EMIT_HEAD : Z := 22.   (* "reac-pw: E_NOT_MARKED " *)

(* the stack bound on image A: the 128-byte frame, the realignment slack, then the printf wrapper's window *)
Definition REAC_CODE_EMIT_AFRAME : Z := 128.
Definition REAC_CODE_EMIT_ASLACK : Z := 16.
Definition AEMIT_RT_STK : Z := 9216.   (* lib/A/AE2t.v:36 FPI_STK, the fprintf interceptor's window *)
Definition REAC_CODE_EMIT_AK : Z :=
  REAC_CODE_EMIT_AFRAME + REAC_CODE_EMIT_ASLACK + AEMIT_RT_STK.
Lemma REAC_CODE_EMIT_AK_val : REAC_CODE_EMIT_AK = 9360. Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* a field of the FILE block, over the A view (`val_mem` counts its bytes in nat) *)
Definition amf_fld (m : word -> option byte) (f off : Z) (n : nat) (v : Z) : Prop :=
  val_mem segs m (f + off) n v.

(* the write window with k bytes pending: empty (after fmemopen, after rewind, or after a write past the end),
   or active after __towrite. The same text as lib/A/Rt/LinkMfDefs.v's `amf_win`. *)
Definition amf_win (m : word -> option byte) (f k : Z) : Prop :=
  (k = 0 /\ amf_fld m f 32 8 0 /\ amf_fld m f 40 8 0 /\ amf_fld m f 56 8 0) \/
  (0 <= k <= AMF_BUFSIZ /\
   amf_fld m f 32 8 (f + AMF_BUF + AMF_BUFSIZ) /\ amf_fld m f 40 8 (f + AMF_BUF + k) /\
   amf_fld m f 56 8 (f + AMF_BUF)).

(* THE predicate the three contracts of this slice share: link's memory FILE at f (the frame's amemfile_at at
   link_amf) with k bytes pending (LinkMfDefs.v `amf_k`), its 1304-byte block and g_said writable *)
Definition amemfile_k (m : word -> option byte) (f k : Z) : Prop :=
  amemfile_at segs link_amf m f /\ amf_win m f k
  /\ awrange segs m f AMF_BLOCK /\ awrange segs m LA_G_SAID SAID_SIZE.

(* where the FILE block must lie for the printf layer's checked writes, inside a function of stack bound K *)
Definition amf_blk_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (f : Z) : Prop :=
  amem_range f (AMF_BLOCK + 8)
  /\ range_addressable (ard segs m) SHADOW_OFF f AMF_BLOCK
  /\ shadow_hull_vis (ard segs m) f AMF_BLOCK
  /\ apart_frame regs K f AMF_BLOCK.

(* ==========================================================================
   3. The format and the four vararg registers
   ========================================================================== *)

(* one vararg register against the piece it feeds, over the A view (the twin of printf_facts_c.v `pf_arg_ok`) *)
Definition apf_arg_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (f : Z)
    (r : word) (a : printf_facts_c.pf_arg) : Prop :=
  match a with
  | printf_facts_c.AInt v => - 2 ^ 31 <= v < 2 ^ 31 /\ bv_unsigned r mod 2 ^ 32 = v mod 2 ^ 32
  | printf_facts_c.AU64 u => bv_unsigned r = u
  | printf_facts_c.APtr s =>
      Forall (fun c => 0 < c < 256) s /\
      acstr_at segs m (bv_unsigned r) (map (Z_to_bv 8) s) /\
      astr_rt_ok segs regs K m (bv_unsigned r) (map (Z_to_bv 8) s) /\
      apart (bv_unsigned r) (Z.of_nat (length s) + 8) f AMF_BLOCK
  end.

Fixpoint apf_args_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (f : Z)
    (rs : list word) (args : list printf_facts_c.pf_arg) : Prop :=
  match args, rs with
  | [], _ => True
  | a :: args', r :: rs' => apf_arg_ok regs K m f r a /\ apf_args_ok regs K m f rs' args'
  | _ :: _, [] => False
  end.

(* the bytes the `%s` conversions read: for each vararg register the format makes an `APtr s`, the string s and
   its NUL at that register's address; a register the format makes an integer, or does not consume, covers no
   byte *)
Fixpoint apf_rd (rs : list word) (args : list printf_facts_c.pf_arg) (a : Z) : Prop :=
  match args, rs with
  | printf_facts_c.APtr s :: args', r :: rs' =>
      (bv_unsigned r <= a <= bv_unsigned r + Z.of_nat (length s)) \/ apf_rd rs' args' a
  | _ :: args', _ :: rs' => apf_rd rs' args' a
  | _, _ => False
  end.

(* the pieces link's printf callees accept (lib/A/Rt/LinkPfPiece.v `pf_link_piece`): a literal
   byte, `%d`, `%s` *)
Definition apf_link_piece (p : printf_facts_c.pf_piece) : Prop :=
  match p with
  | printf_facts_c.PLit _ | printf_facts_c.Pd | printf_facts_c.Ps => True
  | _ => False
  end.

(* the caller's format at fp parses into ps, the four vararg registers are its args, and its text is T *)
Definition aemit_fmt (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (f fp : Z)
    (fmt : list Z) (ps : list printf_facts_c.pf_piece) (args : list printf_facts_c.pf_arg)
    (T : list Z) : Prop :=
  acstr_at segs m fp (map (Z_to_bv 8) fmt)
  /\ astr_rt_ok segs regs K m fp (map (Z_to_bv 8) fmt)
  /\ LA_RO_LO <= fp /\ fp + Z.of_nat (length fmt) + 1 <= LA_GOT_GUARD
  /\ printf_facts_c.pf_parse fmt = Some ps
  /\ fmt <> []
  /\ Forall apf_link_piece ps
  /\ printf_facts_c.pf_text ps args = Some T
  /\ apf_args_ok regs K m f
       [getr regs 14; getr regs 15; getr regs 16; getr regs 17] args.

(* ==========================================================================
   4. The contract
   ========================================================================== *)

Definition reac_code_emit_apre (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists fmt ps args T k,
    aarg regs 0 <> 0 /\ aarg regs 3 <> 0
    /\ In (aarg regs 0, AMF_BLOCK) bl
    /\ amemfile_k m (aarg regs 0) k
    /\ amf_blk_ok regs REAC_CODE_EMIT_AK m (aarg regs 0)
    /\ k + EMIT_HEAD + Z.of_nat (length T) <= AMF_BUFSIZ
    /\ aemit_fmt regs REAC_CODE_EMIT_AK m (aarg regs 0) (aarg regs 3) fmt ps args T
    /\ acstr_at segs m LA_FMT_SS S_FMT_SS
    /\ astr_rt_ok segs regs REAC_CODE_EMIT_AK m LA_FMT_SS S_FMT_SS
    /\ acstr_at segs m LA_S_REACPW S_REACPW
    /\ astr_rt_ok segs regs REAC_CODE_EMIT_AK m LA_S_REACPW S_REACPW
    /\ acstr_at segs m LA_S_E_NOT_MARKED S_E_NOT_MARKED
    /\ astr_rt_ok segs regs REAC_CODE_EMIT_AK m LA_S_E_NOT_MARKED S_E_NOT_MARKED.

(* the read set: the caller's format, and the string of each vararg register the format consumes as `%s` *)
Definition reac_code_emit_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  astr_rd segs m (aarg regs 3) a \/
  (exists fmt ps args T, aemit_fmt regs REAC_CODE_EMIT_AK m (aarg regs 0) (aarg regs 3) fmt ps args T
     /\ apf_rd [getr regs 14; getr regs 15; getr regs 16; getr regs 17] args a).

(* the write set: the FILE block. No flush runs (the Pre bounds the pending bytes by the buffer), so g_said is
   not written; the class-0 side frame is taken and released inside the call. *)
Definition reac_code_emit_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [aivl (aarg regs 0) AMF_BLOCK].

Definition reac_code_emit_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall fmt ps args T k,
    aemit_fmt regs REAC_CODE_EMIT_AK m (aarg regs 0) (aarg regs 3) fmt ps args T ->
    amemfile_k m (aarg regs 0) k ->
    amemfile_k m' (aarg regs 0) (k + EMIT_HEAD + Z.of_nat (length T)).

Definition reac_code_emit_acontract : Prop :=
  aleaf_fx SK segs rlo rhi B REAC_CODE_EMIT_A REAC_CODE_EMIT_AK 0 [(0, 1)]
    reac_code_emit_apre reac_code_emit_ard reac_code_emit_awr reac_code_emit_apost.

End c.
