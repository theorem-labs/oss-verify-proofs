(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the read-stream (source) analogue of cgif_file_fuzzer's write sink
   lib/YE00.v asink_syms / asink_at, for libreac/fuzz_pcap on libreac v1.9.0.

   Why a new file rather than a relocation: cgif's sink is fd- and path-backed (asink_at carries
   Fs.fs_lookup (m_fs md) sink_path and fd_lookup ... FdFileW ...). pcap's stream is an fmemopen
   memory stream: it has no fd and no path, and its backing is a cookie in the FILE block. The shape
   below is cgif's (a static part, a window part, the stdio environment); the content is pcap's.
   NOTE: unlike cgif's YE00.v this file does NOT state the ASan meta region. as_meta_ptr / as_meta_mem
   are carried in the symbol record for the walks that need them, but no conjunct here constrains that
   memory: the meta invariant travels as the core's own ameta_inv premise at each call site instead
   (a Theorem Labs lane, flagged the earlier comment for claiming otherwise).

   IMAGE ROOT: the ORIGINAL v1.9.0 set, which is what the statements target --
   pins (internal path), unstripped twins under
   x/unstripped/, statements ed6b6b7b0ab. NOT the toolchain-N images: a runtime premise
   true on one can be false on the other (Lead; the Theorem Labs lane's AsanRT.v
   malloc_context_size = 1 is exactly such a premise, true on N and false here).

   Every numeral is MEASURED on pcap's v1.9.0 ASan image
   (internal path) (unstripped twin of the
   pin s/fuzz_pcap/fuzz_pcap.asan), from its nm / readelf / objdump dumps in
   (internal path). Addresses are cited at each definition. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* val_mem / garr8 / bytes_ok come from pcap's own Reusable layer, which is
   cgif_file_fuzzer's vocabulary already copied into this unit (YI04.v:141,
   YI00.v:15-17). Deliberately NOT lib/Lib's bytes_at / le8 idiom: the donor
   states its FILE fields with val_mem, and half (1) composes against that. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI00 YI04.
(* YI16: sink_token and sink_open_fp, which ajournal's fp_spares tests (see asource_fp). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The FILE block of an fmemopen stream.                                *)
(*                                                                         *)
(* Layout MEASURED from pcap's own plain proof lib/Prog/StdioModel.v:70-80 *)
(* (mfile_cells), whose musl code is masked-equal to the ASan image's      *)
(* (runtime-donors.md section 3: every one of the 29 musl functions in the *)
(* reach compares eq). Offsets are computed from that cell list, NOT taken *)
(* from cgif: cgif's FILE is 1264 bytes with its buffer at +240, pcap's is *)
(* 1304 with its buffer at +280, so the two layouts do not coincide.       *)
(*                                                                         *)
(*     0 flags(4)   4 pad0(4)    8 rpos(8)   16 rend(8)   24 close(8)      *)
(*    32,40,48,56 zero(8)                                                  *)
(*    64 read(8)   72 write(8)  80 seek(8)   88 bufbase(8)  96 bufsiz(8)   *)
(*   104 prev(8)  112 next(8)  120..151 misc   152 cookie-ptr = f+232      *)
(*   160..231 zero(8) x9                                                   *)
(*   -- the fmemopen cookie --                                             *)
(*   232 cpos(8)  240 len(8)   248 len(8)   256 buf(8)   264 mode 'r'(4)   *)
(*   272 ungetc(8)            280 read buffer (1024) -> ends at 1304       *)
(* ---------------------------------------------------------------------- *)
Definition SRC_FILE_BLOCK : Z := 1304.
Definition SRC_BUF_OFF    : Z := 280.
Definition SRC_BUFSIZ     : Z := 1024.
Definition SRC_COOKIE_OFF : Z := 232.
(* musl writes 'r' (114) into the cookie's mode field for a read stream. *)
Definition SRC_MODE_R     : Z := 114.
(* The all-ones 32-bit cell musl stores in the lock word and the two tail
   words (StdioModel.v mfile_cells' C4 4294967295). *)
Definition U32M1 : Z := 4294967295.

(* The read buffer is the last field: it ends exactly at the end of the block. *)
Lemma src_block_ok :
  SRC_COOKIE_OFF < SRC_BUF_OFF /\ SRC_BUF_OFF + SRC_BUFSIZ = SRC_FILE_BLOCK.
Proof. vm_compute. split; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The symbols the source stream reads, as a record (cgif asink_syms).  *)
(*                                                                         *)
(* MEASURED on fuzz_pcap.asan (asan/fuzz_pcap.nm.txt unless noted):        *)
(*   mread    0x96bec   mwrite   0x96cc0   mseek   0x96dd4  mclose 0x96e70 *)
(*   fmemopen 0x96a1c   ofl_lock 0x652300  ofl_head 0x652308               *)
(*   the "rb\0" mode literal 0x20d40 (.rodata 0x102e0 + file offset;       *)
(*     traced to fmemopen's a2: libreac_fuzz_fopen 0x80798 `mv a2,s0`      *)
(*     then 0x807ac `j 430a8 <__interceptor_trampoline_fmemopen>`, with    *)
(*     s0 the caller's mode pointer set at 0x81568 `addi a1,a0,2012`)      *)
(*   the stream's bytes and length come from the globals                   *)
(*     g_file 0x5d3f60 and g_file_len 0x5d3f40 (objdump 0x80788, 0x80794)  *)
(* The fields are a record rather than constants so that the asan-ubsan    *)
(* copy instantiates the same statements at its own addresses.             *)
(* ---------------------------------------------------------------------- *)
Record asource_syms : Type := mkASource {
  as_read       : Z;   (* mread  *)
  as_write      : Z;   (* mwrite: stored in the FILE, never called on "rb" *)
  as_seek       : Z;   (* mseek  *)
  as_close      : Z;   (* mclose *)
  as_mode       : Z;   (* the "rb\0" literal *)
  as_rwa        : Z;   (* musl's "rwa\0" mode-set literal; the donor's ak_rwa (cgif YE00.v:34, relocated lib/Reusable/YE00.v:35) *)
  as_threaded   : Z;
  as_need_locks : Z;
  as_ofl_lock   : Z;
  as_meta_ptr   : Z;
  as_meta_mem   : Z;
  as_can_got    : Z;
  as_canary     : Z;
  as_icells     : list (Z * Z)
}.

(* musl keeps the open-file list head immediately above its lock. *)
Definition as_ofl_head (K : asource_syms) : Z := as_ofl_lock K + 8.

Definition src_mode_Z : list Z := [114; 98].   (* "rb" *)

(* musl's OWN mode-set literal, not pcap's mode string: fmemopen hands it to strchr to test the
   mode character. It is now a FIELD of asource_syms (as_rwa), the donor's own shape (asink_syms'
   ak_rwa, cgif YE00.v:34 / relocated lib/Reusable/YE00.v:35), not a named constant: naming a constant INSIDE a statement binds it to one
   image even when the hex sits in a Definition (a Theorem Labs lane 23:06Z / 23:10Z, a Theorem Labs lane's item 4). The
   address is the same on both images -- MEASURED end to end through each image's own program
   headers, "rwa\0" occurring exactly once at file offset 0x10026 in each -- so this was a rule
   violation, not a wrong value; each image's KS now supplies it (PSourceK.v's PCAP_RWA). Only
   the BYTES, which are image-independent, stay here. *)
Definition src_modeset_Z : list Z := [114; 119; 97].   (* "rwa" *)

Definition bytesZ (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bytesZ_length : forall l, length (bytesZ l) = length l.
Proof. intros l. apply length_map. Qed.

Lemma bytesZ_app : forall l1 l2, bytesZ (l1 ++ l2) = bytesZ l1 ++ bytesZ l2.
Proof. intros. apply map_app. Qed.

Section b.
Variable segs : list Segment.
Variable K : asource_syms.

Local Notation fld m f off n v := (val_mem segs m (f + off) n v).

(* ---------------------------------------------------------------------- *)
(* 3. source_static: the FILE fields that never move while the stream is   *)
(*    open. Offsets follow StdioModel.v:70-80; the three function pointers *)
(*    are the cookie ops mread / mwrite / mseek, and the close op mclose.  *)
(*    fflush moves ONLY the window (section 4), so every walk that touches *)
(*    the stream keeps this part fixed.                                    *)
(* ---------------------------------------------------------------------- *)
Definition source_static (m : word -> option byte) (f b : Z) (n : Z) : Prop :=
  (* header *)
  fld m f 24  8 (as_close K) /\
  fld m f 64  8 (as_read  K) /\
  fld m f 72  8 (as_write K) /\
  fld m f 80  8 (as_seek  K) /\
  fld m f 88  8 (f + SRC_BUF_OFF) /\
  fld m f 96  8 SRC_BUFSIZ /\
  (* the fmemopen cookie: buffer base, its length twice, and the mode *)
  fld m f (SRC_COOKIE_OFF + 8)  8 n /\
  fld m f (SRC_COOKIE_OFF + 16) 8 n /\
  fld m f (SRC_COOKIE_OFF + 24) 8 b /\
  fld m f (SRC_COOKIE_OFF + 32) 4 SRC_MODE_R /\
  (* the cookie POINTER at +152, which must equal f + 232. mread's first act
     is `c = f->cookie`, a load from this cell, so pinning the cookie's
     fields is not enough: the walk must reach them from f
     (a Theorem Labs lane point 2, which blocks its mread walk outright). *)
  fld m f 152 8 (f + SRC_COOKIE_OFF) /\
  (* the write side, all zero on a read-only stream: wend / wpos / wbase at
     +32 / +40 / +56 and mustbezero_1 at +48. __toread reads
     `f->wpos != f->wbase` and writes all three, so a walk cannot step
     through it without these (a Theorem Labs lane point 5). *)
  fld m f 32 8 0 /\ fld m f 40 8 0 /\ fld m f 48 8 0 /\ fld m f 56 8 0 /\
  (* the open-file list links at +104 (prev) / +112 (next), PINNED TO 0, as the donor pins them
     (YE00.v:86). They were existential here until a Theorem Labs lane's MISMATCH #10a (21:17Z), and that
     made fclose UNPROVABLE: fclose sets *head = f->next (0x8e2a4-0x8e2a8) and writes prev->next /
     next->prev only when those are non-zero (0x8e28c / 0x8e298), so asource_none's `head = 0`
     after the close holds only if next = 0. The fact is that f is the ONLY stream on musl's
     open-file list: __ofl_add inside fmemopen sets f->next = old head and leaves prev 0, and
     pcap's harness opens one memory stream at a time (stdin/stdout/stderr are static and never
     on the list). `as_ofl_head K = f` in asource_at is the other half of the same fact; the
     discharge that the head was 0 before fmemopen belongs to the caller's walk. *)
  fld m f 104 8 0 /\ fld m f 112 8 0 /\
  (* getln_buf at +168, PINNED TO 0 (donor YE00.v:89; a Theorem Labs lane MISMATCH #10b). fclose loads it
     at 0x8e2b0 and passes it to free at 0x8e2b4; free(0) is a no-op, but a non-zero value would
     be a block that is not in the block list, and YCbq.v:364's footprint law would fail. musl
     sets it only inside getline/getdelim, which pcap never calls. *)
  fld m f 168 8 0 /\
  (* +120 is fd (int; musl sets -1 for a memory stream), and +140 / +144 are lock and lbf, all
     three the U32M1 cell (StdioModel.v mfile_cells: C4 4294967295). An earlier comment here
     called +120 "the lock word"; a Theorem Labs lane (#10, 21:17Z) corrected it. The VALUES were always
     right. a Theorem Labs lane needs +140 (lock) pinned because lock < 0 decides __lockfile's branch
     inside fread, and fflush's `bltz` on the same cell takes the no-locking path. *)
  fld m f 120 4 U32M1 /\ fld m f 140 4 U32M1 /\ fld m f 144 4 U32M1 /\
  (* the block is aligned, non-null, and disjoint from the data buffer.
     Disjointness is required, not incidental: without it the memcpy inside
     mread could overlap the FILE object (a Theorem Labs lane point 3). *)
  0 < f /\ f mod 16 = 0 /\ 0 < b /\
  (f + SRC_FILE_BLOCK <= b \/ b + n <= f).

(* The orientation mode (+136), set by __toread and read by the fread walk:
   byte- or wide-oriented, 0 or -1 (StdioModel.v mstl's md). It is NOT in
   source_static because __toread writes it. *)
Definition source_mode (m : word -> option byte) (f : Z) (md : Z) : Prop :=
  val_mem segs m (f + 136) 4 md /\ (md = 0 \/ md = U32M1).

(* ---------------------------------------------------------------------- *)
(* 4. source_window: the read window [rpos, rend) inside the FILE buffer.  *)
(*    Either empty (both null, as fmemopen leaves it) or filled, exactly   *)
(*    as cgif's file_window splits. cpos - p = rend - rpos is the number   *)
(*    of bytes read out of the cookie but not yet handed to the caller.    *)
(* ---------------------------------------------------------------------- *)
(*    pcap keeps rpos at +8 and rend at +16 (StdioModel.v rpos_of/rend_of: *)
(*    both are 0 when the window is empty, else f + 280 + i and            *)
(*    f + 280 + e). There is no separate window base field: +88 holds      *)
(*    f + 280 permanently and belongs to source_static.                    *)
Definition source_window (m : word -> option byte) (f : Z) (W : list Z) : Prop :=
  (W = [] /\ fld m f 8 8 0 /\ fld m f 16 8 0)
  \/
  (exists i : Z,
     0 <= i /\ i + Z.of_nat (length W) <= SRC_BUFSIZ /\
     fld m f 8  8 (f + SRC_BUF_OFF + i) /\
     fld m f 16 8 (f + SRC_BUF_OFF + i + Z.of_nat (length W)) /\
     garr8 segs m (f + SRC_BUF_OFF + i) W).

(* ---------------------------------------------------------------------- *)
(* 5. The stdio environment. The ASan meta region is NOT stated here -- see the header note. *)
(* ---------------------------------------------------------------------- *)
Definition asrc_stdio_env (m : word -> option byte) : Prop :=
  val_mem segs m (as_threaded K) 1 0 /\
  val_mem segs m (as_need_locks K) 1 0 /\
  val_mem segs m (as_ofl_lock K) 4 0 /\
  garr8 segs m (as_mode K) (src_mode_Z ++ [0]) /\
  (* The mode-SET literal "rwa\0" at 0x20026, which musl fmemopen hands to strchr for its mode
     test (auipc 0x96a58 + addi 0x96a5c -> 0x20026). That strchr result decides fmemopen's
     EINVAL arm, so a spec of fmemopen cannot prove its post without these bytes; a Theorem Labs lane
     raised it as MISMATCH #6a (21:03Z) against the fmemopen spec, and the predicate is the
     right place for it because the bytes belong to the stdio environment, not to one call.
     MEASURED on the ORIGINAL v1.9.0 image (see the header's IMAGE ROOT): file offset 0x10026
     = vaddr 0x20026 holds 72 77 61 00. Distinct from as_mode's "rb\0" at 0x20d40 (72 62 00). *)
  garr8 segs m (as_rwa K) (src_modeset_Z ++ [0]) /\
  (exists cval, 0 <= cval < 2 ^ 64 /\ val_mem segs m (as_canary K) 8 cval).

(* ---------------------------------------------------------------------- *)
(* 6. asource_at: the read stream, in cgif's vocabulary.                   *)
(*                                                                         *)
(*   f  the FILE block            b  the data buffer                       *)
(*   C  the stream's whole content, as bytes at b (never written: the      *)
(*      mode is "rb", so no mwrite call occurs and C is invariant)         *)
(*   p  the CALLER-consumed count: how many bytes fread has handed back    *)
(*                                                                         *)
(* The cookie position cpos is p + (rend - rpos), per a Theorem Labs lane's ruling  *)
(* (20:15Z): mread copies into the FILE window ahead of the caller, and    *)
(* fflush's mseek rewinds the cookie by exactly rend - rpos. The window    *)
(* holds C[p .. cpos); an empty window means cpos = p.                     *)
(* ---------------------------------------------------------------------- *)
(* The FILE's flags word (+0). musl's read path sets F_EOF when the cookie  *)
(* is exhausted; pcap's plain model encodes exactly this as fl = 8 (open)   *)
(* or fl = 24 (open + EOF), with fl = 24 forcing p = length C              *)
(* (StdioModel.v:110-114 mstl). a Theorem Labs lane needs the predicate to survive a   *)
(* short read, which is this disjunct.                                      *)
Definition source_flags (m : word -> option byte) (f : Z) (fl : Z) : Prop :=
  val_mem segs m f 4 fl /\ (fl = 8 \/ fl = 24).

Definition asource_at (m : word -> option byte) (f b : Z) (C : list Z) (p : Z) : Prop :=
  exists (W : list Z) (cpos fl md : Z),
    let n := Z.of_nat (length C) in
    (* the two levels of "consumed" *)
    0 <= p /\ p <= cpos /\ cpos <= n /\
    (* |C| < 2^63 (a Theorem Labs lane, 21:50Z, row 1c). mseek's two guards compare in SIGNED 64-bit
       arithmetic (off >= -base, off <= size - base), so with no bound on the length a size
       >= 2^63 wraps negative and the "both guards hold" argument in PFmopsM.v fails: the mseek
       post was unprovable. The donor bounds its sink by SINK_MAX; this is stated at exactly the
       strength the signed guard needs and no stronger, because every caller must establish it
       (fmemopen's post, from its length; pcap's input is < 2^26). *)
    n < 2 ^ 63 /\
    (* The buffer does not WRAP the 64-bit address space. Found by the prover (a Theorem Labs lane, 22:47Z)
       and it is a hole no arithmetic can close from the other premises: garr8 reads
       `mbyte m (b + j)` at the address `Z_to_bv 64 (b + j)`, and nothing bounded b from ABOVE.
       With b near 2^64 the wrapped address (b + j) mod 2^64 is small and can land inside the
       callee's own frame -- or on the cookie cell f+232 that mseek writes, since source_static's
       `f + 1304 <= b` is equally powerless against a wrapped byte. `n < 2^63` does not stop it,
       because sp is about 2^46. The disjointness premises the specs now carry do not either:
       their `spZ regs <= b` disjunct is exactly the wrapping case.
       Stated HERE rather than per spec, so afflush_source_spec and afread_spec get it too.
       Every caller can discharge it: pcap's buffer is a heap block below alloc_ceiling. *)
    b + n <= 2 ^ 64 /\
    cpos = p + Z.of_nat (length W) /\
    W = firstn (Z.to_nat (cpos - p)) (skipn (Z.to_nat p) C) /\
    (* the content, pinned in memory and unchanged while the stream is open *)
    bytes_ok C /\ garr8 segs m b C /\
    (* the FILE *)
    source_static m f b n /\ source_window m f W /\
    source_flags m f fl /\ (fl = 24 -> p = n) /\ source_mode m f md /\
    (* the cookie's own position *)
    val_mem segs m (f + SRC_COOKIE_OFF) 8 cpos /\
    (* the environment, and the open-file list linking this FILE *)
    asrc_stdio_env m /\
    val_mem segs m (as_ofl_head K) 8 f /\ f <> 0.

(* The footprint of the stream: the FILE block alone. The data buffer b is
   the caller's (the harness's g_file) and is NOT part of it, which is why
   fclose frees f and never b. cgif's analogue is asink_fp (YE00.v). *)
(* PLUS YI16.sink_token, and the token is not decoration: a Theorem Labs lane measured (ajournal,
   lib/Reusable/YCbq.v:87) that ajournal keeps EVERY image byte outside owned-static / errno unless
   `fp_spares FP a` spares it, and fp_spares spares musl's open-file-list head
   [AOFL_HEAD, AOFL_HEAD + 8) ONLY when the footprint is sink-open -- `sink_open_fp FP = in_fp FP 0`,
   which `In sink_token FP` gives (YI16.v:71-73). A footprint of the FILE block alone would therefore
   keep the head pinned at f while fclose's post says asource_none (head 0): unprovable. cgif carries
   the same token in asink_fp (YE00.v:47) for exactly this reason. *)
Definition asource_fp (f : Z) : list (Z * Z) :=
  [(f, f + SRC_FILE_BLOCK); YI16.sink_token].

Lemma asource_fp_open : forall f, YI16.sink_open_fp (asource_fp f).
Proof. intros f. apply YI16.sink_open_token. right. left. reflexivity. Qed.

(* The law tying this file's head symbol to the one ajournal spares; cgif states the same equation as
   asink_img_laws' ail_head. Without it nothing connects as_ofl_head K to AOFL_HEAD, so the spared
   range need not be the range this predicate names. AOFL_HEAD is the core's constant, so the law is
   stated against it and discharged when the core lands. MEASURED: pcap's ofl_head is 0x652308. *)
Definition asource_head_law (AOFL_HEAD : Z) : Prop := as_ofl_head K = AOFL_HEAD.

(* The closed state: no FILE is linked in musl's open-file list. cgif's
   analogue is asink_none. fclose must establish this. *)
Definition asource_none (m : word -> option byte) : Prop :=
  asrc_stdio_env m /\ val_mem segs m (as_ofl_head K) 8 0.

(* The caller-visible remainder: what a further fread may still return. *)
Definition asource_rest (C : list Z) (p : Z) : list Z := skipn (Z.to_nat p) C.

Lemma asource_rest_length : forall C p,
  0 <= p <= Z.of_nat (length C) ->
  Z.of_nat (length (asource_rest C p)) = Z.of_nat (length C) - p.
Proof.
  intros C p Hp. unfold asource_rest. rewrite length_skipn. lia.
Qed.

(* At EOF the remainder is empty: the fact a Theorem Labs lane's re-read needs. *)
Lemma asource_rest_eof : forall C p,
  p = Z.of_nat (length C) -> asource_rest C p = [].
Proof.
  intros C p ->. unfold asource_rest. rewrite Nat2Z.id. apply skipn_all.
Qed.

(* An empty window is the state fmemopen leaves and the state mseek restores. *)
Definition asource_unbuffered (m : word -> option byte) (f b : Z) (C : list Z) (p : Z) : Prop :=
  asource_at m f b C p /\ source_window m f [].

End b.
