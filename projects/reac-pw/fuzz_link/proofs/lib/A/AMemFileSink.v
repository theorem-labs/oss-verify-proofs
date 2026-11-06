(** * reac-pw/fuzz_link (asan, image A): the harness's one memory FILE in the ASan frame's forms.

    The A twin of lib/MemFileSink.v (plain). [mark_quietly] (projects/reac-pw/fuzz_link/source/fuzz_link.c:150-164)
    opens [g_sink = fmemopen(g_said, 4096, "w")] once and never closes it. In the asan build (pin 059dae63e07c)
    fmemopen's FILE is one 1304-byte block of the ASan allocator (fmemopen 0x96a1c: +0x94 [addi a0,zero,0x518],
    +0x98 [jal 0x540cc], the malloc interceptor's trampoline, [Tfib_code]'s [pc_wrap_malloc]), and fmemopen ends in
    a tail call of __ofl_add (+0x1cc [j 0x971d0]), which links the FILE at the open-file list head. So from the
    first mark on, the list holds that FILE and the allocator holds its block, for the rest of the process.

    The pcap A frame states, at every return of LLVMFuzzerTestOneInput, the open-file head 0
    ([PSource.asource_none]: [asrc_stdio_env m /\ val_mem segs m (as_ofl_head K) 8 0]) and the call's live blocks
    as a permutation of the caller's ([Permutation (ablocks B ly' S') (ablocks B ly S)], pcap's PcapEntry.v). Link
    breaks both from its first mark. This file states link's replacements (new link-local files only; no frame file
    changes; the record is not an instance of pcap's read-stream record [asource_syms], whose "rb" literals link does
    not have, as the plain design keeps [sk_file := None]):
    - [amf_sink m]: the post's open-file clause. [asource_none] with its head 0 replaced by the one-FILE
      disjunction (the three heads [g_sink], [g_say] and the list head all 0, or all three [f] and a memory FILE
      at [f]); its stdio words are the first three conjuncts of [asrc_stdio_env] ([__libc.threaded],
      [__libc.need_locks], [ofl_lock]), all 0; the others are dropped (see [amf_sink]);
    - [amf_gi T m]: the GI conjunct over the kept blocks [T], as the plain [mf_gi];
    - [amf_gi_ledger B ly S T m]: [amf_gi] and every kept block live in the A allocator ledger [ablocks B ly S],
      so the AR laws give the kept block's range, presence, ownership and addressable shadow (AMemFile.v
      [amf_block_facts]);
    - [amf_blocks_post T T' bl bl']: the post's block clause. The kept blocks only grow ([T' = T ++ D]) and the
      call's live blocks at the return are the caller's plus [D] (the FILE on the first mark, else nothing). It is
      sound only together with [amf_gi T'] at the same return, which forces [D = []] or [T = []] and
      [D = [(f, AMF_BLOCK)]] (AMemFileRI.v [ARI_mf_step], AMemFile.v [amf_blocks_post_bytes]): every consumer
      states both.

    The layout constants are musl's [struct mem_FILE] as link's asan fmemopen fixes them (AMemFile.v
    [link_amf_code] checks each instruction against the image): the FILE (232 bytes), the cookie
    [struct cookie { size_t pos, len, size; unsigned char *buf; int mode; }] at +232, the buffer at +280. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** Layout of musl's [struct mem_FILE] (asan fmemopen 0x96a1c; the offsets are the plain build's). *)
Definition AMF_BLOCK : Z := 1304.   (* +0x94 addi a0,zero,0x518; +0x98 jal malloc *)
Definition AMF_ZEROED : Z := 272.   (* +0xb4 addi a2,zero,0x110; +0xbc jal memset (f, 0, 272) *)
Definition AMF_COOKIE : Z := 232.   (* +0xc0 addi a0,s0,0xe8; +0xcc sd a0,0x98(s0): f->cookie *)
Definition AMF_BUF : Z := 280.      (* +0xc8 addi a2,s0,0x118; +0xd4 sd a2,0x58(s0): f->buf *)
Definition AMF_BUFSIZ : Z := 1024.  (* +0xd0 addi a0,zero,0x400; +0xd8 sd a0,0x60(s0): f->buf_size *)
Definition AF_NORD : Z := 4.        (* +0x11c addi a0,zero,4; +0x128 sw a0,0(s0): mode "w" without '+' *)
Definition AF_ERR : Z := 32.        (* mwrite 0x96cc0 +0x94 ori a0,a0,0x20: a write past the cookie's size *)
Definition AU32M1 : Z := 4294967295.

(** The FILE's fixed parts and the stdio words, as addresses of the asan image (AMemFile.v [link_amf]). *)
Record amemfile_syms : Type := MkAMemFileSyms {
  amf_sink_addr : Z;   (* &g_sink (fuzz_link.c:151) *)
  amf_say_addr : Z;    (* &g_say (reac_served_mark.c:14) *)
  amf_buf : Z;         (* &g_said: the cookie's buf (fuzz_link.c:150, 156) *)
  amf_size : Z;        (* sizeof g_said: the cookie's size *)
  amf_mode : Z;        (* the first byte of the mode string "w": the cookie's mode *)
  amf_read : Z;        (* mread: f->read *)
  amf_write : Z;       (* mwrite: f->write *)
  amf_seek : Z;        (* mseek: f->seek *)
  amf_close : Z;       (* mclose: f->close *)
  amf_threaded : Z;    (* __libc.threaded: fmemopen sets f->lock = -1 when it is 0 *)
  amf_need_locks : Z;  (* __libc.need_locks: __lock returns at once when it is 0 *)
  amf_ofl_lock : Z     (* ofl_lock: the open-file list's lock word *)
}.

(** musl keeps the open-file list head right above its lock (as [PSource.as_ofl_head]). *)
Definition amf_ofl_head (MS : amemfile_syms) : Z := amf_ofl_lock MS + 8.

(** The law tying the record's list head to the head the A frame's journal spares ([YCbq.AOFL_HEAD], which is
    [YI16.sk_ofl_head]; [PSource.asource_head_law] is the read-stream twin). The sink head is EXPLICIT, as on
    pcap's PcapEntry.v statements: the A closure holds the plain build's global instance (YI5b.v
    [src0_sink_head]), so an inferred one would name the plain image's head. *)
Definition amf_head_law (SK : YI16.sink_head) (MS : amemfile_syms) : Prop := amf_ofl_head MS = @YI16.sk_ofl_head SK.

(** The sum of the sizes of a block list. *)
Definition kept_bytes (T : list (Z * Z)) : Z := fold_right (fun b acc => snd b + acc) 0 T.

Section c.
Variable segs : list Segment.
Variable MS : amemfile_syms.
Local Notation fld m f off n v := (val_mem segs m (f + off) n v).

(** [amemfile_static]: what fmemopen writes and no later code changes (memset leaves the other fields 0), the
    cookie's [size], [buf] and [mode], and [prev] / [next] (the list holds this FILE alone).
    [amemfile_flags]: F_NORD, with F_ERR after a write past the cookie's size. [amemfile_omode]: 0 from fmemopen,
    -1 after __towrite. [amemfile_window]: [rpos] / [rend] 0; the write window empty or active with [k] bytes
    pending. [amemfile_cookie]: [pos <= len <= size]; every mark rewinds, so [pos] is not invariant. *)
Definition amemfile_static (m : word -> option byte) (f : Z) : Prop :=
  fld m f 24 8 (amf_close MS) /\ fld m f 48 8 0 /\
  fld m f 64 8 (amf_read MS) /\ fld m f 72 8 (amf_write MS) /\ fld m f 80 8 (amf_seek MS) /\
  fld m f 88 8 (f + AMF_BUF) /\ fld m f 96 8 AMF_BUFSIZ /\
  fld m f 104 8 0 /\ fld m f 112 8 0 /\
  fld m f 120 4 AU32M1 /\ fld m f 124 4 0 /\ fld m f 128 8 0 /\
  fld m f 140 4 AU32M1 /\ fld m f 144 4 AU32M1 /\
  fld m f 152 8 (f + AMF_COOKIE) /\
  fld m f 160 8 0 /\ fld m f 168 8 0 /\ fld m f 176 8 0 /\ fld m f 184 8 0 /\
  fld m f 192 8 0 /\ fld m f 200 8 0 /\ fld m f 208 8 0 /\ fld m f 216 8 0 /\ fld m f 224 8 0 /\
  fld m f (AMF_COOKIE + 16) 8 (amf_size MS) /\ fld m f (AMF_COOKIE + 24) 8 (amf_buf MS) /\
  fld m f (AMF_COOKIE + 32) 4 (amf_mode MS).

Definition amemfile_flags (m : word -> option byte) (f : Z) : Prop :=
  fld m f 0 4 AF_NORD \/ fld m f 0 4 (AF_NORD + AF_ERR).

Definition amemfile_omode (m : word -> option byte) (f : Z) : Prop :=
  fld m f 136 4 0 \/ fld m f 136 4 AU32M1.

Definition amemfile_window (m : word -> option byte) (f : Z) : Prop :=
  fld m f 8 8 0 /\ fld m f 16 8 0 /\
  ((fld m f 32 8 0 /\ fld m f 40 8 0 /\ fld m f 56 8 0) \/
   (exists k, 0 <= k <= AMF_BUFSIZ /\
      fld m f 32 8 (f + AMF_BUF + AMF_BUFSIZ) /\ fld m f 40 8 (f + AMF_BUF + k) /\ fld m f 56 8 (f + AMF_BUF))).

Definition amemfile_cookie (m : word -> option byte) (f : Z) : Prop :=
  exists pos len, 0 <= pos <= len /\ len <= amf_size MS /\
    fld m f AMF_COOKIE 8 pos /\ fld m f (AMF_COOKIE + 8) 8 len.

Definition amemfile_at (m : word -> option byte) (f : Z) : Prop :=
  0 < f /\ f + AMF_BLOCK <= 2 ^ 64 /\ f mod 16 = 0 /\
  amemfile_static m f /\ amemfile_flags m f /\ amemfile_omode m f /\ amemfile_window m f /\
  amemfile_cookie m f.

(** [g_sink], [g_say] and the open-file list head all hold [v]. *)
Definition amf_heads (m : word -> option byte) (v : Z) : Prop :=
  val_mem segs m (amf_sink_addr MS) 8 v /\ val_mem segs m (amf_say_addr MS) 8 v /\
  val_mem segs m (amf_ofl_head MS) 8 v.

(** The three stdio words, all 0: the first three conjuncts of [PSource.asrc_stdio_env] (read at fmemopen 0x96ba8
    [__libc.threaded], __lock 0x9b4d8 [__libc.need_locks], __unlock 0x9b75c [ofl_lock]). *)
Definition amf_env (m : word -> option byte) : Prop :=
  val_mem segs m (amf_threaded MS) 1 0 /\ val_mem segs m (amf_need_locks MS) 1 0 /\
  val_mem segs m (amf_ofl_lock MS) 4 0.

(** The post's open-file clause: [asource_none] with its [head = 0] replaced by the one-FILE disjunction and its
    stdio environment cut to [amf_env]. The dropped conjuncts of [asrc_stdio_env] need no clause: link has no
    "rb\0"; "rwa\0" (0x20291, read by fmemopen's strchr) is read-only, so [arodata_okS] gives it; the canary
    conjunct (0x651c50, read by mseek 0x96de0-0x96de8) is an existential that every memory satisfies through
    [mbyte]'s image fallback (AFih.v [img_word]). *)
Definition amf_sink (m : word -> option byte) : Prop :=
  amf_env m /\ (amf_heads m 0 \/ exists f, amf_heads m f /\ amemfile_at m f).

(** The GI conjunct over the kept blocks [T]: before the first mark the three heads are 0 and nothing is kept;
    from then on they are [f], [f] is the one kept block, and it is a memory FILE over [g_said]. *)
Definition amf_gi (T : list (Z * Z)) (m : word -> option byte) : Prop :=
  (amf_heads m 0 /\ T = []) \/
  (exists f, amf_heads m f /\ T = [(f, AMF_BLOCK)] /\ amemfile_at m f).

(** The bytes [amf_gi] reads outside the kept block, and the buffer the FILE writes into. *)
Definition amf_head_addr (a : Z) : Prop :=
  (amf_sink_addr MS <= a < amf_sink_addr MS + 8) \/ (amf_say_addr MS <= a < amf_say_addr MS + 8) \/
  (amf_ofl_head MS <= a < amf_ofl_head MS + 8).

Definition amf_env_addr (a : Z) : Prop :=
  a = amf_threaded MS \/ a = amf_need_locks MS \/ (amf_ofl_lock MS <= a < amf_ofl_lock MS + 4).

Definition amf_said_addr (a : Z) : Prop := amf_buf MS <= a < amf_buf MS + amf_size MS.

(** The program-global ranges a call that marks may change (the [G] of the A frame's [ajournal_gx]): the
    three heads and [g_said]. *)
Definition amf_globals : list (Z * Z) :=
  [(amf_sink_addr MS, 8); (amf_say_addr MS, 8); (amf_buf MS, amf_size MS); (amf_ofl_head MS, 8)].

Lemma amf_heads_ofl : forall m v, amf_heads m v -> val_mem segs m (amf_ofl_head MS) 8 v.
Proof. intros m v (_ & _ & H). exact H. Qed.

Lemma amf_sink_env : forall m, amf_sink m -> amf_env m.
Proof. intros m (H & _). exact H. Qed.

(** Before the first mark the clause is the pcap form's: the stdio words and every head 0. *)
Lemma amf_sink_of_none : forall m, amf_env m -> amf_heads m 0 -> amf_sink m.
Proof. intros m He Hh. split; [exact He | left; exact Hh]. Qed.

Lemma amf_none_of_sink : forall m, amf_sink m -> amf_heads m 0 ->
  amf_env m /\ val_mem segs m (amf_ofl_head MS) 8 0.
Proof. intros m (He & _) H0. split; [exact He | exact (amf_heads_ofl _ _ H0)]. Qed.

Lemma amf_sink_of_gi : forall T m, amf_gi T m -> amf_env m -> amf_sink m.
Proof.
  intros T m HG He. split; [exact He|].
  destruct HG as [(H & _) | (f & H & _ & Hf)]; [left; exact H | right; exists f; split; assumption].
Qed.

Lemma amf_gi_of_sink : forall m, amf_sink m -> exists T, amf_gi T m.
Proof.
  intros m (_ & [H | (f & H & Hf)]).
  - exists []. left. split; [exact H | reflexivity].
  - exists [(f, AMF_BLOCK)]. right. exists f. split; [exact H|]. split; [reflexivity | exact Hf].
Qed.

Lemma amf_gi_shape : forall T m, amf_gi T m -> T = [] \/ exists f, T = [(f, AMF_BLOCK)].
Proof. intros T m [(_ & ->) | (f & _ & -> & _)]; [left; reflexivity | right; exists f; reflexivity]. Qed.

Lemma amf_gi_kept_bytes : forall T m, amf_gi T m -> 0 <= kept_bytes T <= AMF_BLOCK.
Proof. intros T m H. destruct (amf_gi_shape T m H) as [-> | (f & ->)]; cbn [kept_bytes fold_right snd]; unfold AMF_BLOCK; lia. Qed.

End c.

Section l.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable segs : list Segment.
Variable MS : amemfile_syms.

(** The GI conjunct with the kept blocks in the A allocator ledger. *)
Definition amf_gi_ledger (ly : alayout) (S : astate) (T : list (Z * Z)) (m : word -> option byte) : Prop :=
  amf_gi segs MS T m /\ incl T (ablocks B ly S).

End l.

(** The post's block clause: the kept blocks grow by [D] and the live blocks at the return are the caller's
    plus [D]. With [D = []] it is pcap's [Permutation (ablocks B ly' S') (ablocks B ly S)]. *)
Definition amf_blocks_post (T T' bl bl' : list (Z * Z)) : Prop :=
  exists D, T' = T ++ D /\ Permutation bl' (D ++ bl).

Lemma amf_blocks_post_same : forall T bl bl', Permutation bl' bl -> amf_blocks_post T T bl bl'.
Proof. intros T bl bl' H. exists []. split; [rewrite app_nil_r; reflexivity | exact H]. Qed.

Lemma amf_blocks_post_open : forall f bl bl', Permutation bl' ((f, AMF_BLOCK) :: bl) ->
  amf_blocks_post [] [(f, AMF_BLOCK)] bl bl'.
Proof. intros f bl bl' H. exists [(f, AMF_BLOCK)]. split; [reflexivity | exact H]. Qed.

(** The harness journal's footprint (the [FP] of the target call's [ajournal_gx], pcap's [[YI16.sink_token]]):
    the sink token plus each kept block as the half-open range [(f, f + n)] that [inFP] reads. With [T = []] it is
    pcap's [[sink_token]]; once the first mark has opened the FILE, [amf_gi] forces [T = [(f, AMF_BLOCK)]] with
    [f] the value of [g_sink], and the footprint is [[sink_token; (f, f + AMF_BLOCK)]]: so the journal's write
    clause ([YCbq.awr_byte]'s [inFP FP a] arm) grants every byte of the FILE on every later call
    (AMemFile.v [amf_harness_fp_grants]), where [in_tmp_block] no longer does (the block is already in the
    caller's ledger). [amf_gi] carries it from call to call (AMemFile.v [amf_harness_fp_of_gi],
    [amf_harness_fp_next]). *)
Definition amf_harness_fp (T : list (Z * Z)) : list (Z * Z) :=
  YI16.sink_token :: map (fun b => (fst b, fst b + snd b)) T.
