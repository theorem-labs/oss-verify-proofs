(* model_write (fuzz_link.c:403-421) on image A (fuzz_link.asan 0x88100, 664 bytes; listing
   (internal path) (internal record, sha256 2152d78b142c)): what the harness says a write
   of an interface alias owes. a0 = m (the model block), a1 = name, a2 = alias. The plain contract is
   lib/Prog/model_write_c.v; this file states the SAME link_spec result (`write_model`) in link_amem.v's `aleaf_rd`
   form.

   The image-A code, in order:
     +0x00..+0x38  push a 128-byte frame (+0x04 sd zero, 0(sp)); save ra, s0..s11
     +0x3c  s0 := the entry sp;  +0x40 andi sp, sp, -0x20 (realign: sp' = sp - 128 or sp - 144);  +0x44 s1 := sp'
     +0x48, +0x4c  s3 := alias, s6 := name;  +0x68 s4 := m
     +0x50..+0x64  a2 := the side-stack switch cell (.got+0xb8 = 0xa1a28 -> 0xaa440, lw), s9 := the shadow base
                   (.got+0x60 = 0xa19d0 -> 0xaa438)
     +0x6c  beqz a2 -> +0x80 (real-stack fallback);  +0x70..+0x74 frame_alloc_4(0x260) (0x3ddc4);  +0x78 s2 := F
     +0x84  s11 := F (the side-stack arm);  +0x88 bnez -> +0xa8;  +0x8c..+0xa4 the real-stack fallback (alloca of
                   0x260 bytes; s11 := the alloca, +0x90), refuted under aside_room (link-a/form/FORM.md (internal record, sha256 13aeff774164) 4.2)
     +0xa8  sd s11, 0x10(s1) (own frame)
     +0xac..+0xd0  F's header: 0x41b58ab3 at F, the frame descriptor .rodata+0x815 at F + 8, 0x88100 at F + 16
     +0xb8, +0xd8  s5 := shadow(F);  +0xd4..+0xe8 shadow bytes 0..3 := 0xf1 ([F, F + 32));  +0xec s7 := s5 + 4
     +0xf0..+0xf8  meta_fill_f8(s7, 0x40) (0x55f94): shadow bytes 4..0x43 := 0xf8 ([F + 32, F + 544), r[512] out of
                   scope);  +0xfc..+0x11c shadow bytes 0x44..0x4b := 0xf3 ([F + 544, F + 608))
     +0x120  s8 := -22;  +0x124 beqz name -> +0x210;  +0x128..+0x134 check;  +0x138 beqz alias -> +0x210;
     +0x13c  lbu name[0];  +0x140 beqz -> +0x210
     +0x144..+0x148  wrapper_strlen(alias) (0x43044);  +0x14c..+0x158 alen > 255 (unsigned) -> s8 := -36, +0x210
     +0x15c  s8 := alen;  +0x160..+0x164 index_of(name) (0x86784);  +0x168 beqz a0 -> +0x20c (s8 := -19)
     +0x16c  s6 := idx;  +0x170 s9 := r = F + 0x20;  +0x174..+0x17c meta_fill_00(s7, 0x40) (0x55e74): r's 512
                   bytes in scope
     +0x180..+0x188  s10 := len = 32 + ((alen + 7) & 0x1fc) = 32 + align4(4 + alen) (alen <= 255, so the mask is
                   the align-4 of the C)
     +0x18c..+0x198  checked_memset(r, 0, len) (0x53214)
     +0x19c..+0x1c4  sh alen + 4, 0x20(r); sh 20, 0x22(r); sw len, 0(r); sw 0x50010, 4(r) (type 16, flags 5);
                   sw 1, 8(r); sw idx, 0x14(r)
     +0x1c8..+0x1d4  checked_memcpy(r + 0x24, alias, alen) (0x52d78): r = req_write idx alias
     +0x1d8..+0x1f4  talk(m, r, len, 0, 0, 0, 0) (0x8763c);  +0x1f8 s8 := a0;  +0x1fc..+0x204 meta_fill_f8(s7, 0x40)
     +0x210..+0x218  sd 0x45e0360e, 0(F) (the frame retired);  +0x21c beqz s2 -> +0x238 (fallback only)
     +0x220..+0x228  meta_fill_f5(s5, 0x80) (0x55f7c): the 128 shadow bytes of the 1024-byte class-4 frame
     +0x22c  ld a0, 0x3f8(F) (the flag address frame_alloc_4 left at F + 1024 - 8);  +0x230 sb zero, 0(a0): the
                   inline release (astack_free_law; link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2)
     +0x244..+0x284  a0 := s8; sp := s0 - 0x80; restore; pop; ret.  a0 is -22, -36, -19 (addi) or talk's a0.
   THE REAL-STACK FALLBACK (+0x80, +0x8c..+0xa4, +0x238..+0x240) is not reached: AR's const law holds the switch
   cell at 1, and with `aside_room Sc [(4, 1)]` frame_alloc_4 returns a side frame (link-a/form/FORM.md
   (internal record, sha256 13aeff774164) section 4.2). The order of the refusals is write_core's: NULL name, NULL
   alias, empty name -> -22; alen >= 256 -> -36; no index -> -19.

   THE ONE INSTRUMENTED CHECK (1 error-path call):
     1 +0x128..+0x134, +0x288..+0x294  load1 name[0] (name <> 0; it runs before the alias test +0x138)
                                       astrcmp_arg's range_addressable name (|s| + 1)

   Which instruction needs which premise (callee Pres: index_of_c.v `index_of_apre` / `index_of_ard`, talk_c.v
   `talk_apre` / `talk_ard`; the request's facts come from this function's own code):
   - the journal, gp/tp, ret_ok (apre): the frame stores (+0x04..+0x38, +0xa8); frame_alloc_4, the three
     meta_fill calls, wrapper_strlen, checked_memset, checked_memcpy, index_of and talk are applied on it at sp';
     +0x284 ret.
   - K = 128 + 16 + 8272 = 8416: the 128-byte frame (+0x00), the realignment slack (+0x40), then the deepest callee window from sp':
     index_of's K (INDEX_OF_AK = 8272), above talk's TALK_AK = 4240 and the ESTACK windows of frame_alloc_4, meta_fill_00 / _f5 / _f8,
     wrapper_strlen, checked_memset and checked_memcpy. link-a/form/FORM.md (internal record, sha256 13aeff774164)
     section 5's 4368 took talk as the deepest callee and no slack; the plain K (704) does not carry over.
   - SIDE = [(4, 1)]: frame_alloc_4 (+0x74); index_of and talk take no side frame. EV = 0.
   - `amodel_at m mbs`, `model_wf mbs`, `anlk_at g_nl kbs`, `nlk_wf kbs`: talk_apre's. `aiftab_at`: index_of_apre's.
   - `astr_arg name nm`: +0x124, +0x13c (NULL or empty -> -22); index_of_apre's `aarg 0 <> 0` and `acstr_at`.
   - `astr_arg alias al`: +0x138 (NULL -> -22); the string wrapper_strlen measures.
   - index_of's table shadow, `nm = Some s -> astrcmp_arg regs K name s` and the table strings' `astrcmp_arg regs K`
     (for `0 <= p < 2 ^ 64`, link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a class 2): check 1 (the
     name's) and index_of_apre's, at sp' by apart_frame regs K (sp - 144 <= sp', 144 + INDEX_OF_AK = K).
   - `al = Some s ->` the alias, for wrapper_strlen (disco lib/Rt/StrlenDef.v astrlen_realizes: `0 < x` from
     astr_arg and acstr_at, `k + 1 < 2 ^ 32`, `x + k + 1 <= 2 ^ 63` from amem_range, the bytes to the NUL from
     acstr_at, `src_ok x (k + 1)` from acstr_at and apart_frame, `amem_range`, `range_addressable` and
     `shadow_hull_vis` of [alias, alias + |s| + 1)) and for checked_memcpy +0x1d4's source [alias, alias + alen)
     (alen = |s| <= 255; the sub-range of the same facts; `d + n <= x \/ x + n <= d`: r is in the fresh frame F and
     the alias is not, by the read set's akb); and STRLEN'S SLACK (the plain conjunct, LinkHelpers'): the bytes from
     the NUL's successor to the end of its 8-byte granule are present (`abytes`), which the wrapper may read.
     The wrapper's `rom_view` premise is no premise of model_write: it follows from apre's `arodata_okP` and the
     image instance (as text_of_c.v states for memchr).
   - talk's model block and chunk queue: `range_addressable`, `shadow_hull_vis`, `amem_range` of [m, m + MD_SIZE),
     `range_addressable`, `shadow_hull_vis` of [g_nl + NK_CHUNK, + NK_N_CHUNKS), `apart_gnl m`, `apart_frame m`:
     talk_apre's (talk's window [sp' - 4240, sp') lies inside [sp - K, sp)).
   - NOT asked of the caller: the name or the alias apart from the model block (model_unmark passes m->mark[i],
     inside the block, LLVMFuzzerTestOneInput 0x83008 a1 = s7); both are read before talk writes the block.
   - the bytes kept up to the calls: own frame stores (apart_frame), F's header and shadow stores and the
     meta_fill calls (F was a free frame: it meets no byte of the read set, by akb, nor the model block, by ajw),
     the request writes (inside F). talk_apre's request facts at +0x1f4 come from the code: `abytes r
     (req_write idx alias)`, `len <= 292 <= 512`, r's shadow 0 after meta_fill_00 +0x17c, its hull visible (F's
     shadow is a client range), `amem_range r len`, `apart r len m MD_SIZE` and `apart_frame r len` (a side frame
     is apart from heap blocks and from the real stack); talk_ard's [r, r + len) is akb because F's (4, pos) is in
     the frames at the call. talk's buffer conjuncts are vacuous (a3..a6 = 0, +0x1e4..+0x1f0).
   - the write set [(m, m + MD_SIZE)] and apre's `ajw` on it: talk's write set with NULL buffers (aivl 0 0 owns no
     byte). F and its shadow are not in it (taken and released inside the call), nor the flag byte +0x230.
   - `apart (as_errno B) 4 m MD_SIZE` (the kernel-call walk's model_write walk, 2026-10-30): on the -ENODEV path
     (+0x168 `beqz a0` after index_of -> +0x20c) the Post gives the model block back across the index_of call, and
     index_of's `apost` gives it only through `akept`, whose image clause excepts [as_errno B, as_errno B + 4). The
     Pre locates the block nowhere (`ajw` admits a byte of G), so without this the statement allows the block to BE
     errno bytes and the Post does not follow. True at every call site: the block is the calloc'd heap block, errno
     is an image byte (tp - 164).
   - the read set Rd (`aleaf_rd`): the name and its NUL (+0x13c, index_of's strcmp), the alias and its NUL
     (wrapper_strlen, checked_memcpy), and every interface-table string with its NUL: index_of reads them through
     pointers loaded from g_nl, but frame_alloc_4 (+0x74) runs BEFORE, so a string in a free class-4 frame would be
     handed out as F and overwritten (+0xc8..+0xd0, the request writes); so they are in Rd too. A table pointer is
     the `au64_at` value, whose range `acstr_at` fixes. The alias's slack after its NUL is NOT in Rd: its values are
     never used (the wrapper's answer is the index of the NUL), and for a fuzz_str alias (fuzz.h:84-89, malloc of
     |s| + 1) those bytes lie past the block's requested size, where akb does not hold: putting them in Rd would
     make the Pre false at op_write's call.

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 704` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a).
   - `wz` is written `w64` (the same Z_to_bv 64).
   Nothing of the plain Pre or Post is false of image A.
   Released proofs (rule 24): none of model_write (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): no
   hit on any of the four refs).

   CALL SITES (link-a/facts/asan-set.tsv (internal record, sha256 e26bb6a28c00): LLVMFuzzerTestOneInput only):
   - 0x83858 (op_write): a0 = ld 0xe8(s1) = m; a1 = s5 = name_of's answer (g_names[s], odd[s % 6] or NULL);
     a2 = s6 = text_of's answer (+0x1008): texts[s % 11] (.rodata) or a fuzz_str block of |s| + 1 bytes (heap,
     allocated in this journal; |s| <= 319).
   - 0x83920 (model_mark): a0 = s6 = m; a1 = s4 (non-NULL, non-empty: +0xb38..+0xb50); a2 = .str.11 = 0x21100,
     the 15 bytes of "reac-pw:served" and its NUL (the literal model_unmark compares 15 bytes of, +0x810..+0x81c).
   - 0x83008 (model_unmark): a0 = s6 = m; a1 = s7 = m->mark[i] (inside the block, terminated by model_marks_wf);
     a2 = .str.1 = 0x20fc0 (the empty string).
   At each: names, aliases and table strings are image bytes or heap-block bytes (akb); the model block is a block
   calloc'd in the journal (`ajw` by in_tmp_block); all are outside [sp - K, sp).

   Satisfiability witness (the closed lemma `model_write_apre_sat` of lib/A/Prog/help_witness.v, M = 0x602000001000,
   sp = 0x7fffffffee60): the run of link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) and talk_c.v, first op
   op_write (op byte 1): name byte 0 -> "nl0" (0x62fac0); text byte 1 -> texts[1] = "reac-pw:served", A_SERVED = 0x21100,
   the word at LA_TEXTS + 8 (a .rodata string literal; shadow 00 07 f9 f9); kernel()'s input bytes: flags 0, errno
   byte 0, end-errno byte 0 (nl_errno(0) = 105, so end_errno = 105), one chunk of mode 0 with one message of kind 1:
   nl_error(w, 0, -1), 36 bytes 24 00 00 00 02 00 00 00 01 00 00 00 00 00 00 00 | 00 00 00 00 | 16 x 00 (an ACK).
   - registers at 0x83858: ra = 0x8385c; sp = 0x7fffffffee60; a0 = M (the calloc(1, 8856) block, e.g.
     0x621000000100); a1 = 0x62fac0; a2 = A_SERVED; gp, tp = as_gp B, as_tp B.
   - memory: M all 0 (model_wf); g_nl with n_chunks 1, next 0, chunk_len[0] = 36, chunk[0] the 36 bytes above,
     end_errno 105, the other errnos and counters 0, n_if 64 and interfaces()' table (nlk_wf, aiftab_at);
     nm = Some "nl0", al = Some "reac-pw:served" (14 bytes).
   - conjunct by conjunct: the model, g_nl and table facts and the name's astrcmp_arg as model_read_c.v's witness;
     the alias: 15 < 2 ^ 32, A_SERVED + 15 <= kLowMemEnd - 1, its 15 bytes addressable (an instrumented string
     literal: shadow 0 then 7) and their shadow visible, below sp - 8416; the slack: the (- (A_SERVED + 15)) mod 8
     bytes after the NUL are .rodata bytes (the literal's redzone), present; M and the queue as model_read_c.v's
     witness.
   - the A-state: own = frames Sc = [(4, p4)] (LLVMFuzzerTestOneInput's frame); `aside_room Sc [(4, 1)]`:
     count_cid 4 = 1, 1 + 1 <= fs_frames 4 = 1024; Rd: "nl0", A_SERVED's bytes and the table strings are image bytes
     (akb); `ajw` on M by in_tmp_block; st_nev S + k + 0 <= EV_MAX.
   - the errno separation: M is above kLowMemEnd and errno is an image byte below it, so it holds by its left
     disjunct. The closed lemma `model_write_apre_sat` (lib/A/Prog/help_witness.v) takes that as its one hypothesis
     `HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd` (api_env's first conjunct, Reusable/YCbq.v:807;
     `tl_errno` of A/ACeg.v:49 discharges it, as_errno B = 0x631b6c).
   The Post at this witness: talk walks the ACK (NLMSG_ERROR, ml = 36, code 0): a0 = 0; the model owes
   [req_write 2 "reac-pw:served"] (len 32 + align4(18) = 52) and next = 1.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem index_of_c talk_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition MODEL_WRITE_A : Z := 0x88100.
Lemma MODEL_WRITE_A_is_entry : MODEL_WRITE_A = LA_model_write. Proof. reflexivity. Qed.

(* the stack bound on image A: the 128-byte frame, the realignment slack of +0x40, and the deepest callee window
   from the realigned sp: index_of's, above talk's and the ESTACK windows of the runtime callees *)
Definition MODEL_WRITE_AFRAME : Z := 128.
Definition MODEL_WRITE_ASLACK : Z := 16.
Definition MODEL_WRITE_AK : Z :=
  MODEL_WRITE_AFRAME + MODEL_WRITE_ASLACK + Z.max INDEX_OF_AK (Z.max TALK_AK ESTACK).
Lemma MODEL_WRITE_AK_val : MODEL_WRITE_AK = 8416. Proof. reflexivity. Qed.

(* the side stack: one class-4 frame (frame_alloc_4 at +0x74) *)
Definition MODEL_WRITE_ASIDE : list (Z * Z) := [(4, 1)].

(* the write set: the model block (talk's, with NULL buffers) *)
Definition model_write_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + MD_SIZE)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the read set: the name and the alias with their NULs, and every interface-table string with its NUL (index_of
   reads them after frame_alloc_4) *)
Definition model_write_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  (aarg regs 1 <> 0 /\ exists s, acstr_at segs m (aarg regs 1) s
       /\ aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s))
  \/ (aarg regs 2 <> 0 /\ exists s, acstr_at segs m (aarg regs 2) s
       /\ aarg regs 2 <= a <= aarg regs 2 + Z.of_nat (length s))
  \/ (exists bs i p s, anlk_at segs m LA_G_NL bs /\ 0 <= i < nk_n_if bs
       /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * i) p /\ acstr_at segs m p s
       /\ p <= a <= p + Z.of_nat (length s)).

Definition model_write_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists mbs kbs tab nm al,
    amodel_at segs m (aarg regs 0) mbs /\ model_wf mbs
    /\ anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at segs m LA_G_NL kbs tab
    /\ astr_arg segs m (aarg regs 1) nm /\ astr_arg segs m (aarg regs 2) al
    (* index_of: the table's shadow, the name and the table strings as the strcmp wrapper asks *)
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab))
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab))
    /\ (forall s, nm = Some s -> astrcmp_arg segs regs MODEL_WRITE_AK m (aarg regs 1) s)
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
          astrcmp_arg segs regs MODEL_WRITE_AK m p n2)
    (* the alias: wrapper_strlen's string (and its slack), checked_memcpy +0x1d4's source *)
    /\ (forall s, al = Some s ->
          Z.of_nat (length s) + 1 < 2 ^ 32
          /\ amem_range (aarg regs 2) (Z.of_nat (length s) + 1)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 2) (Z.of_nat (length s) + 1)
          /\ shadow_hull_vis (ard segs m) (aarg regs 2) (Z.of_nat (length s) + 1)
          /\ apart_frame regs MODEL_WRITE_AK (aarg regs 2) (Z.of_nat (length s) + 1)
          /\ exists slack, abytes segs m (aarg regs 2 + Z.of_nat (length s) + 1) slack
               /\ (- (aarg regs 2 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))
    (* talk: the model block and the chunk queue *)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) MD_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) MD_SIZE
    /\ amem_range (aarg regs 0) MD_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ shadow_hull_vis (ard segs m) (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ apart_gnl LA_G_NL (aarg regs 0) MD_SIZE /\ apart_frame regs MODEL_WRITE_AK (aarg regs 0) MD_SIZE
    (* errno: akept's image clause excepts [as_errno B, as_errno B + 4), so the model block, which the Post gives
       back across the index_of call (the -ENODEV path, +0x168 beqz -> +0x20c), must not be errno bytes *)
    /\ apart (as_errno B) 4 (aarg regs 0) MD_SIZE.

Definition model_write_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall mbs kbs tab nm al,
    amodel_at segs m (aarg regs 0) mbs -> anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
    astr_arg segs m (aarg regs 1) nm -> astr_arg segs m (aarg regs 2) al ->
    let WR := write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs) in
    getr regs' 10 = w64 (w_rc WR)
    /\ (exists mbs', amodel_at segs m' (aarg regs 0) mbs' /\ model_wf mbs'
          /\ md_next mbs' = Z.of_nat (k_next (w_state WR))
          /\ md_socket_errno mbs' = k_sock (w_state WR)
          /\ md_send_errno mbs' = k_send (w_state WR)
          /\ md_reqs mbs' = w_reqs WR /\ md_n_req mbs' = Z.of_nat (length (w_reqs WR))
          /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs).

Definition model_write_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B MODEL_WRITE_A MODEL_WRITE_AK 0 MODEL_WRITE_ASIDE
    model_write_apre model_write_ard model_write_awr model_write_apost.

End c.
