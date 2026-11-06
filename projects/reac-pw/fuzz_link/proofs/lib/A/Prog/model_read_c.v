(* model_read (fuzz_link.c:386-401) on image A (fuzz_link.asan 0x8642c, 776 bytes; listing
   (internal path) (internal record, sha256 5070c0eed28b)): what the harness says a read of
   an interface alias owes. a0 = m (the model block), a1 = name, a2 = kind, a3 = kind_n, a4 = alias, a5 = alias_n. The
   plain contract is lib/Prog/model_read_c.v; this file states the SAME link_spec result (`read_model`) in
   link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x38  push a 128-byte frame (+0x04 sd zero, 0(sp)); save ra, s0..s11
     +0x3c  s0 := the entry sp;  +0x40 andi sp, sp, -0x20 (realign: sp' = sp - 128 or sp - 144);  +0x44 s1 := sp'
     +0x48..+0x58  s4 := alias_n, s3 := alias, s6 := kind_n, s5 := kind, s8 := name;  +0x74 s7 := m
     +0x5c..+0x70  a2 := the side-stack switch cell (.got+0xb8 = 0xa1a28 -> 0xaa440, lw), s9 := the shadow base
                   (.got+0x60 = 0xa19d0 -> 0xaa438)
     +0x78  beqz a2 -> +0x8c (real-stack fallback);  +0x7c..+0x80 frame_alloc_1(0x60) (0x3da88);  +0x84 s2 := F1
     +0x90..+0xb0  s11 := F1;  +0x94 bnez -> +0xb4;  +0x98..+0xb0 the real-stack fallback (alloca of 0x60 bytes)
     +0xb4  sd s11, 0x10(s1) (own frame)
     +0xb8..+0xdc  F1's header: 0x41b58ab3 at F1, the frame descriptor .rodata+0xacc2 at F1 + 8, 0x8642c at F1 + 16
     +0xc4, +0xe4 s10 := shadow(F1);  +0xe0..+0x11c shadow bytes 4..7 := 0xf8 ([F1 + 32, F1 + 64), the request, out
                   of scope), 0..3 := 0xf1 ([F1, F1 + 32)), 8..0xb := 0xf3 ([F1 + 64, F1 + 96))
     +0x120, +0x124  kind = 0 or kind_n = 0 -> +0x13c;  +0x128..+0x134 check;  +0x138 sb zero, 0(kind)
     +0x13c, +0x140  alias = 0 or alias_n = 0 -> +0x158;  +0x144..+0x150 check;  +0x154 sb zero, 0(alias)
     +0x158  a0 := -22;  +0x15c beqz name -> +0x208;  +0x160..+0x16c check;  +0x170 lbu name[0];  +0x174 beqz -> +0x208
     +0x178..+0x17c  index_of(name) (0x86784);  +0x180 beqz a0 -> +0x204 (a0 := -19)
     +0x184  s8 := idx;  +0x188 s9 := r = F1 + 0x20;  +0x18c..+0x198 shadow bytes 4..7 := 0 (the request in scope)
     +0x19c..+0x1a8  checked_memset(r + 12, 0, 20) (0x53214)
     +0x1ac..+0x1c8  sw 32, 0(r); sw 0x10012, 4(r) (type 18, flags 1); sw 1, 8(r); sw idx, 0x14(r): r = req_read idx
     +0x1cc..+0x1e8  talk(m, r, 32, kind, kind_n, alias, alias_n) (0x8763c);  +0x1ec..+0x1fc shadow bytes 4..7 := 0xf8
     +0x208..+0x210  sd 0x45e0360e, 0(F1) (the frame retired);  +0x214 beqz s2 -> +0x268 (fallback only)
     +0x218..+0x258  shadow bytes 0..0xf of F1 := 0xf5 (the whole 128-byte class-1 frame);  +0x25c ld a1, 0x78(F1)
                   (the flag address frame_alloc_1 left at F1 + 128 - 8, YG0d.v astack_malloc_realizes);  +0x260 sb zero, 0(a1):
                   the inline release (astack_free_law; link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2)
     +0x298..+0x2d4  sp := s0 - 0x80; restore; pop; ret.  a0 is -22, -19 or talk's a0 untouched.
   THE REAL-STACK FALLBACK (+0x8c, +0x98..+0xb0, +0x268..+0x294) is not reached: AR's const law holds the switch cell
   at 1 (YG0f.v:194), and with `aside_room Sc [(1, 1)]` frame_alloc_1 returns a side frame (frames_bounds), so
   +0x94 bnez is taken (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2, answer 3).

   THE THREE INSTRUMENTED CHECKS (3 error-path calls), each with its range and the premise that makes it pass:
     1 +0x128..+0x134, +0x2e8..+0x2f4  store1 kind[0] (kind <> 0, kind_n <> 0)   range_addressable kind kind_n
     2 +0x144..+0x150, +0x2f8..+0x304  store1 alias[0] (alias <> 0, alias_n <> 0)   range_addressable alias alias_n
     3 +0x160..+0x16c, +0x2d8..+0x2e4  load1 name[0] (name <> 0)   astrcmp_arg's range_addressable name (|s| + 1)

   Which instruction needs which premise (callee Pres: index_of_c.v `index_of_apre` / `index_of_ard`, talk_c.v
   `talk_apre` / `talk_ard`; the request's facts come from this function's own code, not from its caller):
   - the journal, gp/tp, ret_ok (apre): the frame stores (+0x04..+0x38, +0xb4); frame_alloc_1, checked_memset,
     index_of and talk are applied on it at sp'; +0x2d4 ret.
   - K = 128 + 16 + 8272 = 8416: the 128-byte frame (+0x00), the realignment slack (+0x40), then the deepest callee window from
     sp': index_of's K (INDEX_OF_AK = 8272, the strcmp wrapper's 2 * ESTACK), above talk's TALK_AK = 4240, checked_memset's
     and frame_alloc_1's ESTACK. link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5's 4368 took talk
     as the deepest callee (index_of at 4176 with an ESTACK strcmp) and no slack; the plain K (240) does not carry over.
   - SIDE = [(1, 1)]: frame_alloc_1 (+0x80); index_of and talk take no side frame. `aside_room Sc [(1, 1)]`.
   - EV = 0: no allocator event (frame_alloc_1's path has the empty trace, YG0d.v:296).
   - `amodel_at m mbs`, `model_wf mbs`, `anlk_at g_nl kbs`, `nlk_wf kbs`: talk_apre's; the bytes are kept up to
     +0x1e8 (below). `aiftab_at g_nl kbs tab`: index_of_apre's.
   - `astr_arg name nm`: +0x15c, +0x170 (NULL or empty -> -22); index_of_apre's `aarg 0 <> 0`, `acstr_at`.
   - `abuf_arg` of the two buffers: the stores +0x138, +0x154, then talk_apre's `abuf_arg` (still true after them).
   - index_of's table shadow: `range_addressable (g_nl + NK_IF_NAME) (8 |tab|)` and `(g_nl + NK_IF_INDEX)
     (4 |tab|)`: index_of_apre's.
   - `nm = Some s -> astrcmp_arg regs K name s` (index_of_c.v: 0 < p, |s| + 1 < 2 ^ 32, amem_range,
     range_addressable and shadow_hull_vis of [p, p + |s| + 1), apart_frame regs K): check 3, and index_of_apre's
     `astrcmp_arg regs' INDEX_OF_AK name s` at sp' (apart_frame regs K gives apart_frame regs' INDEX_OF_AK because
     sp - 144 <= sp' and 144 + INDEX_OF_AK = K).
   - each table string p of entry i, for `0 <= p < 2 ^ 64` (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3)
     6a class 2): `astrcmp_arg regs K p n2`: index_of_apre's, by the same window argument.
   - talk's model block and chunk queue: `range_addressable`, `shadow_hull_vis`, `amem_range` of [m, m + MD_SIZE);
     `range_addressable`, `shadow_hull_vis` of [g_nl + NK_CHUNK, + NK_N_CHUNKS); `apart_gnl m`, `apart_frame m`:
     talk_apre's (talk's window [sp' - 4240, sp') lies inside [sp - K, sp)).
   - the buffers (kind <> 0, kind_n >= 1; the same for alias): `apart_gnl`, apart from the model block, from every
     table string and from the name (the plain separations: the stores +0x138, +0x154 come before index_of reads
     the strings and g_nl and before talk reads g_nl and the model), `amem_range`, `range_addressable`,
     `shadow_hull_vis` (checks 1, 2 and talk_apre's buffer clause), `apart_frame` (the frame stores; talk_apre's),
     and the two buffers apart from each other (talk_apre's).
   - NOT asked of the caller: the name apart from the model block (model_unmark passes m->mark[i], inside the block:
     LLVMFuzzerTestOneInput 0x82fd8 with a1 = s7 = m + MD_MARK + 16 i); the name is read before talk writes the
     block, and talk does not write the marks. Nor the table strings apart from the model block (read before).
   - the bytes kept up to the two calls: own frame stores (apart_frame), F1's header and shadow stores (F1 was a free
     frame, so it meets no byte of the read set, by akb, and no byte of the write set, by ajw), the NUL stores
     (the buffer separations above). The request r: built by +0x188..+0x1c8 in F1, its shadow zeroed by
     +0x18c..+0x198; talk_apre's `abytes r (req_read idx)`, `len = 32 <= 512`, `amem_range`, `range_addressable`,
     `shadow_hull_vis` of [r, r + 32) (F1's shadow is a client range, am_client), `apart r 32 m MD_SIZE` and
     `apart_frame r 32` (a side frame is apart from heap blocks and from the real stack) come from the code and the
     journal; talk_ard's [r, r + 32) is akb because (1, p1) is in the frames at the call.
   - the write set [(m, m + MD_SIZE); aivl kind kind_n; aivl alias alias_n] and apre's `ajw` on it: talk's write
     set, and the stores +0x138, +0x154. F1 and its shadow are not in it (taken and released inside the call,
     link-a/form/FORM.md (internal record, sha256 13aeff774164) section 2), nor the flag byte +0x260 (the runtime's).
   - `apart (as_errno B) 4` of the model block and of each buffer (the kernel-call walk's model_write walk, 2026-10-30):
     on the -ENODEV path (+0x180 `beqz a0` after index_of -> +0x204) the Post gives the model block back and the
     two NUL stores (+0x138, +0x154) back across the index_of call, and index_of's `apost` gives them only through
     `akept`, whose image clause excepts [as_errno B, as_errno B + 4). The Pre locates these bytes nowhere (a write
     set is placed by `ajw`, which admits a byte of G), so without this the statement allows them to BE errno and
     the Post does not follow. Stated over the whole object, because the Post also gives `abuf m' buf cap`. True at
     every call site: the block is the calloc'd heap block and the buffers are slots of LLVMFuzzerTestOneInput's
     class-4 side frame or NULL, while errno is an image byte (tp - 164).
   - the read set Rd (`aleaf_rd`): the name and its NUL (+0x170, and index_of's strcmp), and every interface-table
     string with its NUL (index_of's strcmp). The table strings are read through pointers loaded from g_nl, not
     through an argument, but frame_alloc_1 (+0x80) runs BEFORE index_of reads them: a string in a free class-1
     frame would be handed out as F1 and overwritten by the header stores +0xd4..+0xdc, so they are in Rd, and
     their akb at the call is what index_of's result at the entry memory needs. A table entry's pointer is the
     `au64_at` value, whose range `acstr_at` fixes (0 <= p, p + |s| + 1 <= 2 ^ 64). The name's akb at the call
     gives index_of_ard's at +0x17c (the frames grow by (1, p1); the window shrinks to index_of's).

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 240` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a: the window is on
     the real stack above alloc_ceiling, g_nl is an image byte).
   - `wz` is written `w64` (the same Z_to_bv 64; -22 and -19 by addi, sign-extended).
   The plain separations carry over unchanged in content; nothing of the plain Post is false of image A (it has no
   `m' = m`; the frame and side-frame changes are what akept allows).
   Released proofs (rule 24): none of model_read (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): no hit
   on any of the four refs).

   CALL SITES (link-a/facts/asan-set.tsv (internal record, sha256 e26bb6a28c00): LLVMFuzzerTestOneInput only), F4 = LLVMFuzzerTestOneInput's class-4 side frame (+0x70):
   - 0x8368c (op_read): a0 = ld 0xe8(s1) = m; a1 = s6 = name_of's answer (g_names[s], odd[s % 6] or NULL);
     a2 = kc ? WK : 0 with WK = F4 + 0x2e0 (+0x2d0), a3 = kc <= 39 (+0xd40..+0xd58; ac at +0xd84..+0xd9c);
     a4 = ac ? WA : 0, WA = F4 + 0x330, a5 = ac <= 39; WK, WA 40 bytes each, zeroed by checked_memset (+0xe58,
     +0xe80), shadow cleared (+0xe34..+0xe44,
     +0xe5c..+0xe6c).
   - 0x833d4 (model_mark): a1 = s4, non-NULL and non-empty (+0xb38..+0xb50); a2 = F4 + 0x160, a3 = 32; a4 =
     F4 + 0x1a0, a5 = 256; shadow cleared (+0xb54..+0xbe0); the bytes uninitialised (abuf holds of any junk).
   - 0x82fd8 (model_unmark): a1 = s7 = m->mark[i] (inside the model block, terminated by model_marks_wf);
     a2 = a3 = 0; a4 = s10 = F4 + 0x20 (+0x2b8), a5 = 256; shadow cleared (+0x76c..+0x7e8).
   At each: the names are image bytes (g_names in .bss, odd's strings in .rodata) or model-block bytes (a heap block
   of Sc), and so are the table strings: akb; the buffers lie in F4 (own; `ajw`), the model block is a block calloc'd
   after the journal began (`ajw` by in_tmp_block); all are outside [sp - K, sp) and apart as the Pre asks.

   Satisfiability witness (the closed lemma `model_read_apre_sat` of lib/A/Prog/help_witness.v, run R: op_read of
   "nl0" as the first op, kernel() made one 36-byte ACK chunk; talk_c.v's witness uses a 40-byte chunk with an
   IFLA_IFALIAS "ab" instead: model_read's Pre reads no chunk byte, so it holds at both), at 0x8368c:
   - registers: ra = 0x83690; sp = 0x7fffffffee60 (LLVMFuzzerTestOneInput's realigned sp from SP0 = 0x7ffffffff000;
     mod 16 = 0); a0 = M (the calloc(1, 8856) block; the lemma has 0x602000001000); a1 = 0x62fac0 (g_names[0] =
     "nl0"); a2 = WK = F4 + 0x2e0, a3 = 16; a4 = WA = F4 + 0x330, a5 = 16 (F4 = frame_addr ly 4 p4; the lemma has
     0x7f0000002000).
   - memory: M all 0 (model_wf); g_nl as in talk_c.v's witness (n_if 64: g_names[k] = "nl<k>" for k < 64,
     k mod 16 <> 15, index k + 2, then odd[1..4] with 101..104; nlk_wf; aiftab_at with |tab| = 64 <= 80);
     g_names' slots "nl<k>" then zeros; WK, WA 40 zero bytes. nm = Some "nl0", index_of tab "nl0" = 2.
   - conjunct by conjunct: amodel_at, model_wf, anlk_at, nlk_wf, aiftab_at: as above; astr_arg: 0x62fac0 <> 0 and
     "nl0" with its NUL; abuf_arg: WK, WA 40 >= 16 bytes present and writable; the table shadow: g_nl's object
     shadow is 0; astrcmp_arg of "nl0": 0 < 0x62fac0, 4 < 2 ^ 32, 0x62fac0 + 4 <= kLowMemEnd - 1, g_names'
     object shadow 0 and visible, 0x62fac0 + 4 <= sp - 8416; each table string: g_names[k] the same, odd[1..4]
     .rodata string literals (instrumented globals, their bytes addressable), each in low memory and below the
     window; M, the queue: shadow 0, visible, M + 8856 <= kHighMemEnd - 1 and kHighMemBeg <= M, M a heap block
     apart from g_nl and the real stack; WK, WA: shadow 0 (cleared above), visible (am_client), in high memory,
     apart from g_nl, M, each other, every table string and "nl0" (fake stack vs image and heap), outside the window.
   - the A-state: as talk_c.v's witness with own = frames Sc = [(4, p4)]; `aside_room Sc [(1, 1)]`: count_cid
     1 = 0, 0 + 1 <= fs_frames 1 = 8192; Rd: "nl0" and the table strings are image bytes outside the runtime's
     statics and errno (akb's image clause; the instance's check of as_owned_static, link-a/form/WITNESS.md
     (internal record, sha256 b8aaf8151f7f) section 1); `ajw` on M, WK, WA as in talk_c.v's witness; st_nev S + k + 0 <= EV_MAX.
   - the errno separations: M, WK and WA are above kLowMemEnd and errno is an image byte below it, so each holds by
     its left disjunct. The closed lemma `model_read_apre_sat` (lib/A/Prog/help_witness.v) takes that as its one
     hypothesis `HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd` (api_env's first conjunct,
     Reusable/YCbq.v:807; `tl_errno` of A/ACeg.v:49 discharges it, as_errno B = 0x631b6c).
   The Post at run R: a0 = 0; r_kind = r_alias = "" (WK[0] = WA[0] = 0, kept by talk: the ACK carries no
   attribute); the model owes [req_read 2] and next = 1. (At talk_c.v's run, r_alias = "ab".)
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem index_of_c talk_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition MODEL_READ_A : Z := 0x8642c.
Lemma MODEL_READ_A_is_entry : MODEL_READ_A = LA_model_read. Proof. reflexivity. Qed.

(* the stack bound on image A: the 128-byte frame, the realignment slack of +0x40, and the deepest callee window
   from the realigned sp: index_of's, above talk's, checked_memset's and frame_alloc_1's *)
Definition MODEL_READ_AFRAME : Z := 128.
Definition MODEL_READ_ASLACK : Z := 16.
Definition MODEL_READ_AK : Z :=
  MODEL_READ_AFRAME + MODEL_READ_ASLACK + Z.max INDEX_OF_AK (Z.max TALK_AK ESTACK).
Lemma MODEL_READ_AK_val : MODEL_READ_AK = 8416. Proof. reflexivity. Qed.

(* the side stack: one class-1 frame (frame_alloc_1 at +0x80) *)
Definition MODEL_READ_ASIDE : list (Z * Z) := [(1, 1)].

(* the write set: talk's (the model block and the two buffers, which a NULL pointer does not own) *)
Definition model_read_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + MD_SIZE); aivl (aarg regs 2) (aarg regs 3); aivl (aarg regs 4) (aarg regs 5)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the read set: the name and its NUL, and every interface-table string with its NUL (index_of reads them after
   frame_alloc_1) *)
Definition model_read_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  (aarg regs 1 <> 0 /\ exists s, acstr_at segs m (aarg regs 1) s
       /\ aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s))
  \/ (exists bs i p s, anlk_at segs m LA_G_NL bs /\ 0 <= i < nk_n_if bs
       /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * i) p /\ acstr_at segs m p s
       /\ p <= a <= p + Z.of_nat (length s)).

Definition model_read_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists mbs kbs tab nm,
    amodel_at segs m (aarg regs 0) mbs /\ model_wf mbs
    /\ anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at segs m LA_G_NL kbs tab
    /\ astr_arg segs m (aarg regs 1) nm
    /\ abuf_arg segs m (aarg regs 2) (aarg regs 3) /\ abuf_arg segs m (aarg regs 4) (aarg regs 5)
    (* index_of: the table's shadow, the name and the table strings as the strcmp wrapper asks *)
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab))
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab))
    /\ (forall s, nm = Some s -> astrcmp_arg segs regs MODEL_READ_AK m (aarg regs 1) s)
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
          astrcmp_arg segs regs MODEL_READ_AK m p n2)
    (* talk: the model block and the chunk queue *)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) MD_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) MD_SIZE
    /\ amem_range (aarg regs 0) MD_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ shadow_hull_vis (ard segs m) (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ apart_gnl LA_G_NL (aarg regs 0) MD_SIZE /\ apart_frame regs MODEL_READ_AK (aarg regs 0) MD_SIZE
    (* the two buffers: checks 1 and 2, talk's buffer clauses, the plain separations *)
    /\ (aarg regs 2 <> 0 -> apart_frame regs MODEL_READ_AK (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> apart_frame regs MODEL_READ_AK (aarg regs 4) (aarg regs 5))
    (* errno: akept's image clause excepts [as_errno B, as_errno B + 4), so the bytes the Post gives back across
       the index_of call (the -ENODEV path, +0x180 beqz -> +0x204) must not be errno bytes *)
    /\ apart (as_errno B) 4 (aarg regs 0) MD_SIZE
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> apart (as_errno B) 4 (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> apart (as_errno B) 4 (aarg regs 4) (aarg regs 5))
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 ->
          apart_gnl LA_G_NL (aarg regs 2) (aarg regs 3)
          /\ apart (aarg regs 2) (aarg regs 3) (aarg regs 0) MD_SIZE
          /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                apart (aarg regs 2) (aarg regs 3) p (Z.of_nat (length n2) + 1))
          /\ amem_range (aarg regs 2) (aarg regs 3)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 2) (aarg regs 3)
          /\ shadow_hull_vis (ard segs m) (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 ->
          apart_gnl LA_G_NL (aarg regs 4) (aarg regs 5)
          /\ apart (aarg regs 4) (aarg regs 5) (aarg regs 0) MD_SIZE
          /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                apart (aarg regs 4) (aarg regs 5) p (Z.of_nat (length n2) + 1))
          /\ amem_range (aarg regs 4) (aarg regs 5)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 4) (aarg regs 5)
          /\ shadow_hull_vis (ard segs m) (aarg regs 4) (aarg regs 5))
    /\ (forall s, nm = Some s ->
          (aarg regs 2 <> 0 -> 1 <= aarg regs 3 ->
             apart (aarg regs 2) (aarg regs 3) (aarg regs 1) (Z.of_nat (length s) + 1))
          /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 ->
             apart (aarg regs 4) (aarg regs 5) (aarg regs 1) (Z.of_nat (length s) + 1)))
    /\ (aarg regs 2 <> 0 -> aarg regs 4 <> 0 -> 1 <= aarg regs 3 -> 1 <= aarg regs 5 ->
          apart (aarg regs 2) (aarg regs 3) (aarg regs 4) (aarg regs 5)).

Definition model_read_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall mbs kbs tab nm,
    amodel_at segs m (aarg regs 0) mbs -> anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
    astr_arg segs m (aarg regs 1) nm ->
    let RR := read_model tab nm (aarg regs 3) (aarg regs 5) (md_reqs mbs) (md_kstate mbs kbs) in
    getr regs' 10 = w64 (r_rc RR)
    /\ (exists mbs', amodel_at segs m' (aarg regs 0) mbs' /\ model_wf mbs'
          /\ md_next mbs' = Z.of_nat (k_next (r_state RR))
          /\ md_socket_errno mbs' = k_sock (r_state RR)
          /\ md_send_errno mbs' = k_send (r_state RR)
          /\ md_reqs mbs' = r_reqs RR /\ md_n_req mbs' = Z.of_nat (length (r_reqs RR))
          /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs)
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> acstr_at segs m' (aarg regs 2) (r_kind RR))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> acstr_at segs m' (aarg regs 4) (r_alias RR))
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> abuf segs m' (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> abuf segs m' (aarg regs 4) (aarg regs 5)).

Definition model_read_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B MODEL_READ_A MODEL_READ_AK 0 MODEL_READ_ASIDE
    model_read_apre model_read_ard model_read_awr model_read_apost.

End c.
