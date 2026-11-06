(* reac_link_alias_read (reac_link_alias.c:95-119) on image A (fuzz_link.asan 0x8867c, 760 bytes; listing
   (internal path) (internal record, sha256 7c23ed8f465f)): the library reads one
   netdev's link kind and interface alias over rtnetlink. a0 = name, a1 = kind, a2 = kind_n, a3 = alias, a4 = alias_n.
   The plain contract is lib/Prog/reac_link_alias_read_c.v; this file states the SAME link_spec result (`read_lib`)
   in link_amem.v's read-set form `aleaf_rd` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 11).

   The image-A code, in order:
     +0x00..+0x34  push a 128-byte frame (+0x04 probes it); save ra, s0..s10
     +0x38  s0 := the entry sp;  +0x3c `andi sp, sp, -0x20` (sp down by 0 or 16);  +0x40 s1 := sp
     +0x44..+0x50  s4 := alias_n, s3 := alias, s6 := kind_n, s5 := kind;  +0x6c s7 := name
     +0x54..+0x68  the side-stack switch (.got+0xb8) and the shadow base (.got+0x60, into s8)
     +0x70  `beqz a2` -> the real-stack arm +0x84..+0xa8 (a 96-byte frame carved below sp)
     +0x74..+0x78  frame_alloc_1(0x60 = 96) (0x3da88): the class-1 side frame (128 bytes), into s2 and s10
     +0xac..+0xd4  the frame's magic, descriptor 0x12dc7 and pc stored at s10 + 0, 8, 16
     +0xd8..+0x114  its shadow: 0xf1 x 4 (left redzone [s10, s10 + 32)), 0xf8 x 4 (the 32-byte request
                   [s10 + 32, s10 + 64), out of scope), 0xf3 x 4 (right redzone [s10 + 64, s10 + 96))
     +0x118..+0x130  kind <> 0 and kind_n <> 0: the instrumented check of the 1-byte store to kind (its shadow byte s;
                   s = 0 passes, else kind & 7 < s passes, else errpath_store1 0x5a63c at +0x2e4); `sb zero, 0(kind)`
     +0x134..+0x14c  the same for alias (+0x2e8..+0x2f4)
     +0x150  a0 := -22;  +0x154 `beqz name` -> +0x1fc
     +0x158..+0x164  the instrumented check of the 1-byte load of name[0] (errpath_load1 0x5a31c at +0x2d4);
                   +0x168 `lbu`; +0x16c `beqz` -> +0x1fc
     +0x170..+0x174  fuzz_if_nametoindex(name) (0x826cc); +0x178 `beqz` -> +0x1f8 (a0 := -19)
     +0x180..+0x190  s8 := s10 + 32 (the request); its 4 shadow bytes := 0 (in scope)
     +0x194..+0x1a0  checked_memset(req + 12, 0, 20) (0x53214)
     +0x1a4..+0x1c0  len 32, type 18 (RTM_GETLINK) with flags 1 (NLM_F_REQUEST), seq 1, ifi_index stored into req
     +0x1c4..+0x1dc  nl_talk(req, 32, kind, kind_n, alias, alias_n) (0x88974); its a0 is the answer
     +0x1e0..+0x1f0  the request's shadow := 0xf8 (out of scope)
     +0x1fc..+0x204  the retired magic 0x45e0360e stored at s10
     +0x208  `beqz s2` -> +0x25c (real-stack arm: the frame's 12 shadow bytes := 0)
     +0x20c..+0x24c  the 16 shadow bytes of the 128-byte frame := 0xf5;  +0x250..+0x254 `ld a1, 0x78(s2);
                   sb zero, 0(a1)`: the frame's flag := 0 (the inline release, astack_free_law YG0d.v:308-316)
     +0x28c..+0x2c4  restore s0..s10, ra; pop; ret (a0 as set above).

   The real-stack arm is not taken under the premises (link-a/form/FORM.md (internal record, sha256 13aeff774164) section
   4.2): AR's const law holds the switch cell at 1 and `aside_room Sc [(1, 1); ...]` gives frame_alloc_1 a frame.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok, the window (apre): the frame stores +0x04..+0x34 in [sp - 128, sp); +0x2c4 ret.
   - K = 128 + 16 + NL_TALK_AK = 8592: the frame, the realignment slack of +0x3c, nl_talk's 8448 (nl_talk_c.v), the
     deepest callee window. The others: fuzz_if_nametoindex 80 + 2 * ESTACK = 8272 (its strcmp wrapper's window is
     2 * ESTACK, pcap Reusable/AStrcmpDef.v), checked_memset and frame_alloc_1 ESTACK. The plain K
     (16672) does not carry over.
   - SIDE = [(1, 1); (9, 1)]: the own class-1 frame, then nl_talk's class-9 frame while it is live. EV = 0.
   - `abuf_arg` of both buffers and, when the buffer is there, `achk` (amem_range, range_addressable,
     shadow_hull_vis): the checks +0x120..+0x12c, +0x13c..+0x148 (range_addressable of the first byte), the two
     `sb zero` (writable), and nl_talk's Pre on the buffers (nl_talk_c.v), which this function passes on unchanged;
     `apart_frame regs K` of each buffer: the frame stores, and nl_talk's `apart_frame regs NL_TALK_AK` at the
     realigned sp; `apart kind kind_n alias alias_n`, `apart_gnl`, apart from errno: nl_talk's.
   - `astr_arg m name nm`; for `nm = Some s`: `achk m name (|s| + 1)`, `|s| + 1 < 2 ^ 32` and the TAIL (every byte
     after the NUL up to the end of its 8-byte granule visible): the check +0x158..+0x164 and fuzz_if_nametoindex's
     strcmp wrapper (fuzz_if_nametoindex_apre's `astrcmp_arg_ni`:
     0 < p, |s| + 1 < 2 ^ 32, amem_range, range_addressable, shadow_hull_vis, apart_frame, and the tail clause of
     link's strcmp contract, lib/A/Rt/RtString.v astrcmp_realizes `atail_vis`, RtDefs.v:54-55: musl's strcmp under
     the interceptor may read word-wise); `apart_frame regs K name`, `apart_gnl`, apart from the buffers (the plain
     separations): the stores before +0x174 keep it.
   - the interface table: `anlk_at`, `aiftab_at m LA_G_NL kbs tab`, g_nl's shadow usable and visible
     (fuzz_if_nametoindex's checks of the if_name / if_index slots, +0x6c..+0x74 and +0xac..+0xb8 of its listing,
     and nl_talk's Pre); per string p of the table, the plain separations (frame, g_nl, errno, buffers) and, for the
     p `au64_at` fixes in [0, 2 ^ 64), `0 < p`, `|n2| + 1 < 2 ^ 32`, `achk m p (|n2| + 1)` and the same tail clause:
     the strcmp wrapper (`astrcmp_arg_ni` again). The positive clause is stated for 0 <= p < 2 ^ 64
     only: `au64_at` fixes p modulo 2 ^ 64 (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a), and
     `amem_range` is false of p + 2 ^ 64; the separations hold of an out-of-range p trivially.
   - THE TAIL BYTES ARE A VISIBILITY PREMISE AT ENTRY, NOT IN THE READ SET (the library walks' integration build,
     2026-10-30: without the clause the call +0x174 cannot meet `astrcmp_arg_ni`). Their values enter no Post. After
     an `odd` string in .rodata they are its registered global's redzone, bytes of `as_owned_static` where `akb`'s
     image clause fails (AF0m.v Tfib_owned_static: (0x20fc1, 0x1f) after odd[0] "", (0x20fec, 0x14), (0x21005, 0x1b),
     (0x21026, 0x1a), (0x21049, 0x17) after odd[1..4], (0x21066, 0x1a) after odd[5] "gone0"; name_of reaches all six,
     LLVMFuzzerTestOneInput +0xcd8..+0xd10, +0xfc0..+0xff8), so naming them in Rd would make the Pre false at every
     call with such a name; after a g_names entry they lie inside its own 8-byte entry; after a name in a caller's
     buffer (reac_served_unmark_all passes a slot of its marks block) inside the block or its 8-byte chunk tail,
     which that caller states visible (`amk_block_ok`). Their
     visibility at the call +0x174 follows from the premise at entry as in the mark contracts' account
     (reac_served_mark_c.v, open item W6): at tfibsegs mbyte falls back to
     seg_rom (YP09.v:18-22), seg_rom is Some on all of the image (AB13.v:148 tfib_rom_all) and image bytes are never
     hidden (YK04.v:38 H_off_segments); at the abstract segments the post-NUL bytes of the registered literals are
     owned redzones that AF0m pins as const cells (AR's `am_const`), and a g_names entry's tail is in neither a write
     set nor the owned list, so `akept`'s image clause keeps it.
   - `anlk_at`, `nlk_wf`, `nk_open = 0`, the two count bounds, errno (`aerrno_ok`, nl_talk_c.v): nl_talk's Pre.
   - the READ SET (`reac_link_alias_read_ard`): the name's bytes through its NUL (when name <> 0) and every table
     string's bytes through its NUL. frame_alloc_1 (+0x78) changes the runtime's bytes and +0xcc..+0x114 store into
     the frame it hands out and its shadow BEFORE fuzz_if_nametoindex reads the name and the table at +0x174; with
     the read set `akb` (the bytes akept keeps) a free side frame or free heap holding them is excluded. It also
     makes apost's akept keep the table strings, which the Post's `aiftab_at m' kbs' tab` re-states.
   - the write set: g_nl's [LA_G_NL, LA_G_NL + NK_N_SENT + 4) (nl_talk's callees) and the two buffers (`aivl`).

   What does NOT carry over from the plain text:
   - errno in the write set (as nl_talk_c.v: `ajw` would be false of it; the journal and akept let errno change);
     `errno_at regs` is `as_errno B` with `as_errno B = as_tp B - 164`.
   - `frame_apart_gnl regs 16672` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a). The plain K.
   Every plain Post conjunct carries over unchanged in content, over the A views.

   Satisfiability witness (a run; lib/A/Prog/alib_witness.v `reac_link_alias_read_apre_sat` closes the
   function-specific part at a memory holding these values): LLVMFuzzerTestOneInput's call at 0x836a8 (op_read) in
   the run of link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1. Registers: ra = 0x836ac; a0 = the
   name op_read takes from its names table, an image string (the lemma: g_names[2] = "nl2" at LA_G_NAMES + 16, .bss);
   a1, a3 = the two text_buf(16) blocks of 0x835f4 / 0x83600 (malloc(17), 17 bytes 0x5a), a2 = a4 = 16;
   sp = LLVMFuzzerTestOneInput's sp; gp, tp the image's. Memory: g_nl as interfaces() and kernel() leave it before the
   socket opens (open = opened = closed = misuse = 0, socket_errno = send_errno = 0, end_errno one of nl_errno's 105, 4,
   11, 1, 24, 111, one queued chunk) with the table interfaces() builds (fuzz_link.c:86-100): n_if = 64; for k = 0 .. 62
   with k mod 16 <> 15 the next entry is g_names[k] = "nl<k>" (.bss, LA_G_NAMES + 8 k) with index k + 2 (60 entries),
   then odd[1..4] (.rodata strings at 0x20fe0, 0x21000, 0x21020, 0x21040, the words of LA_ODD) with indices 101 .. 104;
   so entry 2 is "nl2" with index 4. errno 0 at 0x631b6c; every shadow byte a `range_addressable` premise reads is 0
   (g_nl, g_names and errno: the instance's zero shadow; blocks: the chunk shadow of their first 16 bytes) or, in the
   last granule of an odd string (an instrumented .rodata global), that string's size mod 8, which `saddr_ok` accepts
   for every byte of the string and its NUL (0x04, 0x05, 0x06, 0x01 at shadow(0x20fe8), shadow(0x21000),
   shadow(0x21020), shadow(0x21048): the const shadow cells of lib/A/AF0m.v
   lines 821, 824, 828, 832); every byte of a `shadow_hull_vis` hull is visible (a block's hull also covers its last
   granule, shadow 1, and its redzone). The journal: LLVMFuzzerTestOneInput's with G = LA_G (`ajw` of g_nl by
   `inG`, of the blocks by `in_tmp_block`); own = [(4, p4)], frames S = [], so `aside_room Sc [(1, 1); (9, 1)]` is
   0 + 1 <= 8192 and 0 + 1 <= 32 (fs_frames c = 2 ^ (14 - c), YG00.v:565); the read set (the name and the 64 table
   strings, in g_names and .rodata, through their NULs) is `akb` by the image clause: the instance's
   as_owned_static (AF0m.v Tfib_owned_static at 4a315fd508ce) meets none of those bytes, nor g_nl or errno (its rows
   by the odd strings start right after each NUL: the redzones); `st_nev S + k <= EV_MAX` as in link-a/form/WITNESS.md
   (internal record, sha256 b8aaf8151f7f) section 1.

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem nl_talk_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_READ_A : Z := 0x8867c.
Lemma REAC_LINK_ALIAS_READ_A_is_entry : REAC_LINK_ALIAS_READ_A = LA_reac_link_alias_read.
Proof. reflexivity. Qed.

(* the stack bound on image A: the 128-byte frame, the realignment slack of +0x3c, nl_talk's window *)
Definition REAC_LINK_ALIAS_READ_AFRAME : Z := 128.
Definition REAC_LINK_ALIAS_READ_ASLACK : Z := 16.
Definition REAC_LINK_ALIAS_READ_AK : Z :=
  REAC_LINK_ALIAS_READ_AFRAME + REAC_LINK_ALIAS_READ_ASLACK + NL_TALK_AK.
Lemma REAC_LINK_ALIAS_READ_AK_val : REAC_LINK_ALIAS_READ_AK = 8592. Proof. reflexivity. Qed.

(* the side-stack room: the own class-1 frame and nl_talk's class-9 frame *)
Definition REAC_LINK_ALIAS_READ_ASIDE : list (Z * Z) := [(1, 1); (9, 1)].

(* the write set: g_nl up to n_sent, and the two buffers, which a NULL pointer does not own *)
Definition reac_link_alias_read_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4); aivl (aarg regs 1) (aarg regs 2); aivl (aarg regs 3) (aarg regs 4)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the read set: the name through its NUL, and every interface-table string through its NUL *)
Definition reac_link_alias_read_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  (aarg regs 0 <> 0 /\ exists s, acstr_at segs m (aarg regs 0) s /\
     aarg regs 0 <= a <= aarg regs 0 + Z.of_nat (length s))
  \/ (exists bs tab i n2 ix p, anlk_at segs m LA_G_NL bs /\ aiftab_at segs m LA_G_NL bs tab /\
        nth_error tab i = Some (n2, ix) /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\
        acstr_at segs m p n2 /\ p <= a <= p + Z.of_nat (length n2)).

Definition reac_link_alias_read_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs tab nm,
    anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ nk_open kbs = 0
    /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ aiftab_at segs m LA_G_NL kbs tab
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ aerrno_ok segs B REAC_LINK_ALIAS_READ_AK regs m
    /\ astr_arg segs m (aarg regs 0) nm
    /\ abuf_arg segs m (aarg regs 1) (aarg regs 2) /\ abuf_arg segs m (aarg regs 3) (aarg regs 4)
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
          apart_frame regs REAC_LINK_ALIAS_READ_AK p (Z.of_nat (length n2) + 1)
          /\ apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1)
          /\ apart (as_errno B) 4 p (Z.of_nat (length n2) + 1)
          /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
                apart p (Z.of_nat (length n2) + 1) (aarg regs 1) (aarg regs 2))
          /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
                apart p (Z.of_nat (length n2) + 1) (aarg regs 3) (aarg regs 4))
          /\ (0 <= p < 2 ^ 64 -> 0 < p /\
                Z.of_nat (length n2) + 1 < 2 ^ 32 /\ achk segs m p (Z.of_nat (length n2) + 1)
                /\ (forall a, p + Z.of_nat (length n2) < a
                              < p + Z.of_nat (length n2) - (p + Z.of_nat (length n2)) mod 8 + 8 ->
                      ard segs m a <> None)))
    /\ (forall s, nm = Some s ->
          (aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
             apart (aarg regs 0) (Z.of_nat (length s) + 1) (aarg regs 1) (aarg regs 2))
          /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
             apart (aarg regs 0) (Z.of_nat (length s) + 1) (aarg regs 3) (aarg regs 4)))
    /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
          apart (aarg regs 1) (aarg regs 2) (aarg regs 3) (aarg regs 4))
    /\ (aarg regs 1 <> 0 -> apart (as_errno B) 4 (aarg regs 1) (aarg regs 2))
    /\ (aarg regs 3 <> 0 -> apart (as_errno B) 4 (aarg regs 3) (aarg regs 4))
    /\ (forall s, nm = Some s ->
          apart_frame regs REAC_LINK_ALIAS_READ_AK (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ apart_gnl LA_G_NL (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ achk segs m (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ (forall a, aarg regs 0 + Z.of_nat (length s) < a
                        < aarg regs 0 + Z.of_nat (length s) - (aarg regs 0 + Z.of_nat (length s)) mod 8 + 8 ->
                ard segs m a <> None))
    /\ (aarg regs 1 <> 0 -> apart_frame regs REAC_LINK_ALIAS_READ_AK (aarg regs 1) (aarg regs 2)
          /\ apart_gnl LA_G_NL (aarg regs 1) (aarg regs 2))
    /\ (aarg regs 3 <> 0 -> apart_frame regs REAC_LINK_ALIAS_READ_AK (aarg regs 3) (aarg regs 4)
          /\ apart_gnl LA_G_NL (aarg regs 3) (aarg regs 4))
    /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> achk segs m (aarg regs 1) (aarg regs 2))
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> achk segs m (aarg regs 3) (aarg regs 4)).

Definition reac_link_alias_read_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall kbs tab nm,
    anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab -> astr_arg segs m (aarg regs 0) nm ->
    let R := read_lib tab nm (aarg regs 2) (aarg regs 4) (nk_sent kbs) (nk_kstate kbs) in
    getr regs' 10 = w64 (r_rc R)
    /\ (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at segs m' LA_G_NL kbs' tab
          /\ nk_next kbs' = Z.of_nat (k_next (r_state R))
          /\ nk_socket_errno kbs' = k_sock (r_state R)
          /\ nk_send_errno kbs' = k_send (r_state R)
          /\ nk_sent kbs' = r_reqs R /\ nk_n_sent kbs' = Z.of_nat (length (r_reqs R))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
          /\ ((nm = None \/ nm = Some [] \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                nk_opened kbs' = nk_opened kbs))
    /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> acstr_at segs m' (aarg regs 1) (r_kind R))
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> acstr_at segs m' (aarg regs 3) (r_alias R))
    /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> abuf segs m' (aarg regs 1) (aarg regs 2))
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> abuf segs m' (aarg regs 3) (aarg regs 4)).

Definition reac_link_alias_read_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B REAC_LINK_ALIAS_READ_A REAC_LINK_ALIAS_READ_AK 0 REAC_LINK_ALIAS_READ_ASIDE
    reac_link_alias_read_apre reac_link_alias_read_ard reac_link_alias_read_awr reac_link_alias_read_apost.

End c.
