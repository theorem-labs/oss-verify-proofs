(* layer.asan.alloc (contracts/asan/alloc.asan.md (a working note, not in this delivery), owner a Theorem Labs lane): the ASan allocator of this image, at the
   trampolines that program code calls (__interceptor_trampoline_malloc, _free, _realloc, _calloc) and at the bodies
   ___interceptor_malloc / ___interceptor_free that the runtime's own wrappers call. Stated over this build's asan
   engine (Reusable/ of this directory), whose cut includes the class-full instruction (frame.asan W7): a request whose
   size class is full ends its execution there, so every entry returns a block. Statements only; the frame's ASan
   layer proves them (frame.asan D4, contracts/asan/FRAME.md). Written by startcert/acontract.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YK0s YM05 YM06 YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ClassConsDef.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* The image's entries and runtime cells (nm.txt of the unstripped twin; tp: x4 of the checked main-entry state). *)
Record asan_syms := ASyms {
  as_malloc : Z; as_malloc_body : Z;
  as_malloc_inner : Z;  (* asan_malloc: the entry fuzz_command's strdup wrapper calls directly (claim A) *)
  as_free : Z; as_free_body : Z; as_realloc : option Z; as_calloc : option Z;
  as_oom : Z;          (* OOM(I): the runtime's 1-byte out-of-memory flag *)
  as_tp : Z;           (* the thread pointer *)
  as_mcs : Z;          (* the allocator's setting malloc_context_size (u32; its value at main is the image's, from the
                          checked hand-off state: 30 or 1; struct.asan.heap AH8) *)
  as_mrn : Z           (* the allocator's setting allocator_may_return_null (u8, 1 at main; AH8) *)
}.
Definition ASYMS : asan_syms := ASyms 0x534b8 0x5368c 0x32314 0x534b4 0x534bc None None 0x12b920 0x5dc650 0xaa3bc 0x12b921.
Definition a_errno (B : asan_syms) : Z := as_tp B - 164.   (* musl errno_val: tp - 164 *)
(* Client data: the .data/.bss objects of musl, the harness and the program (not the runtime's, not libunwind's),
   merged (startcert/acontract.py client_ranges). *)
Definition a_client : list (Z * Z) := [(0x9f580, 4576); (0xa07e8, 16); (0xa1550, 24); (0xa1578, 32); (0xa15b8, 24); (0xa25e8, 8); (0xa4e60, 32); (0xa4e98, 776); (0xa6008, 73); (0x5cbd10, 65584); (0x5dc580, 120); (0x5dc600, 72); (0x5dc664, 20); (0x5dc680, 131728); (0x5fc918, 4320); (0x5fda00, 1328)].

(* Stack bounds below the entry sp (alloc.asan.md # Stack): the runs end at R or at a cut, and the cut at
   class_full_at comes before the class-full message, so the bound covers the block arm only (tool bounds 2992, 3360,
   3440, 3040); 4096 is the window of the released allocator proof (AMALLOC_STACK, AFREE_STACK). *)
Definition AK_MALLOC : Z := 4096.
Definition AK_FREE : Z := 4096.
Definition AK_REALLOC : Z := 4096.
Definition AK_CALLOC : Z := 4096.
(* asan_malloc's own bound (claim A, K_A; block arm) and the caller's trace record (compiler-rt BufferedStackTrace:
   trace pointer at +0, size at +8, tag at +12, trace_buffer[255] at +16, top_frame_bp at +2056). *)
Definition AK_INNER : Z := 864.
Definition TR_SIZE : Z := 2064.
Definition TR_MAX : Z := 30.
Definition ANMAX : Z := 2 ^ 30.
(* The inner entry's premises (amalloc_inner_contract, item 12; a Theorem Labs lane, fm W6 MallocInner2.v (not in this delivery)
   amalloc_inner_contract2 at a working branch 079b7a02ed1): asan_malloc's own stack bound with the caller's frame,
   the request bound, and the pcs a one-pc trace record may hold (malloc_context_size = 1). *)
(* fm W6 lib/A/W6/MallocInnerDef.v (not in this delivery) (a working branch 079b7a02ed1) *)
Definition AK_INNER2 : Z := 1968.
(* fm W6 REF lib/AZ/AsanW/ABase.v (not in this delivery) (a working branch 355c85c578c), the value every unit's W6 line moves onto *)
Definition AREQMAX : Z := 2^30.
(* GetCurrentPc's return address on ___interceptor_malloc's short branch (the one jal GetCurrentPc there followed by
   `sd a0,16(..)`), from the image's objdump (startcert/acontract.py trace_pcs); equal to the unit's W6
   lib/AZ/AsanW/ABase.v (asan) / lib/AZ/BothW/ABase.v (asan-ubsan) AMALLOC_PC (the generator asserts it) *)
Definition AMALLOC_PC : Z := 0x53708.
(* the same on ___interceptor_free's short branch; equal to the unit's W6 ABase.v AFREE_PC (asserted) *)
Definition AFREE_PC : Z := 0x535d8.
(* the same pc on the short branch of each of ___interceptor_realloc / _calloc / _strdup that the image has, from the
   image's objdump (startcert/acontract.py trace_pcs; the per-image rule of fm W6 lib/A/W6/AExtraPcs.v, extended to
   strdup, whose wrapper calls asan_malloc with its own one-pc record) *)
Definition A_EXTRA_PCS : list Z := [].
Definition FS_SIZE : Z := 11571200.   (* the side stack for frames (struct.asan.runtime RT4.1) *)
(* The image's GNU_RELRO range rounded out to pages, and GT: the end of the image's writable data rounded up to 4096
   (struct.asan.runtime RT4.3), from the ELF's program headers (startcert/acontract.py). *)
Definition RELRO_LO : Z := 0x9f000.
Definition RELRO_HI : Z := 0xa2000.
Definition GT : Z := 0x5fe000.

Definition aspZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 2).
Definition a_callee_saved (r : Z) : Prop := r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27).
Definition a_regs_kept (regs regs' : bvmap 5 word) : Prop :=
  forall r, a_callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition in_blocks (H : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) H /\ p <= a < p + n.
(* a lies in a read-only segment of the image (the same set as this lib's Sites/AImg.v a_in_ro) *)
Definition a_in_ro (a : Z) : Prop :=
  exists s, In s rsegs /\ seg_writable s = false /\
    Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
(* a lies on a page that a segment of the image maps (the page-rounded LOAD range the model reserves) *)
Definition a_on_img_page (a : Z) : Prop :=
  exists s, In s rsegs /\
    Z.of_N (seg_base s) / 4096 * 4096 <= a < (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096.
(* The word slack of a block: the bytes from its end up to the next multiple of 8 (struct.asan.runtime RT7.4). *)
Definition in_slack (H : list (Z * Z)) (a : Z) : Prop :=
  exists p n, In (p, n) H /\ p + n <= a < p + n + (8 - n mod 8) mod 8.
(* A block-related byte of H: a byte of a live block or of its word slack, or the Shadow byte of one of those. *)
Definition in_blk_ext (H : list (Z * Z)) (a : Z) : Prop :=
  in_blocks H a \/ in_slack H a \/ exists b, (in_blocks H b \/ in_slack H b) /\ a = shadow_addr b.
Definition a_in_img (a : Z) : Prop :=
  exists s, In s rsegs /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
(* The image's RELRO range, page-rounded (the GNU_RELRO program header): no store of a run changes its bytes. *)
Definition a_in_relro (a : Z) : Prop := RELRO_LO <= a < RELRO_HI.
(* The bytes program code may store into between allocator calls (law 4): its live blocks, the real stack, the client
   data outside RELRO (round 14); and the Shadow bytes of its live blocks (a holder may poison and unpoison granules
   of its own block: the allocator writes a live block's Shadow only when it allocates or frees it and never reads
   it; round 15, a Theorem Labs lane 17:02Z), of the real stack, and of the client granules that lie wholly inside one
   client object. *)
Definition a_store_ok (H : list (Z * Z)) (lo : Z) (a : Z) : Prop :=
  in_blocks H a \/ (lo <= a < APPMEM_END) \/ (in_blocks a_client a /\ ~ a_in_relro a) \/
  exists b, a = shadow_addr b /\
    (in_blocks H b \/ (lo <= b < APPMEM_END) \/
     (~ a_in_relro b /\ exists p n, In (p, n) a_client /\ p <= 8 * (b / 8) /\ 8 * (b / 8) + 8 <= p + n)).
(* The side stack FS: its base is the word at tp (struct.asan.runtime RT4.1). *)
Definition a_in_fs (B : asan_syms) (mem : word -> option byte) (a : Z) : Prop :=
  exists b, 0 <= b < 2 ^ 64 /\ word_mem rsegs mem (as_tp B) b /\ b <= a < b + FS_SIZE.
(* The side stack's layout (the runtime's FakeStack; the same formulas as a Theorem Labs lane's fs_B, fs_M, fs_hint, fs_flag,
   fs_frame in lib/A|B/Prog/asan_stack_malloc_c.v): class c (0..10) has frames of a_fs_B c bytes, a_fs_M c of them,
   a hint word at FS + 8c and one flag byte per frame (1 = in use); the frames start at FS + 36864. *)
Definition a_fs_B (c : nat) : Z := 64 * 2 ^ Z.of_nat c.
Definition a_fs_M (c : nat) : Z := 2 ^ (14 - Z.of_nat c).
Definition a_fs_hint (FS : Z) (c : nat) : Z := FS + 8 * Z.of_nat c.
Definition a_fs_flag (FS : Z) (c : nat) (j : Z) : Z := FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat c) + j.
Definition a_fs_frame (FS : Z) (c : nat) (j : Z) : Z := FS + 36864 + Z.of_nat c * 2 ^ 20 + j * a_fs_B c.
(* The side stack's runtime state at FS (what the stack-allocation entries read; a Theorem Labs lane 19:05Z): its bytes are
   present and writable, the header word at FS + 88 is 20 and the byte at FS + 96 (needs_gc) is 0, each class has a
   hint word, and every flag byte is 0 or 1. *)
Definition a_fs_ok (mem : word -> option byte) (FS : Z) : Prop :=
  (forall a, FS <= a < FS + FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < a_fs_M c ->
     mbyte rsegs mem (a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/ mbyte rsegs mem (a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
(* The block (q, n) the runtime gives: n = 0 is served as 1 byte (alloc.asan.md C1.6). *)
Definition a_size (n : Z) : Z := Z.max n 1.

Section AContracts.
Context {fx : YK11.FPState}.
Variable B : asan_syms.
(* RT: struct.asan.runtime (a working note, not in this delivery), clauses RT1-RT8, at a call whose entry sp is the first argument (owner a Theorem Labs lane). *)
Variable RT : Z -> (word -> option byte) -> Model -> Prop.
(* AH: struct.asan.heap (a working note, not in this delivery), clauses AH1-AH10, for the live-block list H (owner a Theorem Labs lane); AH7 is the placement room: every mapping
   the allocator may ask finds a free address range below the model's mmap top. *)
Variable AH : list (Z * Z) -> (word -> option byte) -> Model -> Prop.
(* The allocator's bytes in a state: its data, the trace store, statistics, and the Shadow bytes of chunk headers and
   guards and of chunks that are not live blocks. Not FS, not the Shadow of frames, not the Shadow of a live block's
   [p, p + 8 ceil(n / 8)). *)
(* rt_owned H mem md a: byte a is the allocator's in the state (mem, md) whose live blocks are H (round 15: the live
   blocks are an argument, so the predicate needs no uniqueness of H; W6 AllocRecord4 17:0xZ) *)
Variable rt_owned : list (Z * Z) -> (word -> option byte) -> Model -> Z -> Prop.
(* stklo: the lowest byte of the real stack (struct.asan.runtime RT6, the AsanThread's stack bottom). *)
Variable stklo : (word -> option byte) -> Model -> Z.
(* stkhi: the top of the real stack mapping (struct.asan.runtime [stklo, stkhi)); the runtime's stack-trace walk
   reads frame words in [sp, stkhi). *)
Variable stkhi : (word -> option byte) -> Model -> Z.
Let segs := rsegs.

Definition a_window (K : Z) (regs : bvmap 5 word) (a : Z) : Prop := aspZ regs - K <= a < aspZ regs.

Definition a_call_pre (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    : Prop :=
  RT (aspZ regs) mem md /\ AH H mem md /\ YK0s.ret_ok (getr regs 1) /\
  aspZ regs mod 16 = 0 /\ stklo mem md <= aspZ regs - K /\ aspZ regs < APPMEM_END /\
  aspZ regs <= stkhi mem md /\ stkhi mem md <= APPMEM_END /\
  (forall a, aspZ regs <= a < stkhi mem md -> exists b, mbyte segs mem a = Some b) /\
  (forall a, a_window K regs a -> writable_at segs mem a /\ addressable mem a 1 /\ ~ in_blocks H a) /\
  getr regs 4 = Z_to_bv 64 (as_tp B) /\
  ro_agree segs mem /\ m_halted md = None /\
  (* the window's bytes are present (round 13, a Theorem Labs lane 15:00Z: a callee saves registers in its frame) *)
  (forall a, a_window K regs a -> exists b, mbyte segs mem a = Some b).

(* The end state of every entry: registers kept, the invariants for H', the model changed only in its maps and its
   lazy-page ledgers (fd table, pipes, io, file system, process, limits and time kept), and only the allocator's
   bytes, the window, errno, the flag and the bytes of `touched` change. *)
Definition a_call_post (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
    : Prop :=
  RT (aspZ regs) mem' md' /\ AH H' mem' md' /\ a_regs_kept regs regs' /\
  (exists lz mt vm', md' = with_vm_backing lz mt (with_vmmaps vm' md)) /\
  (* the budget does not change across an allocator call (next round, a Theorem Labs lane 12:3xZ: a callee with two
     allocating calls needs LIM_AG <= vm_limit at the second one; no allocator path changes the limit) *)
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\
  (* vm_init_sp is immutable for the run (LPS State.v:2797-2800; instruction steps keep m_vmmaps, Run.v:347-366 /
     State.v:4708; every map-writing syscall arm copies the old vm_init_sp, check_{brk,munmap,mprotect,madvise,mmap}
     _init_sp in NodesA.v (not in this delivery), a Theorem Labs lane 04:41Z), so alloc_top = vm_init_sp - stack_max_size is
     kept too (released alloc_top_isp): G1 of the relay lanes, two Theorem Labs lanes 19:06Z-20:37Z *)
  vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) /\
  stklo mem' md' = stklo mem md /\ stkhi mem' md' = stkhi mem md /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ rt_owned H mem md a -> ~ rt_owned H' mem' md' a -> ~ a_window K regs a ->
     ~ (a_errno B <= a < a_errno B + 4) -> a <> as_oom B -> ~ touched a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, a_errno B <= a < a_errno B + 4 -> (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_blocks H a -> ~ touched a -> ~ rt_owned H' mem' md' a) /\
  (forall a, a_window K regs a -> writable_at segs mem' a) /\
  ro_agree segs mem' /\ m_halted md' = None /\
  (* the side stack's base word at tp (a_in_fs reads it) and the word after it are not changed by an allocator entry *)
  (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) /\
  (* the window's bytes are present again at the return (round 13) *)
  (forall a, a_window K regs a -> exists b, mbyte segs mem' a = Some b) /\
  (* the flag OOM(I) keeps its writability (round 14, a Theorem Labs lane 16:29Z) *)
  (writable_at segs mem (as_oom B) <-> writable_at segs mem' (as_oom B)) /\
  (* the thread record is kept: the TSD slot's word C, the word T at C + 152 and the 16 bytes at T + 48 (round 15:
     was law 15, which compared two arbitrary states and so could not hold across runs; W6 AllocRecord4 17:2xZ) *)
  (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 ->
     word_mem segs mem' RT_TSDMAIN C /\ word_mem segs mem' (C + 152) T /\
     forall i, 0 <= i < 16 -> mbyte segs mem' (T + 48 + i) = mbyte segs mem (T + 48 + i)) /\
  (* the callee returns with ra (x1) unchanged (next round, two Theorem Labs lanes 23:4xZ: x1 is not in
     a_callee_saved, so the forall-regs' posts leave it free; the W6 posts discharge this from the concrete
     return bank c' = mkCfg (mkst regs' (getr regs 1) ...), as the free posts already are; appended last, a Theorem Labs lane
     08:10Z: existing conjuncts keep their positions) *)
  getr regs' 1 = getr regs 1 /\
  (* the OOM flag's byte itself is kept (next round, a Theorem Labs lane 02:17Z ruling for a Theorem Labs lane: under the room premises
     every allocation succeeds, so no callee sets the flag; W6 discharges it, the flag is untouched; appended last) *)
  mbyte segs mem' (as_oom B) = mbyte segs mem (as_oom B).

(* errno and the flag OOM(I) do not change. *)
Definition a_errno_kept (mem mem' : word -> option byte) : Prop :=
  (forall i, 0 <= i < 4 -> mbyte segs mem' (a_errno B + i) = mbyte segs mem (a_errno B + i)) /\
  mbyte segs mem' (as_oom B) = mbyte segs mem (as_oom B).

(* A new block (q, n): aligned, in AppMem below the real stack, off the image, FS, every block of H and the
   allocator's bytes, writable, addressable, with its word slack readable. *)
Definition a_new_block (H : list (Z * Z)) (q n : Z) (mem' : word -> option byte) (md' : Model) : Prop :=
  q <> 0 /\ q mod 16 = 0 /\ 4096 <= q /\ q + n <= stklo mem' md' /\ end_in_app q n /\
  (forall a, q <= a < q + n ->
     ~ in_blocks H a /\ ~ in_slack H a /\ ~ a_in_img a /\ ~ a_in_fs B mem' a /\ ~ rt_owned (H ++ [(q, n)]) mem' md' a /\
     writable_at segs mem' a) /\
  addressable mem' q n /\
  (forall a, q + n <= a < q + n + (8 - n mod 8) mod 8 -> exists b, mbyte segs mem' a = Some b) /\
  (* the word slack is chunk memory of the new block too: never the image, FS, another block or the allocator's
     (next batch, a Theorem Labs lane 02:18Z) *)
  (forall a, q + n <= a < q + n + (8 - n mod 8) mod 8 ->
     ~ in_blocks H a /\ ~ a_in_img a /\ ~ a_in_fs B mem' a /\ ~ rt_owned (H ++ [(q, n)]) mem' md' a).
(* A new block with its provenance: its bytes, word slack and their Shadow were the allocator's in the producer's entry
   state (H, mem, md) (next round, a Theorem Labs lane 05:16Z: producers that return a new block state their posts with it;
   the allocation contracts' returns give it). *)
Definition a_new_block_own (H : list (Z * Z)) (mem : word -> option byte) (md : Model) (q n : Z)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  a_new_block H q n mem' md' /\ (forall a, in_blk_ext [(q, n)] a -> rt_owned H mem md a).

(* The live blocks' total size (round 17: the room premise of the allocation contracts). *)
Fixpoint a_live_bytes (H : list (Z * Z)) : Z := match H with [] => 0 | (_, n) :: H' => n + a_live_bytes H' end.
(* The allocation contracts' room: the live blocks' total size plus the request is at most 12 * 2^30 (round 17:
   without a bound an adversarially fragmented heap leaves no hole for a large secondary map, which the model may
   answer ENOMEM, and 2^20 live secondary chunks exhaust the runtime's table; the asan analogue of plain's room
   premise; W6. Round 19: 12 * 2^30, not 2^32: fuzz_state's and fuzz_reply's slots need more than 2^30 live in one
   call (two Theorem Labs lanes 20:32Z); W6's gap count allows at most about 13.2 GiB with secondary chunks > 64512
   bytes). *)
Definition ALIVE_MAX : Z := 12 * 2 ^ 30.

(* The secondary map's placement room (next batch, the lead's yes 02:18Z): a request above the primary size
   classes (n > 64512) maps a_sec_map n bytes (the runtime's needed size, page-rounded, plus a guard page) at a place
   the model chooses freely among the free gaps of the band [A_PLACE_LO, A_PLACE_HI) above the shadow; with the live
   secondary blocks spaced adversarially a hole of that size remains only when (their mapped bytes) + (their count + 1)
   * (the hole + a page) fits the band (pigeonhole, W6 AHRoomBudget.v gap_count). MODEL-FIDELITY PREMISE: Linux places
   such maps top-down below mmap_base and has no such limit; the CI/CD lead (lps owner, 2026-10-27T02:15Z) plans
   top-down placement in lps216, after which this premise is dropped. It stays in the allocator contracts only: never
   in a published statement or a top-level hypothesis. *)
Definition A_PRIMARY_MAX : Z := 64512.
Definition A_PLACE_LO : Z := 0x10007fff8000.
Definition A_PLACE_HI : Z := 0x7fff7f800000.
Definition a_rup (x a : Z) : Z := (x + a - 1) / a * a.
Definition a_sec_map (n : Z) : Z := a_rup (a_rup n 8 + 4096) 4096 + 4096.
Definition a_sec_blocks (H : list (Z * Z)) : list (Z * Z) := filter (fun b => A_PRIMARY_MAX <? snd b) H.
Definition a_sec_mapped (H : list (Z * Z)) : Z := fold_right Z.add 0 (map (fun b => a_sec_map (snd b)) (a_sec_blocks H)).
(* The room for the placement of a secondary map (soundness fix, a Theorem Labs lane 09:1xZ, lead's yes 09:18Z): the band
   [A_PLACE_LO, A_PLACE_HI) must also hold the main maps above the Shadow (A_PLACE_OTHER) and the secondary chunks
   the state holds that are not in H (quarantined: A_PLACE_OTHER_N), and the model's ceiling is ATOP_MIN. *)
Definition A_PLACE_OTHER : Z := 2 ^ 41.
Definition A_PLACE_OTHER_N : Z := 8354.
Definition a_place_room (H : list (Z * Z)) (n : Z) : Prop :=
  n <= A_PRIMARY_MAX \/
  a_sec_mapped H + A_PLACE_OTHER +
    (Z.of_nat (length (a_sec_blocks H)) + A_PLACE_OTHER_N + 1) * (a_sec_map n + 4096) <= A_PLACE_HI - A_PLACE_LO.

(* The end of an allocation of n bytes from an entry with stack bound K: a new block, whose bytes, word slack and
   their Shadow were the allocator's in the entry's state (round 17, a Theorem Labs lane 20:19Z; slack and Shadow next round,
   a Theorem Labs lane 03:28Z). *)
Definition amalloc_ret (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (n : Z) (c' : config) : Prop :=
  exists regs' mem' md' q,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\ getr regs' 10 = Z_to_bv 64 q /\
    a_new_block H q (a_size n) mem' md' /\
    a_call_post K H regs mem md (fun a => q <= a < q + a_size n) (H ++ [(q, a_size n)]) regs' mem' md' /\
    a_errno_kept mem mem' /\
    (forall a, in_blk_ext [(q, a_size n)] a -> rt_owned H mem md a).

(* C1: malloc, entered at pc (the trampoline or the body ___interceptor_malloc). Bc bounds the live slot bytes of each
   size class (ClassConsDef.a_class_req_fits, the request's slot counted); with the room inequality no size class is
   full at the call (route (C): the class-full abort is not a cut, YK15.v cut_ok). *)
Definition amalloc_at (pc : Z) : Prop :=
  forall H regs mem md n (Bc : Z -> Z),
    a_call_pre AK_MALLOC H regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n <= ANMAX ->
    a_live_bytes H + a_size n <= ALIVE_MAX -> a_place_room H (a_size n) ->
    ClassConsDef.a_class_req_fits Bc H n ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (amalloc_ret AK_MALLOC H regs mem md n).
Definition amalloc_contract : Prop := amalloc_at (as_malloc B).
Definition amalloc_body_contract : Prop := amalloc_at (as_malloc_body B).

(* A: asan_malloc entered directly (fuzz_command's strdup wrapper; the strndup wrapper calls ___interceptor_malloc,
   C1 at the body), a1 = T, the trace record in the caller's frame (U1 wrote it): T lies at or above sp and below
   stkhi, its bytes are readable, its trace pointer is T + 16, its size (u32 at T + 8) is 1, its tag (u32 at T + 12)
   is 0 and its one pc (at T + 16) is AMALLOC_PC, AFREE_PC or in A_EXTRA_PCS (item 12); T is read, not written. *)
Definition amalloc_inner_contract : Prop :=
  forall H regs mem md n T pc (Bc : Z -> Z),
    a_call_pre AK_INNER2 H regs mem md -> getr regs 10 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
    a_live_bytes H + a_size n <= ALIVE_MAX -> a_place_room H (a_size n) ->
    ClassConsDef.a_class_req_fits Bc H n ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    getr regs 11 = Z_to_bv 64 T -> aspZ regs <= T -> T + TR_SIZE <= stkhi mem md ->
    (forall a, T <= a < T + TR_SIZE -> exists b, mbyte segs mem a = Some b) ->
    word_mem segs mem T (T + 16) ->
    mbyte segs mem (T + 8) = Some (Z_to_bv 8 1) ->
    (forall i, 9 <= i < 16 -> mbyte segs mem (T + i) = Some (Z_to_bv 8 0)) ->
    word_mem segs mem (T + 16) pc -> (pc = AMALLOC_PC \/ pc = AFREE_PC \/ In pc A_EXTRA_PCS) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (as_malloc_inner B)) mem (seg_rom segs)) md)
      (fun c' => amalloc_ret AK_INNER2 H regs mem md n c' /\
         forall regs' mem' md', c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' ->
           forall a, T <= a < T + TR_SIZE -> mbyte segs mem' a = mbyte segs mem a).

(* C2: free of a live block, entered at pc (the trampoline or the body ___interceptor_free). Bc bounds the live slot
   bytes of each size class of the call heap; with the room inequality the quarantine's batch class is not full. *)
Definition afree_at (pc : Z) : Prop :=
  forall H1 H2 regs mem md p n (Bc : Z -> Z),
    a_call_pre AK_FREE (H1 ++ (p, n) :: H2) regs mem md -> getr regs 10 = Z_to_bv 64 p ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (H1 ++ (p, n) :: H2) c <= Bc c) ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         a_call_post AK_FREE (H1 ++ (p, n) :: H2) regs mem md (fun a => p <= a < p + n) (H1 ++ H2)
           regs' mem' md' /\
         a_errno_kept mem mem').
Definition afree_contract : Prop := afree_at (as_free B).
Definition afree_body_contract : Prop := afree_at (as_free_body B).

(* C2.2: free(NULL); the set of the allocator's bytes does not change. *)
Definition afree_null_contract : Prop :=
  forall H regs mem md (Bc : Z -> Z),
    a_call_pre AK_FREE H regs mem md -> getr regs 10 = Z_to_bv 64 0 ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes H c <= Bc c) ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (as_free B)) mem (seg_rom segs)) md)
      (fun c' => exists regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         a_call_post AK_FREE H regs mem md (fun _ => False) H regs' mem' md' /\
         (forall a, rt_owned H mem' md' a <-> rt_owned H mem md a) /\
         a_errno_kept mem mem').

(* C3: realloc of a live block (p, k) to n bytes (the block always moves). *)
Definition arealloc_contract (pc : Z) : Prop :=
  forall H1 H2 regs mem md p k n (Bc : Z -> Z),
    a_call_pre AK_REALLOC (H1 ++ (p, k) :: H2) regs mem md ->
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 1 <= n <= ANMAX ->
    a_live_bytes (H1 ++ (p, k) :: H2) + n <= ALIVE_MAX -> a_place_room (H1 ++ (p, k) :: H2) n ->
    ClassConsDef.a_class_req_fits Bc (H1 ++ (p, k) :: H2) n ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists regs' mem' md' q,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\ getr regs' 10 = Z_to_bv 64 q /\
         a_new_block (H1 ++ (p, k) :: H2) q n mem' md' /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (q + i) = mbyte segs mem (p + i)) /\
         a_call_post AK_REALLOC (H1 ++ (p, k) :: H2) regs mem md (fun a => (p <= a < p + k) \/ (q <= a < q + n))
           (H1 ++ H2 ++ [(q, n)]) regs' mem' md' /\
         a_errno_kept mem mem' /\
         (* the new block's bytes, word slack and their Shadow were the allocator's in the entry's state (round 19,
            a Theorem Labs lane 20:37Z; slack and Shadow next round) *)
         (forall a, in_blk_ext [(q, n)] a -> rt_owned (H1 ++ (p, k) :: H2) mem md a)).

(* C3.2: realloc(NULL, n) is malloc(n), with the realloc window. *)
Definition arealloc_null_contract (pc : Z) : Prop :=
  forall H regs mem md n (Bc : Z -> Z),
    a_call_pre AK_REALLOC H regs mem md -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n ->
    1 <= n <= ANMAX -> a_live_bytes H + n <= ALIVE_MAX -> a_place_room H n ->
    ClassConsDef.a_class_req_fits Bc H n ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (amalloc_ret AK_REALLOC H regs mem md n).

(* C4: calloc(m, s); the block's bytes are 0. *)
Definition acalloc_contract (pc : Z) : Prop :=
  forall H regs mem md m s (Bc : Z -> Z),
    a_call_pre AK_CALLOC H regs mem md -> getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 s ->
    0 <= m -> 0 <= s -> 1 <= m * s <= ANMAX -> a_live_bytes H + m * s <= ALIVE_MAX -> a_place_room H (m * s) ->
    ClassConsDef.a_class_req_fits Bc H (m * s) ->
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES ->
       Bc c + ClassConsDef.QSLOT c + 8 * AsanCtrl.K_MAX_SIZE + 2 * AsanCtrl.K_USER_MAP <= AsanCtrl.K_FREEARR_OFF) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => amalloc_ret AK_CALLOC H regs mem md (m * s) c' /\
         forall regs' mem' md', c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' ->
           forall i, 0 <= i < m * s -> mbyte segs mem' (bv_unsigned (getr regs' 10) + i) = Some (Z_to_bv 8 0)).

(* Laws of the heap invariant that callers use to carry it through their own code (the frame proves them). RT's
   laws (RT8: the stores program code may make) are struct.asan.runtime's (a working note, not in this delivery), owner a Theorem Labs lane. *)
Definition a_laws : Prop :=
  (* AH1: each live block lies in AppMem below the real stack, off the image's pages and FS, writable *)
  (forall H mem md p n, AH H mem md -> In (p, n) H ->
     p mod 16 = 0 /\ 4096 <= p /\ p + n <= stklo mem md /\ end_in_app p n /\
     forall a, p <= a < p + n -> app_mem a /\ writable_at segs mem a /\ ~ a_in_img a /\ ~ a_on_img_page a /\
       ~ a_in_fs B mem a) /\
  (* AH1: live blocks are pairwise disjoint *)
  (forall H1 H2 mem md p n q k, AH (H1 ++ (p, n) :: H2) mem md -> In (q, k) (H1 ++ H2) ->
     p + n <= q \/ q + k <= p) /\
  (* the allocator owns no byte of a live block, its word slack, FS or the real stack, nor the Shadow byte of any of
     them *)
  (forall H mem md a, AH H mem md ->
     (in_blocks H a \/ in_slack H a \/ a_in_fs B mem a \/ stklo mem md <= a < APPMEM_END) ->
     ~ rt_owned H mem md a /\ ~ rt_owned H mem md (shadow_addr a)) /\
  (* stores into the bytes program code may store into (a_store_ok; the overlay unchanged elsewhere, so read-only
     bytes, RELRO and the allocator's cells stay) keep the heap invariant, its ownership, stklo and stkhi (round 14:
     the round-13 form, "the allocator's bytes unchanged", was false at the frame's fields; AllocRecord4 16:4xZ) *)
  (forall H mem mem' md, AH H mem md ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
     (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) ->
     AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\
     stkhi mem' md = stkhi mem md) /\
  (* the order of the live-block list does not matter *)
  (forall H H' mem md, AH H mem md -> Permutation.Permutation H H' -> AH H' mem md) /\
  (* the allocator owns no byte of the client data (musl's, the harness's and the program's .data/.bss objects),
     nor the Shadow byte of any image byte *)
  (forall H mem md a, AH H mem md ->
     (in_blocks a_client a -> ~ rt_owned H mem md a) /\ (a_in_img a -> ~ rt_owned H mem md (shadow_addr a)) /\
     (* the side stack's base word at tp is the allocator's bytes: no program store moves FS *)
     (as_tp B <= a < as_tp B + 8 -> rt_owned H mem md a)) /\
  (* AH9: the thread record. C = the first word of musl's __pthread_tsd_main (RT_TSDMAIN, AsanRT.v; the runtime's TSD
     slot, the allocator's bytes), T = the word at C + 152 (the main thread's AsanThread); both are set at start-up,
     so neither is 0 (round 13, a Theorem Labs lane 15:00Z); the byte at T + 3168 is the allocator's and 0, the byte at
     T + 40 is 0, the 16 bytes at T + 48 (read by the frame-allocation entries) are the allocator's and present, and
     the stack bounds at T + 8 (top) and T + 16 (bottom) are ordered below stkhi *)
  (forall H mem md, AH H mem md ->
     (forall i, 0 <= i < 8 -> rt_owned H mem md (RT_TSDMAIN + i)) /\
     (* the main thread's tsd pointer at tp - 88 is __pthread_tsd_main and the runtime's TSD key is 0 (musl's first
        pthread_key_create; next generation, a Theorem Labs lane 04:47Z: so the slot TS + 8 * k is RT_TSDMAIN, owned above;
        W6: arep_rt's rw_cells at ARep.v (not in this delivery), truth check 04:57Z) *)
     word_mem segs mem (as_tp B - 88) RT_TSDMAIN /\
     (forall i, 0 <= i < 4 -> mbyte segs mem (RT_TSDK + i) = Some (Z_to_bv 8 0)) /\
     exists C T, word_mem segs mem RT_TSDMAIN C /\
       0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\
       word_mem segs mem (C + 152) T /\
       (forall i, 0 <= i < 8 -> rt_owned H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\
       mbyte segs mem (T + 3168) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + 3168) /\
       rt_owned H mem md (T + 3168) /\ ~ a_in_img (T + 3168) /\ app_mem (T + 3168) /\
       mbyte segs mem (T + 40) = Some (Z_to_bv 8 0) /\ rt_owned H mem md (T + 40) /\
       (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 8 + i)) /\
       (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 48 + i) /\ exists b, mbyte segs mem (T + 48 + i) = Some b) /\
       exists top bot, word_mem segs mem (T + 8) top /\ word_mem segs mem (T + 16) bot /\
         0 <= bot < top /\ 4096 <= top <= stkhi mem md) /\
  (* AH8: the allocator's two setting cells hold their start-up values and are the allocator's bytes *)
  (forall H mem md, AH H mem md ->
     mbyte segs mem (as_mcs B) = Some (Z_to_bv 8 30) /\
     (forall i, 1 <= i < 4 -> mbyte segs mem (as_mcs B + i) = Some (Z_to_bv 8 0)) /\
     mbyte segs mem (as_mrn B) = Some (Z_to_bv 8 1) /\
     (forall i, 0 <= i < 4 -> rt_owned H mem md (as_mcs B + i)) /\ rt_owned H mem md (as_mrn B)) /\
  (* the allocator owns no byte of a read-only segment of the image *)
  (forall H mem md a, AH H mem md -> a_in_ro a -> ~ rt_owned H mem md a) /\
  (* nothing at or above the model's mmap top (the real stack and above) is the allocator's or a live block's *)
  (forall H mem md a, AH H mem md -> State.alloc_top (m_vmmaps md) <= a < 2 ^ 64 ->
     ~ rt_owned H mem md a /\ ~ in_blocks H a) /\
  (* AH10: the interceptor metadata region. T = the word at metadata_mem (RT_IMEM, AsanRT.v); its 3727360 bytes are
     0, writable, the allocator's bytes, in AppMem, off the image and FS *)
  (forall H mem md, AH H mem md ->
     exists T, 0 <= T < 2 ^ 64 /\ word_mem segs mem RT_IMEM T /\
       forall i, 0 <= i < 3727360 ->
         mbyte segs mem (T + i) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + i) /\ rt_owned H mem md (T + i) /\
         app_mem (T + i) /\ ~ a_in_img (T + i) /\ ~ a_in_fs B mem (T + i)) /\
  (* a model change outside the memory maps, the lazy-page ledgers and the process state (fd table, file system, ...)
     keeps the heap invariant, the allocator's bytes, stklo and stkhi (round 14: the process state kept) *)
  (forall H mem md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
     m_vm_materialized md' = m_vm_materialized md -> m_proc md' = m_proc md ->
     (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\
     stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md) /\
  (* materializing lazy pages (one LPS accounting step; AsanLift.mat_le is its closure) keeps the heap invariant,
     the allocator's bytes, stklo and stkhi *)
  (forall H mem md acc md', materialize_model_accesses md acc = Some md' ->
     (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\
     stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md) /\
  (* ownership changes only at block-related bytes: in two states of the run (the same stklo, the 16 bytes at tp
     unchanged: the side stack's base word and the DTLS word) where the heap invariant holds for H and H', a byte that
     is block-related in neither is the allocator's in both or in neither. With it a_call_post's frame clause composes
     over consecutive calls (a Theorem Labs lane 2026-10-26 14:11Z). Round 19: 16 bytes, not 8 (W6: the DTLS link's bytes
     at [tp + 8] + 24 are not the allocator's, so with 8 the law was false). *)
  (forall H H' mem md mem' md' a, AH H mem md -> AH H' mem' md' -> stklo mem' md' = stklo mem md ->
     (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) ->
     ~ in_blk_ext H a -> ~ in_blk_ext H' a -> (rt_owned H mem md a <-> rt_owned H' mem' md' a)) /\
  (* the real stack is in HighMem (struct.asan.runtime (a working note, not in this delivery), clause RT6.1; round 14, a Theorem Labs lane 16:44Z) *)
  (forall H mem md, AH H mem md -> HIGHMEM_BEG <= stklo mem md) /\
  (* the side stack FS lies above the image's writable data and below the real stack (RT4.3; round 14), page-aligned
     (a Theorem Labs lane 18:29Z) and in AppMem (a Theorem Labs lane 18:27Z: the start-up maps it off the shadow ranges; round 15);
     b is the word's value in [0, 2^64) (round 16: word_mem holds for every b congruent mod 2^64; an internal review round). Not
     HIGHMEM_BEG <= b: the start-up maps FS with a null-hint mmap, which the model places anywhere at or above GT
     (the check of all 28 images' main-entry facts, 01:5xZ: FS = GT is satisfiable in every image) *)
  (forall H mem md b, AH H mem md -> word_mem segs mem (as_tp B) b -> 0 <= b < 2 ^ 64 ->
     GT <= b /\ b + FS_SIZE <= stklo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + FS_SIZE -> app_mem a) /\
  (* AH1, round 14 (a Theorem Labs lane 16:36Z): a block of n > 0 bytes has AppMem up to 7 bytes past its end (its chunk's
     right guard region is in the same mapping) *)
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n -> app_mem (p + n + 7)) /\
  (* every live block lies at or above 2^21: the size-class space is a start-up reservation far above the image, and
     a secondary chunk (>= 128 KiB) does not fit in the free range below the image (round 15, a Theorem Labs lane 16:57Z) *)
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 2 ^ 21 <= p) /\
  (* a live block's word slack stays present (a_new_block gives it at the return; nothing removes a byte from
     memory; round 15, a Theorem Labs lane 18:15Z) *)
  (forall H mem md p n, AH H mem md -> In (p, n) H ->
     forall a, p + n <= a < p + n + (8 - n mod 8) mod 8 -> exists b, mbyte segs mem a = Some b) /\
  (* the side stack's runtime state (round 16, a Theorem Labs lane 19:05Z: what the stack-allocation entries read; the static
     TLS cells are RT part 9): a_fs_ok at the base FS; the thread's DTLS word DB at tp + 8 is not 0, its word at
     DB + 24 is tp, and those 8 bytes are in AppMem, below the real stack, off errno, FS and every live block, and not
     the allocator's (so every entry keeps them); and the 16 bytes at T + 48 are in AppMem (a Theorem Labs lane 19:16Z) *)
  (forall H mem md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 ->
     a_fs_ok mem FS /\
    (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem segs mem (as_tp B + 8) DB /\ DB <> 0 /\ word_mem segs mem (DB + 24) (as_tp B) /\
        forall a, DB + 24 <= a < DB + 32 ->
          app_mem a /\ a < stklo mem md /\ ~ (a_errno B <= a < a_errno B + 4) /\ ~ a_in_fs B mem a /\
          ~ in_blk_ext H a /\ ~ a_in_img a /\ ~ in_blocks a_client a /\ ~ rt_owned H mem md a) /\
     (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 ->
        forall i, 0 <= i < 16 -> app_mem (T + 48 + i))) /\
  (* stores into the side stack and its Shadow (live frames by their holders, the frame release's flag byte, the
     stack-allocation entries' hint, flag and frame words), together with the stores law 4 allows, keep the heap
     invariant when the side stack's state stays a_fs_ok (round 16: fake frames;
     four Theorem Labs lanes) *)
  (forall H mem mem' md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> ~ (FS <= a < FS + FS_SIZE) ->
        ~ (exists b, FS <= b < FS + FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
     (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) ->
     a_fs_ok mem' FS ->
     AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\
     stkhi mem' md = stkhi mem md) /\
  (* AH10's region is page-aligned (round 16, a Theorem Labs lane: fflush / fclose wrappers' metadata table) *)
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> T mod 4096 = 0) /\
  (* AH10's region lies above the image (an internal map), and the word at RT_IMEM is never the allocator's (round 17,
     a Theorem Labs lane 20:14Z: fflush / fclose wrappers) *)
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> GT <= T) /\
  (forall H mem md i, AH H mem md -> 0 <= i < 8 -> ~ rt_owned H mem md (RT_IMEM + i)) /\
  (* a live block is not empty (round 21, a Theorem Labs lane 21:31Z: 0 <= n; next round 0 < n, a Theorem Labs lane 05:04Z: every block the
     allocator creates has a_size n >= 1, so two live blocks never share an address) *)
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n) /\
  (* the allocator owns every other byte below the model's mmap top (next round, a Theorem Labs lane 05:10Z: a byte of a block
     a call allocates and frees inside itself, and its Shadow, are then covered by the caller's frame): every byte not
     in a live block, its slack or their Shadow, not the image or its pages, not client data, FS or the real stack, not
     the word at RT_IMEM or the DTLS word, and not the Shadow of the image, client data, FS or [alloc_top, APPMEM_END) *)
  (forall H mem md a, AH H mem md -> 0 <= a < State.alloc_top (m_vmmaps md) ->
     ~ in_blk_ext H a -> ~ a_in_img a -> ~ a_on_img_page a -> ~ in_blocks a_client a -> ~ a_in_fs B mem a ->
     ~ (stklo mem md <= a < APPMEM_END) -> ~ (RT_IMEM <= a < RT_IMEM + 8) ->
     ~ (exists DB, word_mem segs mem (as_tp B + 8) DB /\ DB + 24 <= a < DB + 32) ->
     ~ (exists b, a = shadow_addr b /\
          (a_in_img b \/ in_blocks a_client b \/ a_in_fs B mem b \/ State.alloc_top (m_vmmaps md) <= b < APPMEM_END)) ->
     rt_owned H mem md a) /\
  (* the DTLS word lies below the real stack (next round, a Theorem Labs lane 05:46Z: __asan_stack_malloc_0's TLS cells need
     DB + 32 <= 2 ^ 64; fs_state's DTLS clause gives it for its DB, this states it for any DB read at tp + 8) *)
  (forall H mem md DB, AH H mem md -> word_mem segs mem (as_tp B + 8) DB -> 0 <= DB < 2 ^ 64 ->
     DB + 32 <= stklo mem md) /\
  (* a live block's word slack lies below the real stack too (next round, a Theorem Labs lane 06:14Z: AH1 places the bytes
     only; the slack is chunk memory of the same block) *)
  (forall H mem md p n, AH H mem md -> In (p, n) H -> p + n + (8 - n mod 8) mod 8 <= stklo mem md) /\
  (* the real stack's bottom is at or above the model's mmap top (next round, a Theorem Labs lane 09:20Z, via the lead; the
     direction is this one: the W6 instance has stklo = alloc_top + 4096, the guard page amalloc_stmt keeps free,
     a Theorem Labs lane 10:21Z). It does NOT bound a block by the mmap top: that is the above_top law (nothing at or above
     alloc_top is a live block's) *)
  (forall H mem md, AH H mem md -> State.alloc_top (m_vmmaps md) <= stklo mem md) /\
  (* the run's initial sp is a valid one, so alloc_top = vm_init_sp - stack_max_size is 16-aligned and lies above
     HIGHMEM_BEG (next round, a Theorem Labs lane 21:57Z / 22:04Z: the word slack below the entry top and the Shadow case of
     a_laws_rest_owned; W6 discharge: AllocTopValidSp.v (not in this delivery) ah5_valid_sp, a working branch 012b56f81f4) *)
  (forall H mem md, AH H mem md -> Run.valid_sp (vm_init_sp (m_vmmaps md))) /\
  (* every AH state's memory holds no byte at a read-only address: lib/Lib/Mem.v mem_inv, the invariant the program's
     own steps carry (the posts of lib/A/Prog's *_c.v); W6 discharge: mem_inv_h5 (a Theorem Labs lane) *)
  (forall H mem md, AH H mem md -> Mem.mem_inv segs mem) /\
(* AH13: the runtime TLS cells lie below the stack floor and off the side stack, at every AH state (PLACEMENT; the VALUES are a_laws_thread / a_laws_fs_state, the PRESERVATION across a call is a_call_post's thread-record conjunct). Cells: [tp - 88, tp - 80) and [tp - 8, tp + 16) (image TLS words), [DT + 8, DT + 16) for DT the word at tp - 8, the TSD slot [RT_TSDMAIN, RT_TSDMAIN + 8) (= TS + 8 k with TS the word at tp - 88 and the image's TSD key k = 0), [C + 152, C + 160), [T + 48, T + 64); [DB + 24, DB + 32) is a_laws_fs_state's DTLS clause, already placed. C and T are ANY words read at those cells, so a carrier can use this before tying them to their at-main values. *)
(forall H mem md, AH H mem md ->
   (forall a, (as_tp B - 88 <= a < as_tp B - 80 \/ as_tp B - 8 <= a < as_tp B + 16 \/ RT_TSDMAIN <= a < RT_TSDMAIN + 8) ->
      a < stklo mem md /\ ~ a_in_fs B mem a) /\
   (forall DT, word_mem segs mem (as_tp B - 8) DT -> 0 <= DT < 2 ^ 64 ->
      forall a, DT + 8 <= a < DT + 16 -> a < stklo mem md /\ ~ a_in_fs B mem a) /\
   (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 ->
      forall a, (C + 152 <= a < C + 160 \/ T + 48 <= a < T + 64) -> a < stklo mem md /\ ~ a_in_fs B mem a)).

(* The materialization law along AsanLift.mat_le (any number of LPS accounting steps). *)
Lemma a_laws_mat_le : a_laws -> forall H mem md md', AsanLift.mat_le md md' ->
  (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\
  stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L6 & _) H mem md md' M.
  induction M as [m | m acc m' m'' Hm M IH].
  - exact (conj (fun x => x) (conj (fun a => iff_refl _) (conj eq_refl eq_refl))).
  - destruct (L6 H mem m acc m' Hm) as (A1 & A2 & A3 & A4).
    destruct IH as (B1 & B2 & B3 & B4).
    split; [intro X; exact (B1 (A1 X)) |].
    split; [intro a; exact (iff_trans (B2 a) (A2 a)) |].
    split; [rewrite B3; exact A3 | rewrite B4; exact A4].
Qed.

(* The model shape of a_call_post survives lazy-page materialization: materialize_model_accesses changes only the
   materialized pages (LPS State.v materialize_model_accesses). *)
Lemma mat_le_shape : forall md md1 md2 lz mt vm', md1 = with_vm_backing lz mt (with_vmmaps vm' md) ->
  AsanLift.mat_le md1 md2 -> exists lz2 mt2 vm2, md2 = with_vm_backing lz2 mt2 (with_vmmaps vm2 md).
Proof.
  intros md md1 md2 lz mt vm' E M. revert lz mt vm' E.
  induction M as [m | m acc m' m'' Hm M IH]; intros lz mt vm' E.
  - exists lz, mt, vm'. exact E.
  - unfold materialize_model_accesses in Hm.
    destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) (vm_limit (m_vmmaps m))
                acc) as [pages|]; [|discriminate].
    injection Hm as <-. apply (IH lz pages vm'). subst m. reflexivity.
Qed.

(* The two maps fields a_call_post keeps (a_call_post_vm_limit, a_call_post_init_sp): an accounting run keeps the whole
   vmmaps record, so it keeps the budget and the initial sp (fuzz_reply AGlue.v ag_vm_kept, a working branch
   b3d9217852e; a working branch 02b6e83e482's helper). *)
Lemma ag_vm_kept : forall md md', AsanLift.mat_le md md' ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Proof.
  intros md md' H. destruct (AsanLift.mat_le_frame md md' H) as (_ & VM & _).
  rewrite VM. split; reflexivity.
Qed.

(* An entry's end state stays one after later lazy-page materialization (AsanLift.mat_le, e.g. the steps of
   evt_SR_lazy), given that RT does (round 13, a Theorem Labs lane 15:00Z). *)
Lemma a_call_post_mat_le : a_laws ->
  (forall sp mem md md', RT sp mem md -> AsanLift.mat_le md md' -> RT sp mem md') ->
  forall K H regs mem md touched H' regs' mem' md1 md2,
    a_call_post K H regs mem md touched H' regs' mem' md1 -> AsanLift.mat_le md1 md2 ->
    a_call_post K H regs mem md touched H' regs' mem' md2.
Proof.
  intros LW RTM K H regs mem md touched H' regs' mem' md1 md2
    (P1 & P2 & P3 & (lz & mt & vm' & E) & V1 & V2 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14) M.
  destruct (a_laws_mat_le LW H' mem' md1 md2 M) as (A1 & A2 & A3 & A4).
  destruct (AsanLift.mat_le_frame md1 md2 M) as (_ & VM & _).
  split; [exact (RTM _ _ _ _ P1 M)|].
  split; [exact (A1 P2)|].
  split; [exact P3|].
  split; [exact (mat_le_shape md md1 md2 lz mt vm' E M)|].
  split; [rewrite VM; exact V1|].
  split; [rewrite VM; exact V2|].
  split; [rewrite A3; exact P5|].
  split; [rewrite A4; exact P6|].
  split; [intros a Ha N1 N2; apply (P7 a Ha N1); intro X; apply N2; exact (proj2 (A2 a) X)|].
  split; [exact P8|].
  split; [intros a Hb Ht X; exact (P9 a Hb Ht (proj1 (A2 a) X))|].
  split; [exact P10|].
  split; [exact P11|].
  split; [rewrite (AsanLift.mat_le_halted md1 md2 M); exact P12|].
  split; [exact P13|exact P14].
Qed.

(* Two one-step facts about the mmap top (lead 03:31Z via (internal)): it is a
   function of vm_init_sp alone (LPS State.v: alloc_top h = bv_unsigned (vm_init_sp h) - stack_max_size), so the
   a_call_post vm_init_sp clause gives the alloc_top clause; and Run.valid_sp's 16-alignment with stack_max_size =
   8 * 1024 * 1024 gives the 8-alignment from the valid_sp law. *)
Lemma alloc_top_kept_of_init_sp : forall h h' : VmMaps,
  vm_init_sp h' = vm_init_sp h -> State.alloc_top h' = State.alloc_top h.
Proof. intros h h' E. unfold State.alloc_top. rewrite E. reflexivity. Qed.

Lemma alloc_top_mod8_of_valid_sp : forall h : VmMaps,
  Run.valid_sp (vm_init_sp h) -> State.alloc_top h mod 8 = 0.
Proof.
  intros h (_ & _ & E). unfold State.alloc_top, State.stack_max_size.
  pose proof (Z.div_mod (bv_unsigned (vm_init_sp h)) 16 ltac:(lia)) as Hd.
  rewrite Z.mod_divide by lia. rewrite E in Hd. exists (2 * (bv_unsigned (vm_init_sp h) / 16) - 1048576). lia.
Qed.

(* Named projections of a_call_pre, a_call_post and a_laws, one per conjunct, and their intro lemmas (round 15,
   a Theorem Labs lane 17:04Z): use these instead of destruct patterns. Names and statements stay from round 15 on; a new
   obligation is a new conjunct with a new projection; only the intro lemmas gain an argument. *)
Lemma a_call_pre_rt : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  RT (aspZ regs) mem md.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_ah : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  AH H mem md.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_ret : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  YK0s.ret_ok (getr regs 1).
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_sp_align : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  aspZ regs mod 16 = 0.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_stklo : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  stklo mem md <= aspZ regs - K.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_sp_app : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  aspZ regs < APPMEM_END.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_sp_stkhi : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  aspZ regs <= stkhi mem md.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_stkhi_app : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  stkhi mem md <= APPMEM_END.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_stack_present : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  (forall a, aspZ regs <= a < stkhi mem md -> exists b, mbyte segs mem a = Some b).
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_window : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  (forall a, a_window K regs a -> writable_at segs mem a /\ addressable mem a 1 /\ ~ in_blocks H a).
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_tp : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  getr regs 4 = Z_to_bv 64 (as_tp B).
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_ro : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  ro_agree segs mem.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_live : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  m_halted md = None.
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_win_present : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model), a_call_pre K H regs mem md ->
  (forall a, a_window K regs a -> exists b, mbyte segs mem a = Some b).
Proof. intros K H regs mem md P; unfold a_call_pre in P; decompose [and] P; assumption. Qed.

Lemma a_call_pre_intro : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  RT (aspZ regs) mem md ->
  AH H mem md ->
  YK0s.ret_ok (getr regs 1) ->
  aspZ regs mod 16 = 0 ->
  stklo mem md <= aspZ regs - K ->
  aspZ regs < APPMEM_END ->
  aspZ regs <= stkhi mem md ->
  stkhi mem md <= APPMEM_END ->
  (forall a, aspZ regs <= a < stkhi mem md -> exists b, mbyte segs mem a = Some b) ->
  (forall a, a_window K regs a -> writable_at segs mem a /\ addressable mem a 1 /\ ~ in_blocks H a) ->
  getr regs 4 = Z_to_bv 64 (as_tp B) ->
  ro_agree segs mem ->
  m_halted md = None ->
  (forall a, a_window K regs a -> exists b, mbyte segs mem a = Some b) ->
  a_call_pre K H regs mem md.
Proof.
  intros K H regs mem md P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13; unfold a_call_pre; repeat (split; [assumption|]); assumption.
Qed.

Lemma a_call_post_rt : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  RT (aspZ regs) mem' md'.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_ah : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  AH H' mem' md'.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_regs : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  a_regs_kept regs regs'.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_model : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (exists lz mt vm', md' = with_vm_backing lz mt (with_vmmaps vm' md)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_vm_limit : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_init_sp : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_stklo : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  stklo mem' md' = stklo mem md.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_stkhi : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  stkhi mem' md' = stkhi mem md.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_frame : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rt_owned H mem md a -> ~ rt_owned H' mem' md' a -> ~ a_window K regs a -> ~ (a_errno B <= a < a_errno B + 4) -> a <> as_oom B -> ~ touched a -> mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_errno_writable : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall a, a_errno B <= a < a_errno B + 4 -> (writable_at segs mem a <-> writable_at segs mem' a)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_blocks_free : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall a, in_blocks H a -> ~ touched a -> ~ rt_owned H' mem' md' a).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_win_writable : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall a, a_window K regs a -> writable_at segs mem' a).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_ro : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  ro_agree segs mem'.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_live : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  m_halted md' = None.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_tp : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_win_present : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall a, a_window K regs a -> exists b, mbyte segs mem' a = Some b).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_oom : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (writable_at segs mem (as_oom B) <-> writable_at segs mem' (as_oom B)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_thread_kept : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> word_mem segs mem' RT_TSDMAIN C /\ word_mem segs mem' (C + 152) T /\ forall i, 0 <= i < 16 -> mbyte segs mem' (T + 48 + i) = mbyte segs mem (T + 48 + i)).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_ra : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  getr regs' 1 = getr regs 1.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_oom_byte : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  mbyte segs mem' (as_oom B) = mbyte segs mem (as_oom B).
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; assumption. Qed.

Lemma a_call_post_intro : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  RT (aspZ regs) mem' md' ->
  AH H' mem' md' ->
  a_regs_kept regs regs' ->
  (exists lz mt vm', md' = with_vm_backing lz mt (with_vmmaps vm' md)) ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
  vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
  stklo mem' md' = stklo mem md ->
  stkhi mem' md' = stkhi mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rt_owned H mem md a -> ~ rt_owned H' mem' md' a -> ~ a_window K regs a -> ~ (a_errno B <= a < a_errno B + 4) -> a <> as_oom B -> ~ touched a -> mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) ->
  (forall a, a_errno B <= a < a_errno B + 4 -> (writable_at segs mem a <-> writable_at segs mem' a)) ->
  (forall a, in_blocks H a -> ~ touched a -> ~ rt_owned H' mem' md' a) ->
  (forall a, a_window K regs a -> writable_at segs mem' a) ->
  ro_agree segs mem' ->
  m_halted md' = None ->
  (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) ->
  (forall a, a_window K regs a -> exists b, mbyte segs mem' a = Some b) ->
  (writable_at segs mem (as_oom B) <-> writable_at segs mem' (as_oom B)) ->
  (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> word_mem segs mem' RT_TSDMAIN C /\ word_mem segs mem' (C + 152) T /\ forall i, 0 <= i < 16 -> mbyte segs mem' (T + 48 + i) = mbyte segs mem (T + 48 + i)) ->
  getr regs' 1 = getr regs 1 ->
  mbyte segs mem' (as_oom B) = mbyte segs mem (as_oom B) ->
  a_call_post K H regs mem md touched H' regs' mem' md'.
Proof.
  intros K H regs mem md touched H' regs' mem' md' P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19; unfold a_call_post; repeat (split; [assumption|]); assumption.
Qed.

Record a_call_post_r (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop := {
  acp_rt : RT (aspZ regs) mem' md';
  acp_ah : AH H' mem' md';
  acp_regs : a_regs_kept regs regs';
  acp_model : (exists lz mt vm', md' = with_vm_backing lz mt (with_vmmaps vm' md));
  acp_vm_limit : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md);
  acp_init_sp : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md);
  acp_stklo : stklo mem' md' = stklo mem md;
  acp_stkhi : stkhi mem' md' = stkhi mem md;
  acp_frame : (forall a, 0 <= a < 2 ^ 64 -> ~ rt_owned H mem md a -> ~ rt_owned H' mem' md' a -> ~ a_window K regs a -> ~ (a_errno B <= a < a_errno B + 4) -> a <> as_oom B -> ~ touched a -> mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a));
  acp_errno_writable : (forall a, a_errno B <= a < a_errno B + 4 -> (writable_at segs mem a <-> writable_at segs mem' a));
  acp_blocks_free : (forall a, in_blocks H a -> ~ touched a -> ~ rt_owned H' mem' md' a);
  acp_win_writable : (forall a, a_window K regs a -> writable_at segs mem' a);
  acp_ro : ro_agree segs mem';
  acp_live : m_halted md' = None;
  acp_tp : (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i));
  acp_win_present : (forall a, a_window K regs a -> exists b, mbyte segs mem' a = Some b);
  acp_oom : (writable_at segs mem (as_oom B) <-> writable_at segs mem' (as_oom B));
  acp_thread_kept : (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> word_mem segs mem' RT_TSDMAIN C /\ word_mem segs mem' (C + 152) T /\ forall i, 0 <= i < 16 -> mbyte segs mem' (T + 48 + i) = mbyte segs mem (T + 48 + i));
  acp_ra : getr regs' 1 = getr regs 1;
  acp_oom_byte : mbyte segs mem' (as_oom B) = mbyte segs mem (as_oom B)
}.

Lemma a_call_post_of_r : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  a_call_post_r K H regs mem md touched H' regs' mem' md' ->
  a_call_post K H regs mem md touched H' regs' mem' md'.
Proof. intros K H regs mem md touched H' regs' mem' md' R; destruct R; apply a_call_post_intro; assumption. Qed.

Lemma a_call_post_r_of : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  a_call_post K H regs mem md touched H' regs' mem' md' ->
  a_call_post_r K H regs mem md touched H' regs' mem' md'.
Proof. intros K H regs mem md touched H' regs' mem' md' P; unfold a_call_post in P; decompose [and] P; constructor; assumption. Qed.

Lemma a_call_post_limit : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model), a_call_post K H regs mem md touched H' regs' mem' md' ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md).
Proof. exact a_call_post_vm_limit. Qed.

Lemma a_call_post_trans :
  forall K H regs mem md T1 H1 regs1 mem1 md1 T2 H2 regs2 mem2 md2,
    a_call_post K H regs mem md T1 H1 regs1 mem1 md1 ->
    a_call_post K H1 regs1 mem1 md1 T2 H2 regs2 mem2 md2 ->
    (forall a, ~ rt_owned H mem md a -> ~ rt_owned H2 mem2 md2 a -> ~ T1 a -> ~ T2 a ->
       ~ rt_owned H1 mem1 md1 a) ->
    (forall a, in_blocks H a -> ~ T1 a -> in_blocks H1 a) ->
    a_call_post K H regs mem md (fun a => T1 a \/ T2 a) H2 regs2 mem2 md2.
Proof.
  intros K H regs mem md T1 H1 regs1 mem1 md1 T2 H2 regs2 mem2 md2 P1 P2 OWNMID BLKMID.
  pose proof (a_call_post_rt _ _ _ _ _ _ _ _ _ _ P1) as X1_rt.
  pose proof (a_call_post_ah _ _ _ _ _ _ _ _ _ _ P1) as X1_ah.
  pose proof (a_call_post_regs _ _ _ _ _ _ _ _ _ _ P1) as X1_regs.
  pose proof (a_call_post_model _ _ _ _ _ _ _ _ _ _ P1) as X1_model.
  pose proof (a_call_post_vm_limit _ _ _ _ _ _ _ _ _ _ P1) as X1_vm_limit.
  pose proof (a_call_post_init_sp _ _ _ _ _ _ _ _ _ _ P1) as X1_init_sp.
  pose proof (a_call_post_stklo _ _ _ _ _ _ _ _ _ _ P1) as X1_stklo.
  pose proof (a_call_post_stkhi _ _ _ _ _ _ _ _ _ _ P1) as X1_stkhi.
  pose proof (a_call_post_frame _ _ _ _ _ _ _ _ _ _ P1) as X1_frame.
  pose proof (a_call_post_errno_writable _ _ _ _ _ _ _ _ _ _ P1) as X1_errno_writable.
  pose proof (a_call_post_blocks_free _ _ _ _ _ _ _ _ _ _ P1) as X1_blocks_free.
  pose proof (a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ P1) as X1_win_writable.
  pose proof (a_call_post_ro _ _ _ _ _ _ _ _ _ _ P1) as X1_ro.
  pose proof (a_call_post_live _ _ _ _ _ _ _ _ _ _ P1) as X1_live.
  pose proof (a_call_post_tp _ _ _ _ _ _ _ _ _ _ P1) as X1_tp.
  pose proof (a_call_post_win_present _ _ _ _ _ _ _ _ _ _ P1) as X1_win_present.
  pose proof (a_call_post_oom _ _ _ _ _ _ _ _ _ _ P1) as X1_oom.
  pose proof (a_call_post_thread_kept _ _ _ _ _ _ _ _ _ _ P1) as X1_thread_kept.
  pose proof (a_call_post_ra _ _ _ _ _ _ _ _ _ _ P1) as X1_ra.
  pose proof (a_call_post_oom_byte _ _ _ _ _ _ _ _ _ _ P1) as X1_oom_byte.
  pose proof (a_call_post_rt _ _ _ _ _ _ _ _ _ _ P2) as X2_rt.
  pose proof (a_call_post_ah _ _ _ _ _ _ _ _ _ _ P2) as X2_ah.
  pose proof (a_call_post_regs _ _ _ _ _ _ _ _ _ _ P2) as X2_regs.
  pose proof (a_call_post_model _ _ _ _ _ _ _ _ _ _ P2) as X2_model.
  pose proof (a_call_post_vm_limit _ _ _ _ _ _ _ _ _ _ P2) as X2_vm_limit.
  pose proof (a_call_post_init_sp _ _ _ _ _ _ _ _ _ _ P2) as X2_init_sp.
  pose proof (a_call_post_stklo _ _ _ _ _ _ _ _ _ _ P2) as X2_stklo.
  pose proof (a_call_post_stkhi _ _ _ _ _ _ _ _ _ _ P2) as X2_stkhi.
  pose proof (a_call_post_frame _ _ _ _ _ _ _ _ _ _ P2) as X2_frame.
  pose proof (a_call_post_errno_writable _ _ _ _ _ _ _ _ _ _ P2) as X2_errno_writable.
  pose proof (a_call_post_blocks_free _ _ _ _ _ _ _ _ _ _ P2) as X2_blocks_free.
  pose proof (a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ P2) as X2_win_writable.
  pose proof (a_call_post_ro _ _ _ _ _ _ _ _ _ _ P2) as X2_ro.
  pose proof (a_call_post_live _ _ _ _ _ _ _ _ _ _ P2) as X2_live.
  pose proof (a_call_post_tp _ _ _ _ _ _ _ _ _ _ P2) as X2_tp.
  pose proof (a_call_post_win_present _ _ _ _ _ _ _ _ _ _ P2) as X2_win_present.
  pose proof (a_call_post_oom _ _ _ _ _ _ _ _ _ _ P2) as X2_oom.
  pose proof (a_call_post_thread_kept _ _ _ _ _ _ _ _ _ _ P2) as X2_thread_kept.
  pose proof (a_call_post_ra _ _ _ _ _ _ _ _ _ _ P2) as X2_ra.
  pose proof (a_call_post_oom_byte _ _ _ _ _ _ _ _ _ _ P2) as X2_oom_byte.
  assert (ESP : aspZ regs1 = aspZ regs).
  { unfold aspZ. f_equal. exact (X1_regs 2 ltac:(unfold a_callee_saved; lia)). }
  assert (EWIN : forall a, a_window K regs1 a <-> a_window K regs a).
  { intros a. unfold a_window. rewrite ESP. reflexivity. }
  apply a_call_post_intro.
  - (* rt: second_sp *) rewrite <- ESP. exact X2_rt.
  - (* ah: second *) exact X2_ah.
  - (* regs: regs *) intros r Hr. exact (eq_trans (X2_regs r Hr) (X1_regs r Hr)).
  - (* model: model *) destruct X1_model as (l1 & t1 & v1 & E1). destruct X2_model as (l2 & t2 & v2 & E2). exists l2, t2, v2. rewrite E2, E1. reflexivity.
  - (* vm_limit: eq *) exact (eq_trans X2_vm_limit X1_vm_limit).
  - (* init_sp: eq *) exact (eq_trans X2_init_sp X1_init_sp).
  - (* stklo: eq *) exact (eq_trans X2_stklo X1_stklo).
  - (* stkhi: eq *) exact (eq_trans X2_stkhi X1_stkhi).
  - (* frame: frame *) intros a Ha Hn Hn2 Hw He Hoom HT. assert (Hnm : ~ rt_owned H1 mem1 md1 a) by exact (OWNMID a Hn Hn2 (fun X => HT (or_introl X)) (fun X => HT (or_intror X))). destruct (X2_frame a Ha Hnm Hn2 (fun X => Hw (proj1 (EWIN a) X)) He Hoom (fun X => HT (or_intror X))) as [E2 W2]. destruct (X1_frame a Ha Hn Hnm Hw He Hoom (fun X => HT (or_introl X))) as [E1 W1]. exact (conj (eq_trans E2 E1) (iff_trans W1 W2)).
  - (* errno_writable: iff_forall *) intros a Ha. exact (iff_trans (X1_errno_writable a Ha) (X2_errno_writable a Ha)).
  - (* blocks_free: blocks_free *) intros a Hb HT. exact (X2_blocks_free a (BLKMID a Hb (fun X => HT (or_introl X))) (fun X => HT (or_intror X))).
  - (* win_writable: win *) intros a Ha. exact (X2_win_writable a (proj2 (EWIN a) Ha)).
  - (* ro: second *) exact X2_ro.
  - (* live: second *) exact X2_live.
  - (* tp: eq_forall *) intros i Hi. exact (eq_trans (X2_tp i Hi) (X1_tp i Hi)).
  - (* win_present: win *) intros a Ha. exact (X2_win_present a (proj2 (EWIN a) Ha)).
  - (* oom: iff *) exact (iff_trans X1_oom X2_oom).
  - (* thread_kept: thread_kept *) intros C T HC HCr HT HTr. destruct (X1_thread_kept C T HC HCr HT HTr) as (HC1 & HT1 & HB1). destruct (X2_thread_kept C T HC1 HCr HT1 HTr) as (HC2 & HT2 & HB2). split; [exact HC2|]. split; [exact HT2|]. intros i Hi. exact (eq_trans (HB2 i Hi) (HB1 i Hi)).
  - (* ra: eq *) exact (eq_trans X2_ra X1_ra).
  - (* oom_byte: eq *) exact (eq_trans X2_oom_byte X1_oom_byte).
Qed.

Lemma a_laws_blocks : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> p mod 16 = 0 /\ 4096 <= p /\ p + n <= stklo mem md /\ end_in_app p n /\ forall a, p <= a < p + n -> app_mem a /\ writable_at segs mem a /\ ~ a_in_img a /\ ~ a_on_img_page a /\ ~ a_in_fs B mem a).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_disjoint : a_laws ->
  (forall H1 H2 mem md p n q k, AH (H1 ++ (p, n) :: H2) mem md -> In (q, k) (H1 ++ H2) -> p + n <= q \/ q + k <= p).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_not_owned : a_laws ->
  (forall H mem md a, AH H mem md -> (in_blocks H a \/ in_slack H a \/ a_in_fs B mem a \/ stklo mem md <= a < APPMEM_END) -> ~ rt_owned H mem md a /\ ~ rt_owned H mem md (shadow_addr a)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_store : a_laws ->
  (forall H mem mem' md, AH H mem md -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_perm : a_laws ->
  (forall H H' mem md, AH H mem md -> Permutation.Permutation H H' -> AH H' mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_client : a_laws ->
  (forall H mem md a, AH H mem md -> (in_blocks a_client a -> ~ rt_owned H mem md a) /\ (a_in_img a -> ~ rt_owned H mem md (shadow_addr a)) /\ (as_tp B <= a < as_tp B + 8 -> rt_owned H mem md a)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_thread : a_laws ->
  (forall H mem md, AH H mem md -> (forall i, 0 <= i < 8 -> rt_owned H mem md (RT_TSDMAIN + i)) /\ word_mem segs mem (as_tp B - 88) RT_TSDMAIN /\ (forall i, 0 <= i < 4 -> mbyte segs mem (RT_TSDK + i) = Some (Z_to_bv 8 0)) /\ exists C T, word_mem segs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\ word_mem segs mem (C + 152) T /\ (forall i, 0 <= i < 8 -> rt_owned H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\ mbyte segs mem (T + 3168) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + 3168) /\ rt_owned H mem md (T + 3168) /\ ~ a_in_img (T + 3168) /\ app_mem (T + 3168) /\ mbyte segs mem (T + 40) = Some (Z_to_bv 8 0) /\ rt_owned H mem md (T + 40) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 8 + i)) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 48 + i) /\ exists b, mbyte segs mem (T + 48 + i) = Some b) /\ exists top bot, word_mem segs mem (T + 8) top /\ word_mem segs mem (T + 16) bot /\ 0 <= bot < top /\ 4096 <= top <= stkhi mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_settings : a_laws ->
  (forall H mem md, AH H mem md -> mbyte segs mem (as_mcs B) = Some (Z_to_bv 8 30) /\ (forall i, 1 <= i < 4 -> mbyte segs mem (as_mcs B + i) = Some (Z_to_bv 8 0)) /\ mbyte segs mem (as_mrn B) = Some (Z_to_bv 8 1) /\ (forall i, 0 <= i < 4 -> rt_owned H mem md (as_mcs B + i)) /\ rt_owned H mem md (as_mrn B)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_ro_not_owned : a_laws ->
  (forall H mem md a, AH H mem md -> a_in_ro a -> ~ rt_owned H mem md a).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_above_top : a_laws ->
  (forall H mem md a, AH H mem md -> State.alloc_top (m_vmmaps md) <= a < 2 ^ 64 -> ~ rt_owned H mem md a /\ ~ in_blocks H a).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_imem : a_laws ->
  (forall H mem md, AH H mem md -> exists T, 0 <= T < 2 ^ 64 /\ word_mem segs mem RT_IMEM T /\ forall i, 0 <= i < 3727360 -> mbyte segs mem (T + i) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + i) /\ rt_owned H mem md (T + i) /\ app_mem (T + i) /\ ~ a_in_img (T + i) /\ ~ a_in_fs B mem (T + i)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_model : a_laws ->
  (forall H mem md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_proc md' = m_proc md -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_mat : a_laws ->
  (forall H mem md acc md', materialize_model_accesses md acc = Some md' -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_owned_run : a_laws ->
  (forall H H' mem md mem' md' a, AH H mem md -> AH H' mem' md' -> stklo mem' md' = stklo mem md -> (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) -> ~ in_blk_ext H a -> ~ in_blk_ext H' a -> (rt_owned H mem md a <-> rt_owned H' mem' md' a)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_stack_high : a_laws ->
  (forall H mem md, AH H mem md -> HIGHMEM_BEG <= stklo mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_fs_place : a_laws ->
  (forall H mem md b, AH H mem md -> word_mem segs mem (as_tp B) b -> 0 <= b < 2 ^ 64 -> GT <= b /\ b + FS_SIZE <= stklo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + FS_SIZE -> app_mem a).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_block_end : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n -> app_mem (p + n + 7)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_block_high : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 2 ^ 21 <= p).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_block_slack : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> forall a, p + n <= a < p + n + (8 - n mod 8) mod 8 -> exists b, mbyte segs mem a = Some b).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_fs_state : a_laws ->
  (forall H mem md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> a_fs_ok mem FS /\ (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem segs mem (as_tp B + 8) DB /\ DB <> 0 /\ word_mem segs mem (DB + 24) (as_tp B) /\ forall a, DB + 24 <= a < DB + 32 -> app_mem a /\ a < stklo mem md /\ ~ (a_errno B <= a < a_errno B + 4) /\ ~ a_in_fs B mem a /\ ~ in_blk_ext H a /\ ~ a_in_img a /\ ~ in_blocks a_client a /\ ~ rt_owned H mem md a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i))).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_fs_store : a_laws ->
  (forall H mem mem' md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> ~ (FS <= a < FS + FS_SIZE) -> ~ (exists b, FS <= b < FS + FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> a_fs_ok mem' FS -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_imem_align : a_laws ->
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> T mod 4096 = 0).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_imem_place : a_laws ->
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> GT <= T).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_imem_cell : a_laws ->
  (forall H mem md i, AH H mem md -> 0 <= i < 8 -> ~ rt_owned H mem md (RT_IMEM + i)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_block_size : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_rest_owned : a_laws ->
  (forall H mem md a, AH H mem md -> 0 <= a < State.alloc_top (m_vmmaps md) -> ~ in_blk_ext H a -> ~ a_in_img a -> ~ a_on_img_page a -> ~ in_blocks a_client a -> ~ a_in_fs B mem a -> ~ (stklo mem md <= a < APPMEM_END) -> ~ (RT_IMEM <= a < RT_IMEM + 8) -> ~ (exists DB, word_mem segs mem (as_tp B + 8) DB /\ DB + 24 <= a < DB + 32) -> ~ (exists b, a = shadow_addr b /\ (a_in_img b \/ in_blocks a_client b \/ a_in_fs B mem b \/ State.alloc_top (m_vmmaps md) <= b < APPMEM_END)) -> rt_owned H mem md a).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_dtls_place : a_laws ->
  (forall H mem md DB, AH H mem md -> word_mem segs mem (as_tp B + 8) DB -> 0 <= DB < 2 ^ 64 -> DB + 32 <= stklo mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_slack_below : a_laws ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> p + n + (8 - n mod 8) mod 8 <= stklo mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_top_le_stklo : a_laws ->
  (forall H mem md, AH H mem md -> State.alloc_top (m_vmmaps md) <= stklo mem md).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_valid_sp : a_laws ->
  (forall H mem md, AH H mem md -> Run.valid_sp (vm_init_sp (m_vmmaps md))).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_mem_inv : a_laws ->
  (forall H mem md, AH H mem md -> Mem.mem_inv segs mem).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_tls_cells : a_laws ->
  (forall H mem md, AH H mem md -> (forall a, (as_tp B - 88 <= a < as_tp B - 80 \/ as_tp B - 8 <= a < as_tp B + 16 \/ RT_TSDMAIN <= a < RT_TSDMAIN + 8) -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall DT, word_mem segs mem (as_tp B - 8) DT -> 0 <= DT < 2 ^ 64 -> forall a, DT + 8 <= a < DT + 16 -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall a, (C + 152 <= a < C + 160 \/ T + 48 <= a < T + 64) -> a < stklo mem md /\ ~ a_in_fs B mem a)).
Proof. intros  P; unfold a_laws in P; decompose [and] P; assumption. Qed.

Lemma a_laws_intro : (forall H mem md p n, AH H mem md -> In (p, n) H -> p mod 16 = 0 /\ 4096 <= p /\ p + n <= stklo mem md /\ end_in_app p n /\ forall a, p <= a < p + n -> app_mem a /\ writable_at segs mem a /\ ~ a_in_img a /\ ~ a_on_img_page a /\ ~ a_in_fs B mem a) ->
  (forall H1 H2 mem md p n q k, AH (H1 ++ (p, n) :: H2) mem md -> In (q, k) (H1 ++ H2) -> p + n <= q \/ q + k <= p) ->
  (forall H mem md a, AH H mem md -> (in_blocks H a \/ in_slack H a \/ a_in_fs B mem a \/ stklo mem md <= a < APPMEM_END) -> ~ rt_owned H mem md a /\ ~ rt_owned H mem md (shadow_addr a)) ->
  (forall H mem mem' md, AH H mem md -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md) ->
  (forall H H' mem md, AH H mem md -> Permutation.Permutation H H' -> AH H' mem md) ->
  (forall H mem md a, AH H mem md -> (in_blocks a_client a -> ~ rt_owned H mem md a) /\ (a_in_img a -> ~ rt_owned H mem md (shadow_addr a)) /\ (as_tp B <= a < as_tp B + 8 -> rt_owned H mem md a)) ->
  (forall H mem md, AH H mem md -> (forall i, 0 <= i < 8 -> rt_owned H mem md (RT_TSDMAIN + i)) /\ word_mem segs mem (as_tp B - 88) RT_TSDMAIN /\ (forall i, 0 <= i < 4 -> mbyte segs mem (RT_TSDK + i) = Some (Z_to_bv 8 0)) /\ exists C T, word_mem segs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\ word_mem segs mem (C + 152) T /\ (forall i, 0 <= i < 8 -> rt_owned H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\ mbyte segs mem (T + 3168) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + 3168) /\ rt_owned H mem md (T + 3168) /\ ~ a_in_img (T + 3168) /\ app_mem (T + 3168) /\ mbyte segs mem (T + 40) = Some (Z_to_bv 8 0) /\ rt_owned H mem md (T + 40) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 8 + i)) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 48 + i) /\ exists b, mbyte segs mem (T + 48 + i) = Some b) /\ exists top bot, word_mem segs mem (T + 8) top /\ word_mem segs mem (T + 16) bot /\ 0 <= bot < top /\ 4096 <= top <= stkhi mem md) ->
  (forall H mem md, AH H mem md -> mbyte segs mem (as_mcs B) = Some (Z_to_bv 8 30) /\ (forall i, 1 <= i < 4 -> mbyte segs mem (as_mcs B + i) = Some (Z_to_bv 8 0)) /\ mbyte segs mem (as_mrn B) = Some (Z_to_bv 8 1) /\ (forall i, 0 <= i < 4 -> rt_owned H mem md (as_mcs B + i)) /\ rt_owned H mem md (as_mrn B)) ->
  (forall H mem md a, AH H mem md -> a_in_ro a -> ~ rt_owned H mem md a) ->
  (forall H mem md a, AH H mem md -> State.alloc_top (m_vmmaps md) <= a < 2 ^ 64 -> ~ rt_owned H mem md a /\ ~ in_blocks H a) ->
  (forall H mem md, AH H mem md -> exists T, 0 <= T < 2 ^ 64 /\ word_mem segs mem RT_IMEM T /\ forall i, 0 <= i < 3727360 -> mbyte segs mem (T + i) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + i) /\ rt_owned H mem md (T + i) /\ app_mem (T + i) /\ ~ a_in_img (T + i) /\ ~ a_in_fs B mem (T + i)) ->
  (forall H mem md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_proc md' = m_proc md -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md) ->
  (forall H mem md acc md', materialize_model_accesses md acc = Some md' -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md) ->
  (forall H H' mem md mem' md' a, AH H mem md -> AH H' mem' md' -> stklo mem' md' = stklo mem md -> (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) -> ~ in_blk_ext H a -> ~ in_blk_ext H' a -> (rt_owned H mem md a <-> rt_owned H' mem' md' a)) ->
  (forall H mem md, AH H mem md -> HIGHMEM_BEG <= stklo mem md) ->
  (forall H mem md b, AH H mem md -> word_mem segs mem (as_tp B) b -> 0 <= b < 2 ^ 64 -> GT <= b /\ b + FS_SIZE <= stklo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + FS_SIZE -> app_mem a) ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n -> app_mem (p + n + 7)) ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 2 ^ 21 <= p) ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> forall a, p + n <= a < p + n + (8 - n mod 8) mod 8 -> exists b, mbyte segs mem a = Some b) ->
  (forall H mem md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> a_fs_ok mem FS /\ (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem segs mem (as_tp B + 8) DB /\ DB <> 0 /\ word_mem segs mem (DB + 24) (as_tp B) /\ forall a, DB + 24 <= a < DB + 32 -> app_mem a /\ a < stklo mem md /\ ~ (a_errno B <= a < a_errno B + 4) /\ ~ a_in_fs B mem a /\ ~ in_blk_ext H a /\ ~ a_in_img a /\ ~ in_blocks a_client a /\ ~ rt_owned H mem md a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i))) ->
  (forall H mem mem' md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> ~ (FS <= a < FS + FS_SIZE) -> ~ (exists b, FS <= b < FS + FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> a_fs_ok mem' FS -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md) ->
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> T mod 4096 = 0) ->
  (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> GT <= T) ->
  (forall H mem md i, AH H mem md -> 0 <= i < 8 -> ~ rt_owned H mem md (RT_IMEM + i)) ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n) ->
  (forall H mem md a, AH H mem md -> 0 <= a < State.alloc_top (m_vmmaps md) -> ~ in_blk_ext H a -> ~ a_in_img a -> ~ a_on_img_page a -> ~ in_blocks a_client a -> ~ a_in_fs B mem a -> ~ (stklo mem md <= a < APPMEM_END) -> ~ (RT_IMEM <= a < RT_IMEM + 8) -> ~ (exists DB, word_mem segs mem (as_tp B + 8) DB /\ DB + 24 <= a < DB + 32) -> ~ (exists b, a = shadow_addr b /\ (a_in_img b \/ in_blocks a_client b \/ a_in_fs B mem b \/ State.alloc_top (m_vmmaps md) <= b < APPMEM_END)) -> rt_owned H mem md a) ->
  (forall H mem md DB, AH H mem md -> word_mem segs mem (as_tp B + 8) DB -> 0 <= DB < 2 ^ 64 -> DB + 32 <= stklo mem md) ->
  (forall H mem md p n, AH H mem md -> In (p, n) H -> p + n + (8 - n mod 8) mod 8 <= stklo mem md) ->
  (forall H mem md, AH H mem md -> State.alloc_top (m_vmmaps md) <= stklo mem md) ->
  (forall H mem md, AH H mem md -> Run.valid_sp (vm_init_sp (m_vmmaps md))) ->
  (forall H mem md, AH H mem md -> Mem.mem_inv segs mem) ->
  (forall H mem md, AH H mem md -> (forall a, (as_tp B - 88 <= a < as_tp B - 80 \/ as_tp B - 8 <= a < as_tp B + 16 \/ RT_TSDMAIN <= a < RT_TSDMAIN + 8) -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall DT, word_mem segs mem (as_tp B - 8) DT -> 0 <= DT < 2 ^ 64 -> forall a, DT + 8 <= a < DT + 16 -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall a, (C + 152 <= a < C + 160 \/ T + 48 <= a < T + 64) -> a < stklo mem md /\ ~ a_in_fs B mem a)) ->
  a_laws.
Proof.
  intros P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31; unfold a_laws; repeat (split; [assumption|]); assumption.
Qed.

Record a_laws_r : Prop := {
  al_blocks : (forall H mem md p n, AH H mem md -> In (p, n) H -> p mod 16 = 0 /\ 4096 <= p /\ p + n <= stklo mem md /\ end_in_app p n /\ forall a, p <= a < p + n -> app_mem a /\ writable_at segs mem a /\ ~ a_in_img a /\ ~ a_on_img_page a /\ ~ a_in_fs B mem a);
  al_disjoint : (forall H1 H2 mem md p n q k, AH (H1 ++ (p, n) :: H2) mem md -> In (q, k) (H1 ++ H2) -> p + n <= q \/ q + k <= p);
  al_not_owned : (forall H mem md a, AH H mem md -> (in_blocks H a \/ in_slack H a \/ a_in_fs B mem a \/ stklo mem md <= a < APPMEM_END) -> ~ rt_owned H mem md a /\ ~ rt_owned H mem md (shadow_addr a));
  al_store : (forall H mem mem' md, AH H mem md -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md);
  al_perm : (forall H H' mem md, AH H mem md -> Permutation.Permutation H H' -> AH H' mem md);
  al_client : (forall H mem md a, AH H mem md -> (in_blocks a_client a -> ~ rt_owned H mem md a) /\ (a_in_img a -> ~ rt_owned H mem md (shadow_addr a)) /\ (as_tp B <= a < as_tp B + 8 -> rt_owned H mem md a));
  al_thread : (forall H mem md, AH H mem md -> (forall i, 0 <= i < 8 -> rt_owned H mem md (RT_TSDMAIN + i)) /\ word_mem segs mem (as_tp B - 88) RT_TSDMAIN /\ (forall i, 0 <= i < 4 -> mbyte segs mem (RT_TSDK + i) = Some (Z_to_bv 8 0)) /\ exists C T, word_mem segs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\ word_mem segs mem (C + 152) T /\ (forall i, 0 <= i < 8 -> rt_owned H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\ mbyte segs mem (T + 3168) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + 3168) /\ rt_owned H mem md (T + 3168) /\ ~ a_in_img (T + 3168) /\ app_mem (T + 3168) /\ mbyte segs mem (T + 40) = Some (Z_to_bv 8 0) /\ rt_owned H mem md (T + 40) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 8 + i)) /\ (forall i, 0 <= i < 16 -> rt_owned H mem md (T + 48 + i) /\ exists b, mbyte segs mem (T + 48 + i) = Some b) /\ exists top bot, word_mem segs mem (T + 8) top /\ word_mem segs mem (T + 16) bot /\ 0 <= bot < top /\ 4096 <= top <= stkhi mem md);
  al_settings : (forall H mem md, AH H mem md -> mbyte segs mem (as_mcs B) = Some (Z_to_bv 8 30) /\ (forall i, 1 <= i < 4 -> mbyte segs mem (as_mcs B + i) = Some (Z_to_bv 8 0)) /\ mbyte segs mem (as_mrn B) = Some (Z_to_bv 8 1) /\ (forall i, 0 <= i < 4 -> rt_owned H mem md (as_mcs B + i)) /\ rt_owned H mem md (as_mrn B));
  al_ro_not_owned : (forall H mem md a, AH H mem md -> a_in_ro a -> ~ rt_owned H mem md a);
  al_above_top : (forall H mem md a, AH H mem md -> State.alloc_top (m_vmmaps md) <= a < 2 ^ 64 -> ~ rt_owned H mem md a /\ ~ in_blocks H a);
  al_imem : (forall H mem md, AH H mem md -> exists T, 0 <= T < 2 ^ 64 /\ word_mem segs mem RT_IMEM T /\ forall i, 0 <= i < 3727360 -> mbyte segs mem (T + i) = Some (Z_to_bv 8 0) /\ writable_at segs mem (T + i) /\ rt_owned H mem md (T + i) /\ app_mem (T + i) /\ ~ a_in_img (T + i) /\ ~ a_in_fs B mem (T + i));
  al_model : (forall H mem md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_proc md' = m_proc md -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md);
  al_mat : (forall H mem md acc md', materialize_model_accesses md acc = Some md' -> (AH H mem md -> AH H mem md') /\ (forall a, rt_owned H mem md' a <-> rt_owned H mem md a) /\ stklo mem md' = stklo mem md /\ stkhi mem md' = stkhi mem md);
  al_owned_run : (forall H H' mem md mem' md' a, AH H mem md -> AH H' mem' md' -> stklo mem' md' = stklo mem md -> (forall i, 0 <= i < 16 -> mbyte segs mem' (as_tp B + i) = mbyte segs mem (as_tp B + i)) -> ~ in_blk_ext H a -> ~ in_blk_ext H' a -> (rt_owned H mem md a <-> rt_owned H' mem' md' a));
  al_stack_high : (forall H mem md, AH H mem md -> HIGHMEM_BEG <= stklo mem md);
  al_fs_place : (forall H mem md b, AH H mem md -> word_mem segs mem (as_tp B) b -> 0 <= b < 2 ^ 64 -> GT <= b /\ b + FS_SIZE <= stklo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + FS_SIZE -> app_mem a);
  al_block_end : (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n -> app_mem (p + n + 7));
  al_block_high : (forall H mem md p n, AH H mem md -> In (p, n) H -> 2 ^ 21 <= p);
  al_block_slack : (forall H mem md p n, AH H mem md -> In (p, n) H -> forall a, p + n <= a < p + n + (8 - n mod 8) mod 8 -> exists b, mbyte segs mem a = Some b);
  al_fs_state : (forall H mem md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> a_fs_ok mem FS /\ (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem segs mem (as_tp B + 8) DB /\ DB <> 0 /\ word_mem segs mem (DB + 24) (as_tp B) /\ forall a, DB + 24 <= a < DB + 32 -> app_mem a /\ a < stklo mem md /\ ~ (a_errno B <= a < a_errno B + 4) /\ ~ a_in_fs B mem a /\ ~ in_blk_ext H a /\ ~ a_in_img a /\ ~ in_blocks a_client a /\ ~ rt_owned H mem md a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i)));
  al_fs_store : (forall H mem mem' md FS, AH H mem md -> word_mem segs mem (as_tp B) FS -> 0 <= FS < 2 ^ 64 -> (forall a, 0 <= a < 2 ^ 64 -> ~ a_store_ok H (stklo mem md) a -> ~ (FS <= a < FS + FS_SIZE) -> ~ (exists b, FS <= b < FS + FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> writable_at segs mem a -> writable_at segs mem' a) -> a_fs_ok mem' FS -> AH H mem' md /\ (forall a, rt_owned H mem' md a <-> rt_owned H mem md a) /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md);
  al_imem_align : (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> T mod 4096 = 0);
  al_imem_place : (forall H mem md T, AH H mem md -> word_mem segs mem RT_IMEM T -> 0 <= T < 2 ^ 64 -> GT <= T);
  al_imem_cell : (forall H mem md i, AH H mem md -> 0 <= i < 8 -> ~ rt_owned H mem md (RT_IMEM + i));
  al_block_size : (forall H mem md p n, AH H mem md -> In (p, n) H -> 0 < n);
  al_rest_owned : (forall H mem md a, AH H mem md -> 0 <= a < State.alloc_top (m_vmmaps md) -> ~ in_blk_ext H a -> ~ a_in_img a -> ~ a_on_img_page a -> ~ in_blocks a_client a -> ~ a_in_fs B mem a -> ~ (stklo mem md <= a < APPMEM_END) -> ~ (RT_IMEM <= a < RT_IMEM + 8) -> ~ (exists DB, word_mem segs mem (as_tp B + 8) DB /\ DB + 24 <= a < DB + 32) -> ~ (exists b, a = shadow_addr b /\ (a_in_img b \/ in_blocks a_client b \/ a_in_fs B mem b \/ State.alloc_top (m_vmmaps md) <= b < APPMEM_END)) -> rt_owned H mem md a);
  al_dtls_place : (forall H mem md DB, AH H mem md -> word_mem segs mem (as_tp B + 8) DB -> 0 <= DB < 2 ^ 64 -> DB + 32 <= stklo mem md);
  al_slack_below : (forall H mem md p n, AH H mem md -> In (p, n) H -> p + n + (8 - n mod 8) mod 8 <= stklo mem md);
  al_top_le_stklo : (forall H mem md, AH H mem md -> State.alloc_top (m_vmmaps md) <= stklo mem md);
  al_valid_sp : (forall H mem md, AH H mem md -> Run.valid_sp (vm_init_sp (m_vmmaps md)));
  al_mem_inv : (forall H mem md, AH H mem md -> Mem.mem_inv segs mem);
  al_tls_cells : (forall H mem md, AH H mem md -> (forall a, (as_tp B - 88 <= a < as_tp B - 80 \/ as_tp B - 8 <= a < as_tp B + 16 \/ RT_TSDMAIN <= a < RT_TSDMAIN + 8) -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall DT, word_mem segs mem (as_tp B - 8) DT -> 0 <= DT < 2 ^ 64 -> forall a, DT + 8 <= a < DT + 16 -> a < stklo mem md /\ ~ a_in_fs B mem a) /\ (forall C T, word_mem segs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem segs mem (C + 152) T -> 0 <= T < 2 ^ 64 -> forall a, (C + 152 <= a < C + 160 \/ T + 48 <= a < T + 64) -> a < stklo mem md /\ ~ a_in_fs B mem a))
}.

Lemma a_laws_of_r : a_laws_r ->
  a_laws.
Proof. intros R; destruct R; apply a_laws_intro; assumption. Qed.

Lemma a_laws_r_of : a_laws ->
  a_laws_r.
Proof. intros P; unfold a_laws in P; decompose [and] P; constructor; assumption. Qed.

(* The mmap top is kept across every entry: a_call_post's vm_init_sp clause, through alloc_top_kept_of_init_sp (the
   released alloc_top_isp). A projection LEMMA, not a conjunct: the fact is the vm_init_sp clause read through
   State.alloc_top's definition (a Theorem Labs lane 04:07Z; G1 of the relay lanes, a Theorem Labs lane's a_init_sp_kept). *)
Lemma a_call_post_top : forall (K : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (touched : Z -> Prop) (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model),
  a_call_post K H regs mem md touched H' regs' mem' md' ->
  State.alloc_top (m_vmmaps md') = State.alloc_top (m_vmmaps md).
Proof.
  intros K H regs mem md touched H' regs' mem' md' P.
  exact (alloc_top_kept_of_init_sp _ _ (a_call_post_init_sp K H regs mem md touched H' regs' mem' md' P)).
Qed.

(* The mmap top is 8-aligned at every AH state: a_laws' valid_sp law through alloc_top_mod8_of_valid_sp. A LEMMA, not a
   law (a Theorem Labs lane 04:31Z / 05:14Z: the round ships valid_sp only; consumers get mod 8 from its 16-alignment). G2 of the
   relay lanes is premise-free with it. *)
Lemma a_laws_top_mod8 : a_laws ->
  forall H mem md, AH H mem md -> State.alloc_top (m_vmmaps md) mod 8 = 0.
Proof. intros L H mem md HA. exact (alloc_top_mod8_of_valid_sp _ (a_laws_valid_sp L H mem md HA)). Qed.

(* Every entry's end state satisfies lib/Lib/Mem.v's mem_inv: a_call_post's AH conjunct through the mem_inv law. *)
Lemma a_call_post_mem_inv : a_laws -> forall K H regs mem md touched H' regs' mem' md',
  a_call_post K H regs mem md touched H' regs' mem' md' -> Mem.mem_inv segs mem'.
Proof.
  intros L K H regs mem md touched H' regs' mem' md' P.
  exact (a_laws_mem_inv L H' mem' md' (a_call_post_ah K H regs mem md touched H' regs' mem' md' P)).
Qed.

End AContracts.

(* Where a live block and its word slack lie with respect to the model's mmap top (alloc_top <= stklo, so AH1's
   p + n <= stklo does not place a block below alloc_top): by a_laws_above_top nothing at or above alloc_top is in a
   live block, and a block of n > 0 bytes ends inside AppMem; the slack forms use that alloc_top is a multiple of 8.
   The four statements are character-identical to fuzz_reply's lib/A/ContractPlace.v copies
   (a working branch 3bcb4cdf17e :165, :187, :202, :345); a_live_slack_below_top_of_valid_sp's proof cites
   alloc_top_mod8_of_valid_sp above (the same statement as that file's a_top_mod8_of_valid_sp). A name that covers the
   word slack carries "slack" (a Theorem Labs lane 2026-10-27 21:45Z). *)
Section ALiveBelowTop.
Variable B : asan_syms.
Variable AH : list (Z * Z) -> (word -> option byte) -> Model -> Prop.
Variable rt_owned : list (Z * Z) -> (word -> option byte) -> Model -> Z -> Prop.
Variable stklo stkhi : (word -> option byte) -> Model -> Z.

Lemma a_live_below_top : a_laws B AH rt_owned stklo stkhi ->
  forall H mem md p n, AH H mem md -> In (p, n) H ->
    p + n <= State.alloc_top (m_vmmaps md).
Proof.
  intros L H mem md p n HAH Hin.
  pose proof (a_laws_block_size _ _ _ _ _ L H mem md p n HAH Hin) as Hn.
  destruct (Z.le_gt_cases (p + n) (State.alloc_top (m_vmmaps md))) as [Hle | Hgt]; [exact Hle|].
  exfalso.
  destruct (a_laws_blocks _ _ _ _ _ L H mem md p n HAH Hin) as (_ & _ & _ & Hend & _).
  assert (Happ : app_mem (p + n)) by (destruct Hend as [E | E]; [lia | exact E]).
  assert (Htop : State.alloc_top (m_vmmaps md) < p + n) by lia.
  assert (Hb : in_blocks H (Z.max p (State.alloc_top (m_vmmaps md)))).
  { exists p, n. split; [exact Hin | lia]. }
  assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hlt : Z.max p (State.alloc_top (m_vmmaps md)) < 2 ^ 64).
  { unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ. lia. }
  destruct (a_laws_above_top _ _ _ _ _ L H mem md (Z.max p (State.alloc_top (m_vmmaps md))) HAH
              (conj (Z.le_max_r _ _) Hlt)) as (_ & Hnb).
  exact (Hnb Hb).
Qed.

Lemma a_in_blocks_below_top : a_laws B AH rt_owned stklo stkhi ->
  forall H mem md a, AH H mem md -> in_blocks H a -> a < State.alloc_top (m_vmmaps md).
Proof.
  intros L H mem md a HAH (p & n & Hin & Hr).
  pose proof (a_live_below_top L H mem md p n HAH Hin) as Hb. lia.
Qed.

Lemma a_live_slack_below_top_of_top8 : a_laws B AH rt_owned stklo stkhi ->
  forall H mem md p n, AH H mem md -> In (p, n) H ->
    State.alloc_top (m_vmmaps md) mod 8 = 0 ->
    p + n + (8 - n mod 8) mod 8 <= State.alloc_top (m_vmmaps md).
Proof.
  intros L H mem md p n HAH Hin Halign.
  pose proof (a_live_below_top L H mem md p n HAH Hin) as Hbytes.
  pose proof (a_laws_block_size _ _ _ _ _ L H mem md p n HAH Hin) as Hn.
  destruct (a_laws_blocks _ _ _ _ _ L H mem md p n HAH Hin) as (Hp16 & _ & _ & _ & _).
  pose proof (Z.div_mod p 16 ltac:(lia)) as Hpd.
  pose proof (Z.div_mod n 8 ltac:(lia)) as Hnd.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hnr.
  pose proof (Z.div_mod (State.alloc_top (m_vmmaps md)) 8 ltac:(lia)) as Htd.
  destruct (Z.eq_dec (n mod 8) 0) as [Hz | Hz].
  - rewrite Hz. change ((8 - 0) mod 8) with 0. lia.
  - rewrite (Z.mod_small (8 - n mod 8) 8) by lia. lia.
Qed.

Lemma a_live_slack_below_top_of_valid_sp : a_laws B AH rt_owned stklo stkhi ->
  forall H mem md p n, AH H mem md -> In (p, n) H ->
    valid_sp (vm_init_sp (m_vmmaps md)) ->
    p + n + (8 - n mod 8) mod 8 <= State.alloc_top (m_vmmaps md).
Proof.
  intros L H mem md p n HAH Hin Hsp.
  apply (a_live_slack_below_top_of_top8 L H mem md p n HAH Hin).
  apply alloc_top_mod8_of_valid_sp, Hsp.
Qed.

End ALiveBelowTop.

(* The side stack's flag bytes (one per fake frame, a_fs_flag) are kept across every entry, except a flag the call's
   touched set names: each lies in FS, so neither state's allocator owns it (a_laws_not_owned; the base word at tp is
   kept, a_call_post_tp), below the window (a_laws_fs_place, a_call_pre_stklo), and above GT, so off errno and the OOM
   flag (this image's tp and flag lie below GT; startcert/acontract.py asserts both at render). The text of
   fuzz_command's fs14k_keep / fs14_kept_post (lib/A/Prog/Fs14K.v, a working branch 6a8236a8ccc) over every class
   c <= 10 and Contract.v's layout, with the touched exception. *)
Section AFsFlagsKept.
Variable RT : Z -> (word -> option byte) -> Model -> Prop.
Variable AH : list (Z * Z) -> (word -> option byte) -> Model -> Prop.
Variable rt_owned : list (Z * Z) -> (word -> option byte) -> Model -> Z -> Prop.
Variable stklo stkhi : (word -> option byte) -> Model -> Z.

Lemma a_call_post_fs_flags_kept : forall K H regs mem md (touched : Z -> Prop) H' regs' mem' md',
  a_laws ASYMS AH rt_owned stklo stkhi ->
  a_call_pre ASYMS RT AH stklo stkhi K H regs mem md ->
  a_call_post ASYMS RT AH rt_owned stklo stkhi K H regs mem md touched H' regs' mem' md' ->
  forall FS c j, word_mem rsegs mem (as_tp ASYMS) FS -> 0 <= FS < 2 ^ 64 -> (c <= 10)%nat -> 0 <= j < a_fs_M c ->
    ~ touched (a_fs_flag FS c j) ->
    mbyte rsegs mem' (a_fs_flag FS c j) = mbyte rsegs mem (a_fs_flag FS c j).
Proof.
  intros K H regs mem md touched H' regs' mem' md' L PRE P FS c j WB RB HC HJ NT.
  pose proof (a_call_pre_ah _ _ _ _ _ _ _ _ _ _ PRE) as AH0.
  pose proof (a_call_pre_stklo _ _ _ _ _ _ _ _ _ _ PRE) as SLO.
  pose proof (a_call_post_ah _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P) as AH1.
  pose proof (a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P) as KP.
  pose proof (a_call_post_tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P) as TPK.
  destruct (a_laws_fs_place _ _ _ _ _ L H mem md FS AH0 WB RB) as (FGT & FHI & _ & FAPP).
  unfold FS_SIZE in FHI, FAPP.
  assert (FLR : FS <= a_fs_flag FS c j < FS + 36864).
  { unfold a_fs_flag. unfold a_fs_M in HJ.
    assert (E : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
    { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia. apply Z.pow_succ_r. lia. }
    assert (U : 2 ^ (14 - Z.of_nat c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
    assert (P0 : 0 < 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
    change (2 ^ 15) with 32768. change (2 ^ 14) with 16384 in U. lia. }
  assert (FA : app_mem (a_fs_flag FS c j)) by (apply FAPP; lia).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in FA.
  assert (WB' : word_mem rsegs mem' (as_tp ASYMS) FS).
  { intros k Hk. rewrite (TPK (Z.of_nat k) ltac:(lia)). exact (WB k Hk). }
  assert (INF : a_in_fs ASYMS mem (a_fs_flag FS c j)).
  { exists FS. split; [exact RB|]. split; [exact WB | unfold FS_SIZE; lia]. }
  assert (INF' : a_in_fs ASYMS mem' (a_fs_flag FS c j)).
  { exists FS. split; [exact RB|]. split; [exact WB' | unfold FS_SIZE; lia]. }
  assert (TG : a_errno ASYMS + 4 <= GT) by (unfold a_errno, ASYMS, GT; cbn [as_tp]; lia).
  assert (OG : as_oom ASYMS < GT) by (unfold ASYMS, GT; cbn [as_oom]; lia).
  refine (proj1 (KP (a_fs_flag FS c j) _ _ _ _ _ _ NT)).
  - change (2 ^ 64) with 18446744073709551616. lia.
  - exact (proj1 (a_laws_not_owned _ _ _ _ _ L H mem md _ AH0 (or_intror (or_intror (or_introl INF))))).
  - exact (proj1 (a_laws_not_owned _ _ _ _ _ L H' mem' md' _ AH1 (or_intror (or_intror (or_introl INF'))))).
  - intros Wa. unfold a_window in Wa. lia.
  - lia.
  - lia.
Qed.

End AFsFlagsKept.

(* What the frame's ASan layer provides for this image (the analogue of the plain AllocAPI), given the runtime
   invariant RT of struct.asan.runtime. *)
Record AsanAllocAPI (B : asan_syms) (RT : Z -> (word -> option byte) -> Model -> Prop) := {
  aa_AH : list (Z * Z) -> (word -> option byte) -> Model -> Prop;
  aa_owned : list (Z * Z) -> (word -> option byte) -> Model -> Z -> Prop;
  aa_stklo : (word -> option byte) -> Model -> Z;
  aa_stkhi : (word -> option byte) -> Model -> Z;
  aa_laws : a_laws B aa_AH aa_owned aa_stklo aa_stkhi;
  aa_malloc : forall {fx : YK11.FPState}, amalloc_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_malloc_body : forall {fx : YK11.FPState}, amalloc_body_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_malloc_inner : forall {fx : YK11.FPState}, amalloc_inner_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_free : forall {fx : YK11.FPState}, afree_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_free_body : forall {fx : YK11.FPState}, afree_body_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_free_null : forall {fx : YK11.FPState}, afree_null_contract B RT aa_AH aa_owned aa_stklo aa_stkhi;
  aa_realloc : forall {fx : YK11.FPState} pc, as_realloc B = Some pc ->
    arealloc_contract B RT aa_AH aa_owned aa_stklo aa_stkhi pc /\
    arealloc_null_contract B RT aa_AH aa_owned aa_stklo aa_stkhi pc;
  aa_calloc : forall {fx : YK11.FPState} pc, as_calloc B = Some pc ->
    acalloc_contract B RT aa_AH aa_owned aa_stklo aa_stkhi pc
}.
