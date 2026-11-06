(* The machine contract of receive (fuzz/fuzz_transport.c:995-1025 of the harness fix on 835f336c, c47f6290;
   fuzz_dup and spec_read_frame inlined) in the plain image, and the pieces the SR contracts of the harness functions
   that call the allocator share (receive, build_and_receive, LLVMFuzzerTestOneInput). *)
(* receive at 0x14afc, 556 bytes (the patched image; the pin's receive is another function, 620 bytes).
   addi sp,sp,-48 at 0x14afc (ra, s0-s4 saved). Callees: malloc (0x14b30, a0 = n ? n : 1), memcpy (0x14b4c, only
   when n != 0), memset twice (0x14b64, 0x14b74: op_begin's memset of OW and GOT), diginet_session_poll (0x14c68,
   by_poll != 0), m_rx (0x14c80) and diginet_session_rx (0x14c9c) (by_poll = 0), settle (0x14ca4), and free as a
   tail call (j at 0x14cc8 after the epilogue, so from receive's entry sp); abort (0x14d24) when malloc returns NULL.
   FRAME 8240 = 48 + ALLOC_STACK (8192, malloc's window below receive's own frame); every other callee window is
   smaller (diginet_session_poll 3840, diginet_session_rx 2272, m_rx 144, settle 80, memcpy / memset 0), and free's
   window [sp - 8192, sp) lies inside [sp - 8240, sp).
   The contract is an SR contract (Reusable/YM06.v SR, as the kit's malloc_contract / free_contract,
   Contract.v:91-113, and the donor's segment contracts, fuzz_decode Prog/fd_segments_c.v): the allocator state
   (L, A, md) goes in and comes out. The evt contracts of the callees that do not allocate are cut in by evt_SR
   (Contract.v:24), after MemNorm.v evt_normalize. The heap frame's address a is chosen by malloc, so the model premise quantifies over it
   (every a that a successful malloc can return: 0 < a, a + 65536 <= 2^64) and the post names the a malloc
   returned: the world after is receive_m's at that a (m_rx stores pointers into the frame). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
Import ListNotations.
Local Open Scope Z_scope.

Definition receive_ENTRY : Z := 0x14afc.
Definition receive_FRAME : Z := 48 + ALLOC_STACK.

(* The plain image's allocator entries and guards (FrameAPI.v frame_plain). *)
Definition H_MALLOC : Z := 0x18aa0.
Definition H_FREE : Z := 0x18960.
Definition H_GUARD_GOT : Z := 0x214e0.
Definition H_GUARD : Z := 0x62b20.

(* The world, as a footprint: the bytes a harness function may change outside its stack window and the heap. *)
Definition h_world (x : Z) : Prop := W_BASE_PLAIN <= x < W_BASE_PLAIN + W_LEN.

(* The heap-frame addresses the model is asked about: every address a successful malloc returns (fresh_block,
   Contract.v:73, and alloc_ceiling below 2^63 give it). TSim's heap_ok (TSim/LoopOk.v) asks the same of each A k. *)
Definition h_addr_ok (a : Z) : Prop := 0 < a /\ a + 65536 <= 2 ^ 64.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* The allocator's symbols of the image, and the world apart from what the allocator owns statically, its context
   and errno: receive writes the world between malloc and free, and the allocator invariant (aa_MR) asks every
   byte it owns to stay. The world clause is FrameAPI.v frame_plain's clause over frame_G (Prog/T/GI.v
   frame_G_clause proves it from the symbol values; frame_G_world turns in_globals frame_G into h_world). errno lies
   below alloc_ceiling (malloc and free may write errno as scratch; a caller keeps its frame cells across them only
   if errno is below the stack): FrameAPI.v frame_plain gives it (errno_addr B + 4 <= alloc_ceiling). The RELRO block of
   TContract.v (relro_img, which h_post carries across malloc and free; .data.rel.ro lies in the writable LOAD
   segment) is apart from the allocator the same way: the frame's frame_RELRO clause gives it ([0x213c8, 0x21460) inside frame_RELRO's first block [0x213b8, 0x214e0)). *)
Definition h_binds : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = H_MALLOC /\ ms_free B = H_FREE /\
  ms_got_guard B = H_GUARD_GOT /\ ms_guard B = H_GUARD /\ AllocExtra B MR /\
  errno_addr B + 4 <= alloc_ceiling /\ ms_ctx B + CTX_SIZE <= alloc_ceiling /\
  (forall a, h_world a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, RELRO_BASE <= a < RELRO_BASE + RELRO_LEN -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)).

(* The n bytes at p that a harness function reads through its argument (receive's p, build_and_receive's body):
   none (n = 0), or bytes off the world inside a user block of A (the input payload, LLVMFuzzerTestOneInput's data)
   or above the caller's sp (a caller's stack buffer: build_and_receive's frame[], op_announce's body[]). Either
   way the allocator keeps them (call_post_k) and the function's own stack window does not reach them. *)
Definition h_src (L : layout) (A : astate) (sp p n : Z) : Prop :=
  n = 0 \/
  (off_world p n /\
   ((exists q k, In (q, k) (user_blocks A) /\ ptr_addr L q <= p /\ p + n <= ptr_addr L q + k) \/
    (sp <= p /\ p + n <= 2 ^ 63))).

(* The state a harness function that allocates is entered in: the allocator's call_pre_k with a window of K bytes
   (ret_ok ra, sp 16-aligned with alloc_ceiling + K <= sp < 2^63, the window writable, tp, errno writable), the
   allocator initialised, the machine model running, read-only memory read as the image (ro_agree, a value-level
   fact: what the allocator's contracts ask and give; no mem_inv, which free's and malloc's contracts do not keep),
   the budget b, the world Bw (wmem, Prog/T/WMem.v) with its facts the session contracts carry (g_fail_next Bw <= 1,
   relro_img), and the window above the world. A walk reaches its evt callees from ro_agree through MemNorm.v
   evt_normalize / evt_rodata and RoAdapt.v's *_norm / *_back lemmas, as the donor's walks do. *)
Definition h_pre (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (b : sbound) (Bw : list byte) : Prop :=
  call_pre_k B MR K L A regs mem md /\ st_init_done A = true /\
  m_halted md = None /\ m_vm_lazy md = [] /\
  ro_agree segs mem /\
  res_ok_slots A b /\
  w_off_stack W_BASE_PLAIN (getr regs 2) K /\
  wmem rsegs mem Bw /\ g_fail_next Bw <= 1 /\ relro_img mem.

(* The state such a function returns in, at ra (getr regs 1): the allocator's call_post_k with the footprint E
   (the world, and whatever heap block the function allocated and freed), the user blocks and the block list
   back as they were, the budget b again, read-only memory intact, the guard kept, and the world Bw'. *)
Definition h_post (K : Z) (E : Z -> Prop) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (b : sbound) (Bw' : list byte) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B MR K L A regs mem md E L' A' regs' mem' md' /\
    st_init_done A' = true /\ m_halted md' = None /\ m_vm_lazy md' = [] /\
    blocks L' A' = blocks L A /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' b /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    wmem rsegs mem' Bw' /\ g_fail_next Bw' <= 1 /\ relro_img mem'.

(* The premises of receive (p, n, by_poll, poll_flags) besides the budget: a0 = p, a1 = n = length bytes
   (size_t), a2 = by_poll (int), a3 = poll_flags (unsigned: its low 32 bits). The callers: LLVMFuzzerTestOneInput's
   ops 0 and 8 (a record of the input: p in the payload block, n <= 65535) and build_and_receive (p its frame[] on
   its stack, n <= 1514). *)
Definition receive_args (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (Bw : list byte) (p : Z) (bytes : list byte) (by_poll pf : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 p /\
  getr regs 11 = Z_to_bv 64 (Z.of_nat (length bytes)) /\
  getr regs 12 = Z_to_bv 64 by_poll /\ - 2 ^ 31 <= by_poll < 2 ^ 31 /\
  bv_unsigned (getr regs 13) mod 2 ^ 32 = pf /\ 0 <= pf < 2 ^ 32 /\
  Z.of_nat (length bytes) <= 65535 /\
  blk_data B mem p bytes /\
  h_src L A (spZ regs) p (Z.of_nat (length bytes)) /\
  (forall a, h_addr_ok a -> receive_m timg_plain Bw a bytes by_poll pf <> None).

(* What receive returns in: the heap frame a malloc returned (below alloc_ceiling, malloc_ret's fresh_block, so
   that a caller's saved registers above its sp lie outside the freed frame; and off the image, fresh_block too),
   the world receive_m gives at it.
   The footprint E: the world, the freed frame, and the allocator's ctx (a ctx byte malloc takes and free gives
   back is owned only in between, so neither call_post_k keeps it; the kit's lib_post excludes ctx too). *)
Definition receive_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (b : sbound) (Bw : list byte) (bytes : list byte) (by_poll pf : Z) (c' : config) : Prop :=
  exists (a : Z) (Bw' : list byte),
    h_addr_ok a /\ a + Z.max 1 (Z.of_nat (length bytes)) <= alloc_ceiling /\
    (forall i, 0 <= i < Z.max 1 (Z.of_nat (length bytes)) -> ~ in_img B (a + i)) /\
    receive_m timg_plain Bw a bytes by_poll pf = Some (Bw', tt) /\
    h_post receive_FRAME
      (fun x => h_world x \/ a <= x < a + Z.max 1 (Z.of_nat (length bytes)) \/ ms_ctx B <= x < ms_ctx B + CTX_SIZE)
      L A regs mem md b Bw' c'.

Definition receive_contract : Prop :=
  h_binds ->
  forall L A regs mem md b (Bw : list byte) (p : Z) (bytes : list byte) (by_poll pf : Z),
    h_pre receive_FRAME L A regs mem md b Bw ->
    frm_zero fp_csr ->
    receive_args L A regs mem Bw p bytes by_poll pf ->
    room_slots b (Z.max 1 (Z.of_nat (length bytes))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 receive_ENTRY) mem (seg_rom segs)) md)
      (receive_ret L A regs mem md b Bw bytes by_poll pf).

End K.
