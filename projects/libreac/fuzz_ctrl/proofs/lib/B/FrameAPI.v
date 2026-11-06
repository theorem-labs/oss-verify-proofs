(* frame.asan W1 (FRAME.md (a working note, not in this delivery), owner a Theorem Labs lane): the statement the frame's ASan layer will prove for this
   image, and the slot contract at LLVMFuzzerTestOneInput for the asan-ubsan build. The slot contract is plain's
   lib_contract_g (here lib/B/PContract.v, the plain vocabulary over this build's engine lib/B/Reusable) with the
   ASan allocator (lib/B/Contract.v, layer.asan.alloc) and the runtime invariant (lib/B/AsanRTInv.v,
   struct.asan.runtime) in place of mallocng's. Statements only. Written by startcert/aframeapi.py. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK15 YP09 YO0f YO0d YO09 YL00 YL0g
  YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import PContract MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract AsanRTInv.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.

Definition ENTRY : Z := 0x81018.
(* The slot's stack window: the real stack below the slot's entry sp (8 MiB at start-up; the driver's frames above). *)
Definition SLOT_STACK : Z := 1048576.
(* The target's own .data/.bss objects (with the guard bytes the build adds after each). *)
Definition frame_G : list (Z * Z) := [].
(* The image's whole GNU_RELRO range [p_vaddr, p_vaddr + p_filesz) from its program header (.init_array ... .got;
   batch 2: the stack guard's GOT slot included). *)
Definition frame_RELRO : list (Z * Z) := [(0x9f168, 9344)].
(* The image's registered (instrumented) globals, each [beg, beg + size) from its descriptor in the asan_globals
   section: the start-up registers them, so their bytes are addressable (round 16, two Theorem Labs lanes). *)
Definition frame_AG : list (Z * Z) := [(0x21140, 6); (0x21160, 1); (0x21180, 12); (0x211e0, 2); (0x21200, 7); (0x21220, 5); (0x21240, 7); (0x21260, 15); (0x21280, 10); (0x212a0, 16); (0x212c0, 6); (0x212e0, 8); (0x21300, 7); (0x21320, 15); (0x21340, 16); (0x21360, 10); (0x21380, 16); (0x213a0, 6); (0x213c0, 13); (0x213e0, 6); (0x21400, 23); (0x21440, 6); (0x21460, 22); (0x214a0, 7); (0x214c0, 7); (0x214e0, 29); (0x21520, 12); (0x21540, 29); (0x21580, 6); (0x215a0, 23); (0x215e0, 8); (0x21600, 6); (0x21620, 24); (0x21660, 8); (0x21680, 7); (0x216a0, 24); (0x216e0, 9); (0x21700, 7); (0x21720, 24); (0x21760, 9); (0x21780, 7); (0x217a0, 23); (0x217e0, 8); (0x21800, 7); (0x21820, 23); (0x21860, 8); (0x21880, 7); (0x218a0, 24); (0x218e0, 8); (0x21900, 32); (0x21940, 32); (0x21980, 56); (0x21a20, 32); (0x21a60, 32); (0x9f580, 112); (0x9f620, 3256); (0xa0600, 264)].
(* The registered globals' redzones, each [beg + size, beg + size_with_redzone) from its descriptor, and the
   asan_globals section itself (the descriptors): the start-up poisons both; every other image byte is addressable
   (round 20, a Theorem Labs lane 20:51Z; the section: batch 2, a Theorem Labs lane 04:55Z). *)
Definition frame_RZ : list (Z * Z) := [(0x21146, 26); (0x21161, 31); (0x2118c, 20); (0x211e2, 30); (0x21207, 25); (0x21225, 27); (0x21247, 25); (0x2126f, 17); (0x2128a, 22); (0x212b0, 16); (0x212c6, 26); (0x212e8, 24); (0x21307, 25); (0x2132f, 17); (0x21350, 16); (0x2136a, 22); (0x21390, 16); (0x213a6, 26); (0x213cd, 19); (0x213e6, 26); (0x21417, 41); (0x21446, 26); (0x21476, 42); (0x214a7, 25); (0x214c7, 25); (0x214fd, 35); (0x2152c, 20); (0x2155d, 35); (0x21586, 26); (0x215b7, 41); (0x215e8, 24); (0x21606, 26); (0x21638, 40); (0x21668, 24); (0x21687, 25); (0x216b8, 40); (0x216e9, 23); (0x21707, 25); (0x21738, 40); (0x21769, 23); (0x21787, 25); (0x217b7, 41); (0x217e8, 24); (0x21807, 25); (0x21837, 41); (0x21868, 24); (0x21887, 25); (0x218b8, 40); (0x218e8, 24); (0x21920, 32); (0x21960, 32); (0x219b8, 40); (0x21a40, 32); (0x21a80, 32); (0x9f5f0, 48); (0xa02d8, 808); (0xa0708, 88); (0xa51a0, 3648)].

Section S.
Context {fx : YK11.FPState} {LS : lib_shape}.
(* B carries the image's segments and the driver's cells (sink, errno); its mallocng fields are not used here. *)
Variable B : malloc_syms.
(* RT: struct.asan.runtime at a call with the given entry sp (a Theorem Labs lane). *)
Variable RT : Z -> (word -> option byte) -> Model -> Prop.
Variable AA : AC.AsanAllocAPI AC.ASYMS RT.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let AH := AC.aa_AH AC.ASYMS RT AA.
Let owned := AC.aa_owned AC.ASYMS RT AA.
Let stklo := AC.aa_stklo AC.ASYMS RT AA.
Let stkhi := AC.aa_stkhi AC.ASYMS RT AA.

(* Start of a slot call: the allocator call premise with the slot's window, the input buffer (p, n) a live block of H
   whose bytes are addressable (or the empty buffer), the bytes pl at p, no sink open, a fresh fd, sorted file
   system. *)
Definition alib_pre (stk empty : Z) (H : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (ra p n : Z) (pl : list byte) : Prop :=
  AC.a_call_pre AC.ASYMS RT AH stklo stkhi stk H regs mem md /\
  getr regs 1 = Z_to_bv 64 ra /\ getr regs 10 = Z_to_bv 64 p /\ getr regs 11 = Z_to_bv 64 n /\
  ((n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) H /\ addressable mem p n)) /\
  n = Z.of_nat (length pl) /\ n <= AC.ANMAX /\ blk_data B mem p pl /\
  (* the registered globals' bytes are addressable (round 16) *)
  (forall a, in_globals frame_AG a -> addressable mem a 1) /\
  (* the live heap at a slot call is small: the driver's input buffer and its copy (each <= ANMAX = 2^30), the
     target's kept blocks (TB_bound: at most 2 of <= 2^29) and the blocks of the at most 3 earlier calls that the
     target dropped from its kept set but alib_post leaves live (each call at most 2 of <= 2^29): 2 x 2^30 + 3 x 2 x
     2^29 <= 5 x 2^30; so a slot keeps 7 x 2^30 of room under the allocation contracts' ALIVE_MAX = 12 x 2^30
     (Contract.v; round 18, two Theorem Labs lanes 20:28Z; batch 2, a Theorem Labs lane 05:02Z) *)
  AC.a_live_bytes H <= 5 * 2 ^ 30 /\
  (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at segs mem a) /\
  sink_none B mem md /\
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
  Fs.fs_sorted (m_fs md) = true /\
  (* every image byte outside frame_RZ (the registered globals' redzones and the asan_globals section) is
     addressable (round 20, a Theorem Labs lane 20:51Z: literals in .rodata passed to checked wrappers) *)
  (forall a, AC.a_in_img a -> ~ in_globals frame_RZ a -> addressable mem a 1).

(* End of a slot call: a0 = 0; registers kept; the model changes only in its maps, lazy-page ledgers, fd table (same
   lookups) and file system; every block of H that the target does not keep (not in T) still live with its bytes (the
   input buffer included); the image's bytes kept except the runtime's, G and errno; errno writable; the stack at or
   above sp kept, bytes and writability; the Shadow bytes of the image and of the stack at or above sp kept; stklo and
   stkhi kept; nothing printed; the target's kept blocks T' are live, and those that were live before were in T
   (round 16: the kept-block list of the plain lib_contract_p, a Theorem Labs lane 18:39Z). *)
Definition alib_post (G : list (Z * Z)) (stk : Z) (H : list (Z * Z)) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (l : lleaf) (T T' : list (Z * Z))
    (H' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  RT (AC.aspZ regs) mem' md' /\ AH H' mem' md' /\
  getr regs' 10 = Z_to_bv 64 0 /\ AC.a_regs_kept regs regs' /\
  (exists lz mt vm' fds' pins', md' = with_vm_backing lz mt (os_upd vm' fds' (ll_fs l) pins' md) /\
     forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  m_halted md' = None /\ stklo mem' md' = stklo mem md /\ stkhi mem' md' = stkhi mem md /\
  (forall q k, In (q, k) H -> ~ In (q, k) T -> In (q, k) H') /\
  (forall q k i, In (q, k) H -> ~ In (q, k) T -> 0 <= i < k -> mbyte segs mem' (q + i) = mbyte segs mem (q + i)) /\
  (* and their Shadow (batch 2 item 9, a Theorem Labs lane 05:19Z: the k >= 2 arms call the slot again on the driver's copy;
     the runtime writes a chunk's Shadow only when that chunk is allocated or freed) *)
  (forall q k i, In (q, k) H -> ~ In (q, k) T -> 0 <= i < k ->
     mbyte segs mem' (shadow_addr (q + i)) = mbyte segs mem (shadow_addr (q + i))) /\
  (forall a, AC.a_in_img a -> ~ owned H mem md a -> ~ owned H' mem' md' a -> ~ in_globals G a ->
     ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at segs mem' a) /\
  (forall a, AC.aspZ regs <= a < APPMEM_END ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, (AC.a_in_img a \/ AC.aspZ regs <= a < APPMEM_END) ->
     mbyte segs mem' (shadow_addr a) = mbyte segs mem (shadow_addr a)) /\
  (* the slot's window below sp is writable and addressable again when it returns (the instrumented epilogues clear
     the Shadow of their frames) *)
  (forall a, AC.aspZ regs - stk <= a < AC.aspZ regs -> writable_at segs mem' a /\ addressable mem' a 1) /\
  ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\ ro_agree segs mem' /\
  (forall t, In t T' -> In t H') /\ (forall t, In t T' -> In t H -> In t T) /\
  (* no leak: every block live at the return was live at the call or is kept (round 18: the frame bounds the live heap
     at the next slot call) *)
  (forall t, In t H' -> In t H \/ In t T').

(* The slot contract of call j (j < 4), with the target's global invariant GI over its kept blocks T. *)
Definition alib_contract (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall H regs mem md p n pl T (K : lleaf -> TSet),
    alib_pre stk empty H regs mem md ra p n pl ->
    GI j T mem ->
    (forall t, In t T -> In t H) ->
    (0 < n -> ~ In (p, n) T) ->
    G_img_c B R mem ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) H' regs' mem' md' T',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          alib_post G stk H regs mem md l T T' H' regs' mem' md' /\
          GI (S j) T' mem') ->
       realizes segs c' (K l)) ->
    realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

(* The target's invariant depends only on G and its kept blocks (the plain SlotKept.v G_local_t). *)
Definition G_local_t (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) : Prop :=
  forall j T m m', (forall a, in_globals G a \/ in_tb T a -> mbyte segs m' a = mbyte segs m a) ->
    GI j T m -> GI j T m'.
End S.

(* The bound on the kept blocks (the plain SlotKept.v TB_bound, same constants). *)
Definition TBMAX : nat := 2.
Definition TBBYTES : Z := 2 ^ 29.
Definition TB_bound (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) : Prop :=
  forall j T m, GI j T m -> (length T <= TBMAX)%nat /\ forall t k, In (t, k) T -> 0 < k <= TBBYTES.

(* What the frame's ASan layer proves for this image: given the target's slot contract for its first 4 calls, the
   statement holds. RT is struct.asan.runtime's Rocq predicate (lib/B/AsanRTInv.v, owner a Theorem Labs lane; its laws
   RT_any, RT_store, RT_meta_write are lemmas there). *)
Definition frame_asan_ubsan : Prop :=
  exists (B : malloc_syms) (AA : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_tp B = AC.as_tp AC.ASYMS /\ ms_errno_off B = -164 /\
    @sk_ofl_head SH = 0x5fcd48 /\ @sk_ofl_lock SK = 0x5fcd40 /\ @sk_threaded SK = 0x5fc8e0 + 1 /\
    empty = 0x5dbd20 /\ 0 < empty < 2 ^ 62 /\
    (* every sink env cell lies inside the image (batch 2 item 4, a Theorem Labs lane 04:55Z: the slots' runtime wrappers store
       through them) *)
    (forall a, @YI14.env_addr SH SK a -> 0 <= a < AC.GT) /\
    (forall a, in_globals frame_G a -> AC.a_in_img a) /\
    (forall a, in_globals frame_RELRO a -> AC.a_in_img a) /\
    (forall rc H mem md a, AC.aa_owned AC.ASYMS AsanRTInv.RT (AA rc) H mem md a ->
       ~ in_globals frame_G a /\ ~ in_globals frame_RELRO a) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_t B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat [] mem) ->
       TB_bound GI ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @alib_contract fx LS B AsanRTInv.RT (AA rc) SH SK G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.asan_ubsan_halts).
