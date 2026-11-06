(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 578 of its 664 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_finish_seg.v, with its module paths and module names changed; 360 of its 432 lines of code are new or changed and 592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/RecKindB.v, with its module paths and module names changed; 50 of its 61 lines of code are new or changed and 421 lines of the source are left out. *)
(* check_copy, fuzz_wire.c:184-210, with untagged (:172-182) and fuzz.h's fuzz_dup inlined: fuzz_wire plain
   c8763dfc4e81 at 0x13378 (308 bytes). A 48-byte frame (ra / s0..s4); callees rp_copy_untag (32 bytes below its sp),
   malloc and free (ALLOC_STACK below their sp), memcpy twice, bcmp: CC_STACK = 48 + ALLOC_STACK bytes below sp.
   Form: libreac/fuzz_decode's check_round_trip_c.v (recipes 25e3d17bdb5): the allocator model B / API, call_pre_k at
   entry, the SR run to ret_pc ra. check_copy returns normally (its abort() at 0x134a8 is unreachable) from every state
   LLVMFuzzerTestOneInput calls it in (fuzz_wire.c:274-275): c = fuzz_dup(f, n) a heap block holding the n bytes f holds,
   f in another heap block, n <= W_RECV_MAX = 1600, the allocator initialised and with room for fuzz_dup's
   malloc(n ? n : 1) (FuzzDup.v's fuzz_dup_size).
   The post: check_copy writes into c (rp_copy_untag's memmove), so instead of call_post_k (every entry block kept) it
   states call_post_x: call_post_k's clauses with the block at c excepted from the kept blocks; c then holds
   cu_bytes n bs and check_copy returns copy_untag_result n bs (rp_copy_untag_c.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import rp_copy_untag_c FuzzDup.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_COPY : Z := 0x13378.
Definition CHECK_COPY_FRAME : Z := 48.
Definition CC_STACK : Z := CHECK_COPY_FRAME + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* call_post_k (YO0d.v) with every clause kept but the entry blocks whose address is `gone` released: their bytes may
   change (check_copy rewrites c in place) *)
Definition call_post_x (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (gone : Z -> Prop)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ gone (ptr_addr L p) -> 0 <= i < n ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B stk regs a -> writable_at segs mem' a).

Definition check_copy_contract : Prop :=
  forall L A regs mem md (c f n kc : Z) (bs : list byte) (b : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR CC_STACK L A regs mem md ->
    st_init_done A = true ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 f -> getr regs 12 = Z_to_bv 64 n ->
    n <= 1600 -> Z.of_nat (length bs) = n ->
    In (c, kc) (blocks L A) -> n <= kc ->
    (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) ->
    Mem.bytes_at segs mem c bs -> Mem.bytes_at segs mem f bs ->
    ro_agree segs mem ->
    frm_zero fp_csr ->
    res_ok_slots A b -> room_slots b (fuzz_dup_size n) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_COPY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_x CC_STACK L A regs mem md (fun a => a = c) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 (copy_untag_result n bs) /\
         Mem.bytes_at segs mem' c (cu_bytes n bs) /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun a => a = c) /\
         guard_kept B mem mem' /\
         ro_agree segs mem' /\
         res_ok_slots A' b /\
         st_init_done A' = true).

End K.
