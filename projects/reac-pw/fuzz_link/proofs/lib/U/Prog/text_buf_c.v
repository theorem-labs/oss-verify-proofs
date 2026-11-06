(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 29 of its 45 lines of code are new or changed and 51 lines of the source are left out. *)
(* text_buf (fuzz_link.c:655-666), UBSAN build: a buffer of `cap` bytes a reader may write, with a
   guard byte after it.

   The twin of lib/Prog/text_buf_c.v, with its premises, its statement shape and its Post
   unchanged: nothing below is added. a0 = cap. A zero cap answers NULL and allocates nothing.
   Otherwise it allocates cap+1 bytes and fills every one of them with 0x5a (memset, reached by a
   tail call at +0x34): the cap bytes the reader may write and the guard byte that check_bounds
   reads afterwards (fuzz_link.c:565). The abort at +0x48 (0x153b4, reached from the `beqz a0` at
   0x15388) is the harness`s own allocation failure, which is not a property of the program; the
   premise `room_slots b (cap+1)` rules it out.
   K = 16 + ALLOC_STACK = 8208: its own frame of 16 (link/donors/premises-ubsan.txt) and the
   allocator`s ALLOC_STACK = 8192 (lib/Reusable/YO0d.v, re-exported by lib/U/Reusable/YO0d.v);
   memset uses no stack (lib/U/Prog/memset_c.v keeps sp and takes no stack premise). The ubsan
   body calls exactly what the plain body calls (malloc, memset, abort): no call edge of the ubsan
   build only.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/text_buf.s): NONE. The body has no
   guard branch. Its one `unimp`, at 0x153b8 (+0x4c), follows the call to abort and is reached only
   through it (ubsan-checks.tsv, text_buf, the `fallthrough` row of fuzz_link.c:662).
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). This
   contract has the SR shape of the released allocator-facing contracts: the function reaches
   malloc, so it is stated over the frame`s allocator interface (lib/U/Contract.v) and not with the
   `leaf` shape of lib/U/Prog/link_mem.v.
   THE START STATE IS THE FP-AWARE ONE (a Theorem Labs lane, AMEND-slot item 6): `mkst` is written
   `@YK11.mkst fx` here, because this file imports lib/Prog/link_mem.v last and the bare name
   would otherwise resolve to lib/Lib/PropExec.v`s, whose FP file is empty and whose fcsr is 0.
   At every call site the FP file is whatever the printf layer left and the fcsr has only its
   rounding mode at 0, so the contract would not apply.
   
   AMEND-slot item 11 (a Theorem Labs lane, 2026-10-30): the allocating arm keeps every old user block,
   `forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')`, as Contract.malloc_ret
   gives it. call_post_k protects an old block's bytes only when the block is in both A and A', so
   without this the caller loses the model, marks, payload and FILE blocks across the call. True:
   the function allocates once and changes no other allocator state. The same arm also gives
   `st_init_done A' = true`, which malloc_ret states and call_post_k does not carry, and which
   every later call_pre_k and the slot's own post ask for.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract OutForm Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_spec link_mem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TEXT_BUF : Z := 0x1536c.
Lemma TEXT_BUF_is_entry : TEXT_BUF = P_text_buf. Proof. reflexivity. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition TEXT_BUF_K : Z := 16 + ALLOC_STACK.

Definition text_buf_contract : Prop :=
  forall L A regs mem md (b : sbound) (cap : Z),
    segs = rsegs ->
    call_pre_k B MR TEXT_BUF_K L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 cap -> 0 <= cap < 40 ->
    res_ok_slots A b -> room_slots b (cap + 1) ->
    SR segs (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 TEXT_BUF) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (@YK11.mkst fx regs' (getr regs 1) mem' (seg_rom segs)) md'
         /\ call_post_k B MR TEXT_BUF_K L A regs mem md
              (fun a => bv_unsigned (getr regs' 10) <= a < bv_unsigned (getr regs' 10) + cap + 1)
              L' A' regs' mem' md'
         /\ ro_agree segs mem'
         /\ (cap = 0 -> getr regs' 10 = Z_to_bv 64 0
               /\ L' = L /\ A' = A /\ md' = md /\ res_ok_slots A' b)
         /\ (cap <> 0 ->
               getr regs' 10 <> Z_to_bv 64 0
               /\ fresh_block B (bv_unsigned (getr regs' 10)) (cap + 1)
               /\ (exists b1 b2, blocks L' A' = b1 ++ (bv_unsigned (getr regs' 10), cap + 1) :: b2
                     /\ blocks L A = b1 ++ b2)
               /\ res_ok_slots A' (sb_malloc b (cap + 1))
               /\ (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true
               /\ tbuf_at mem' (bv_unsigned (getr regs' 10)) cap
                    (repeat (zb GUARD_BYTE) (Z.to_nat cap)))).

End K.
