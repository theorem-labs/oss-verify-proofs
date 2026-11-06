(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 59 of its 75 lines of code are new or changed and 51 lines of the source are left out. *)
(* text_of (fuzz_link.c:126-136): a text from the table `texts`, or a heap copy of the input`s own
   bytes cut at their first NUL.

   a0 = in (the input cursor), a1 = own (where the copy to free is stored). The selector byte
   decides: without bit 7 it answers one of the eleven `texts` entries and stores NULL in *own;
   with bit 7 it takes up to (fuzz_u16 mod 320) bytes of the input, cuts them at their first NUL
   and answers a fresh heap C string, which it also stores in *own. The abort at +0x1a4 is the
   harness`s own allocation failure; `room_slots b 320` rules it out.
   THE WEAKEST FORM THE CALLER NEEDS: the caller (op_write and op_decide) uses the answer only as
   a C string and frees *own. So the contract says the answer is a C string of at most 319 bytes,
   that *own is either 0 or that same address, and, when it allocated, that the block is fresh and
   accounted. It does NOT say which of the two the selector chose; that needs the input cursor
   model, which no check reads.
   K = 8240 (48 of its own and the allocator`s 8192).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f). This contract
   has the SR shape of the released allocator-facing contracts (lib/Prog/pcap-family form): the
   function reaches malloc, so it is stated over the frame's allocator interface and not with the
   `leaf` shape of lib/Prog/link_mem.v.
   THE START STATE IS THE FP-AWARE ONE (a Theorem Labs lane, AMEND-slot item 6): `mkst` is written
   `@YK11.mkst fx` here, because this file imports lib/Prog/link_mem.v last and the bare name
   would otherwise resolve to lib/Lib/PropExec.v`s, whose FP file is empty and whose fcsr is 0.
   At every call site the FP file is whatever the printf layer left and the fcsr has only its
   rounding mode at 0, so the contract would not apply.
   
   THE CURSOR AND *own ARE NOT HEAP (LinkHelpers' walker HpTextOf, 2026-10-30): without
   `alloc_ceiling <= a0` and `alloc_ceiling <= a1` the Post is unprovable twice over. `sd a3, 0(a0)`
   at 0x15ad8 writes the advanced cursor on EVERY path with c1 <> 0, including the table arm where
   A' = A, so call_post_k's user-block conjunct is false if the cursor lies in a live block; and a
   cursor or *own in a free slot below alloc_ceiling is kept by no conjunct of malloc's own
   call_post_k, whose frame clause covers only `alloc_ceiling <= a` or `in_img`, so the Post's
   cursor cells need not survive `jal malloc` at 0x15bf4 and the fresh block may cover *own, which
   `sd s3, 0(s0)` at 0x15c1c then overwrites. Both callers pass slots of the slot's own frame
   (a0 = sp+0x40, a1 = sp+0x78 or sp+0x50, at 0x13a9c-0x13ab4 and 0x13fac-0x13fb4).
   *own IS NOT REQUIRED TO BE ZERO, same source: op_decide's `char *ok, *oa` are not initialised
   before the call, so the slot cannot supply it; the function stores 0 there itself before any
   read (`sd zero, 0(s0)`), so any word will do.
   
   AMEND-slot item 8 (a Theorem Labs lane's decide arm, 2026-10-30): the Post must say WHERE the answer
   lies, or a caller cannot show the two strings it then compares are readable and do not move.
   The table arm answers a `texts` entry, inside the read-only image; the copy arm answers the
   fresh block, and the string with its NUL fits inside it. `t` is therefore bound in the outer
   existential, so both arms can speak of it.
   
   THE ALLOCATOR IS ALREADY INITIALISED (LinkHelpers' walker HpTextOf, 2026-10-30): this function
   stores to the cursor (0x15ad8, 0x15adc, 0x15bcc, 0x15bd0) and to *own (0x15ae4) BEFORE its
   `jal malloc` at 0x15bf4, and both callers pass slots of their own frame, which lie above this
   function's sp. malloc's call_pre asks `st_init_done A = false -> auxv_pre ...`, and auxv_pre
   names words above sp (lib/Reusable/YO0d.v:70-77), so with the allocator not yet initialised
   those stores could change the auxv words and nothing would give malloc its premise. The slot
   calls calloc for the model and the marks block before any operation, malloc's Post gives
   `st_init_done A' = true`, and free keeps it. text_buf stores nothing above sp before its malloc
   and needs nothing. The released kb_pre_A (lib/KindBGlue.v:613) has the same side condition.
   
   AMEND-slot item 11 (a Theorem Labs lane, 2026-10-30): the allocating arm keeps every old user block,
   `forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')`, as Contract.malloc_ret
   gives it. call_post_k protects an old block's bytes only when the block is in both A and A', so
   without this the caller loses the model, marks, payload and FILE blocks across the call. True:
   the function allocates once and changes no other allocator state. The same arm also gives
   `st_init_done A' = true`, which malloc_ret states and call_post_k does not carry, and which
   every later call_pre_k and the slot's own post ask for.
   
   AMEND-slot item 12 (a Theorem Labs lane, 2026-10-30): the footprint is the block's real size `k`, not a
   flat 320. With `own + 320` the footprint could reach past the block, above alloc_ceiling or into
   image bytes for a block just below 0x10000, and the slot's step was unprovable. `k` is now bound
   in the outer existential so the footprint can name it; the table arm (own = 0) gives `k = 0`.
   
   AMEND-slot item 13 (a Theorem Labs lane, 2026-10-30): the table arm puts the string AND strlen's slack in
   the read-only segment, `s + |t| + 8 <= A_RO_END`. The first PT_LOAD ends at 0x11eb4 (ubsan
   0x11f54) and the next starts a page later, so a text ending in its last 3 bytes would leave the
   slack to the next 8-boundary in no segment. True with room: the last text ends at 0x10573
   (ubsan 0x10571), so s + |t| + 8 is at most 0x1057b. This is a Post fact, so the flat `+ 8`
   strengthens it for the caller; it is not the containment trap item 10 was, which was a Pre.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract OutForm Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TEXT_OF : Z := 0x15aa8.
Lemma TEXT_OF_is_entry : TEXT_OF = P_text_of. Proof. reflexivity. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition TEXT_OF_K : Z := 48 + ALLOC_STACK.

Definition text_of_contract : Prop :=
  forall L A regs mem md (b : sbound) (c0 c1 : word),
    segs = rsegs ->
    call_pre_k B MR TEXT_OF_K L A regs mem md -> ro_agree segs mem ->
    rw_cells rsegs mem (bv_unsigned (getr regs 10)) [C8 c0; C8 c1] ->
    (exists w, rw_cells rsegs mem (bv_unsigned (getr regs 11)) [C8 w]) ->
    bv_unsigned (getr regs 10) <> 0 -> bv_unsigned (getr regs 11) <> 0 ->
    @YM05.alloc_ceiling rc <= bv_unsigned (getr regs 10) ->
    @YM05.alloc_ceiling rc <= bv_unsigned (getr regs 11) ->
    res_ok_slots A b -> room_slots b 320 ->
    st_init_done A = true ->
    (* AMEND-slot item 1, and the facts the UBSan twin states that are not guard premises: the
       input is readable, inside a live user block, apart from the cursor and from *own; the
       cursor and *own are apart from each other, from the frame and from the texts table, whose
       eleven pointers are the image's *)
    (exists inp, bytes_at rsegs mem (bv_unsigned c0) inp
                 /\ Z.of_nat (length inp) = bv_unsigned c1
                 /\ (bv_unsigned c0 + bv_unsigned c1 <= bv_unsigned (getr regs 10)
                     \/ bv_unsigned (getr regs 10) + 16 <= bv_unsigned c0)
                 /\ (bv_unsigned c0 + bv_unsigned c1 <= bv_unsigned (getr regs 11)
                     \/ bv_unsigned (getr regs 11) + 8 <= bv_unsigned c0)) ->
    (bv_unsigned c1 <> 0 ->
       exists q k, In (q, k) (user_blocks A) /\ ptr_addr L q <= bv_unsigned c0
                   /\ bv_unsigned c0 + bv_unsigned c1 <= ptr_addr L q + k) ->
    (bv_unsigned (getr regs 11) + 8 <= bv_unsigned (getr regs 10)
       \/ bv_unsigned (getr regs 10) + 16 <= bv_unsigned (getr regs 11)) ->
    apart_frame regs TEXT_OF_K (bv_unsigned (getr regs 10)) 16 ->
    apart_frame regs TEXT_OF_K (bv_unsigned (getr regs 11)) 8 ->
    G_img_c B [(A_TEXTS, 8 * TEXTS_N)] mem ->
    (bv_unsigned (getr regs 10) + 16 <= A_TEXTS
       \/ A_TEXTS + 8 * TEXTS_N <= bv_unsigned (getr regs 10)) ->
    (bv_unsigned (getr regs 11) + 8 <= A_TEXTS
       \/ A_TEXTS + 8 * TEXTS_N <= bv_unsigned (getr regs 11)) ->
    SR segs (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 TEXT_OF) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (own s : Z) (t : list byte) (k : Z),
         c' = mkCfg (@YK11.mkst fx regs' (getr regs 1) mem' (seg_rom segs)) md'
         /\ call_post_k B MR TEXT_OF_K L A regs mem md
              (fun a => (own <= a < own + k)
                        \/ (bv_unsigned (getr regs 10) <= a < bv_unsigned (getr regs 10) + 16)
                        \/ (bv_unsigned (getr regs 11) <= a < bv_unsigned (getr regs 11) + 8))
              L' A' regs' mem' md'
         /\ ro_agree segs mem'
         /\ getr regs' 10 = Z_to_bv 64 s /\ s <> 0
         /\ cstr_at mem' s t /\ Z.of_nat (length t) < 320
         /\ bytes_at rsegs mem' (bv_unsigned (getr regs 11)) (le8 (Z_to_bv 64 own))
         /\ (exists adv, 0 <= adv <= bv_unsigned c1
               /\ rw_cells rsegs mem' (bv_unsigned (getr regs 10))
                    [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))])
         /\ (own = 0 -> k = 0 /\ L' = L /\ A' = A /\ res_ok_slots A' b
               /\ A_RO_LO <= s /\ s + Z.of_nat (length t) + 8 <= A_RO_END)
         /\ (own <> 0 ->
               own = s
               /\ 1 <= k <= 320 /\ fresh_block B own k
               /\ Z.of_nat (length t) + 1 <= k
               /\ (exists b1 b2, blocks L' A' = b1 ++ (own, k) :: b2 /\ blocks L A = b1 ++ b2)
               /\ res_ok_slots A' (sb_malloc b k)
               /\ (forall q n, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A'))
               /\ st_init_done A' = true)).

End K.
