(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 104 of its 121 lines of code are new or changed and 50 lines of the source are left out. *)
(* mark_quietly (fuzz_link.c:153-164): open the harness`s own stream once, rewind it, and run the
   marking policy.

   a0 = m, a1 = ifname. On the FIRST call of the process it opens the fmemopen FILE over g_said
   ("w", 4096 bytes), stores it in g_sink and points the policy at it with reac_served_say_to;
   every call then rewinds that FILE and answers reac_served_mark, which it TAIL-CALLS at 0x15dfc
   with sp already restored (0x15df8), so reac_served_mark runs on this function`s own sp.
   THE FILE is lib/Prog/memfile_c.v's `memfile_k m f k`, the predicate the whole output path and
   the three marking contracts share (link/ct/AMEND-mark.md gap 2). Every call rewinds, so the
   buffer starts empty and ends with at most one line, MARK_LINE_MAX bytes.
   GAP 3c of the same file: because of that tail call, this Pre must carry every conjunct
   reac_served_mark`s Pre asks for, at this function`s K (17280 >= 17248, so its window contains
   reac_served_mark`s): errno, the name, the marks block, the fake kernel and the FILE. They are
   stated with reac_served_mark_c.v`s own `mark_errno_ok`, `mark_name_ok` and `mark_block_ok`, so
   there is ONE form for both callers. The `sink = 0` arm adds what fmemopen asks
   (lib/Prog/fmemopen_c.v): stdio_ok, ofl_empty, guard_ok, g_said writable, room for the block.
   GAP 8 (a) and (b), which the slot (a Theorem Labs lane) needs: the Post gives the conjuncts of
   `call_post_k` over the footprint E below, with the user-block clause excepting the two blocks
   this call really writes (the marks block and the FILE block); g_nl unchanged when a0 = 0; and
   the open counter bounded by two exchanges.
   The abort at +0x4c is the harness`s own fmemopen failure; `room_slots b MF_BLOCK` rules it out.
   K = 17280 (32 of its own, then reac_served_mark`s 17248; the fmemopen arm needs only
   32 + 8192).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f). This contract
   has the SR shape of the released allocator-facing contracts (lib/Prog/pcap-family form): the
   function reaches malloc, so it is stated over the frame's allocator interface and not with the
   `leaf` shape of lib/Prog/link_mem.v.
   THE START STATE IS THE FP-AWARE ONE (a Theorem Labs lane, AMEND-slot item 6): `mkst` is written
   `@YK11.mkst fx` here, because this file imports lib/Prog/link_mem.v last and the bare name
   would otherwise resolve to lib/Lib/PropExec.v`s, whose FP file is empty and whose fcsr is 0.
   At every call site the FP file is whatever the printf layer left and the fcsr has only its
   rounding mode at 0, so the contract would not apply.
   
   GAPS 15, 16 AND 17 (a Theorem Labs lane's sub-lane a Theorem Labs lane). 15: the stack is below TASK_SIZE, which is
   what turns this SR memory into the `task_mem` the tail call at 0x15dfc needs of leaf_fp.
   16: the marks block and the FILE block are user blocks of the allocator state; rewind writes the
   FILE header at 0x15ddc and reac_served_mark writes both, so the frame's MR needs them owned, and
   through fmemopen's malloc the marks bytes survive only inside a user block. 17: the name and
   every table string must survive the prologue, rewind's g_said and errno writes, the g_sink store
   at 0x15dc8, say_to's g_say store and fmemopen's malloc; `kept_str` is what no call of this unit
   can move.
   
   AMEND-slot item 9 (a Theorem Labs lane, 2026-10-30): the Post fixes the open-file list head, next to
   g_sink and g_say; the slot's GI and its post's mf_sink both read it, and mq_writes lets this
   call change it. On the first call fmemopen's tail call to __ofl_add stores the new FILE there
   (the list was empty, `ofl_empty`); on every later call nothing writes it, so the Pre's sink <> 0
   arm carries `ofl_head = sink`, which the slot's `mf_heads mem f` already gives. `memfile_k` does
   not mention the list head, so without the Pre fact the later-call arm was unprovable.
   
   AMEND-slot item 10 (a Theorem Labs lane, 2026-10-30): the name's `kept_str` span is `name_span`, the
   string, its NUL and the slack to the next 8-boundary, not a flat `length s + 8`. The flat form
   is FALSE at the slot's call 0x13dac for g_names[63] = "nl63": 0x743f0 + 12 = 0x743fc passes
   g_names' end at 0x743f8, and the next bytes are long_alias. The `+ 8` spans in mark_name_ok are
   separation premises and stay: for that name they reach into long_alias, which is none of the
   regions they separate it from.
   
   AMEND-slot item 11 (a Theorem Labs lane, 2026-10-30): the allocating arm keeps every old user block,
   `forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')`, as Contract.malloc_ret
   gives it. call_post_k protects an old block's bytes only when the block is in both A and A', so
   without this the caller loses the model, marks, payload and FILE blocks across the call. True:
   the function allocates once and changes no other allocator state. The same arm also gives
   `st_init_done A' = true`, which malloc_ret states and call_post_k does not carry, and which
   every later call_pre_k and the slot's own post ask for.
   
   AMEND-slot item 14 (a Theorem Labs lane, 2026-10-30): the table-string `kept_str` clause takes
   `0 <= p < 2 ^ 64`. `u64_at` fixes p only mod 2^64, so p = 0x741f8 + 2^64 met the clause's
   premises while kept_str, a CONTAINMENT claim, is false of it: the clause was false at both call
   sites. The separation clauses over the same p (mark_table_ok and its kin) are true of an
   out-of-range p and need nothing. mark_quietly reads p with ld, so its proof needs only p < 2^64.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract OutForm Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Import ListNotations.
Local Open Scope Z_scope.

Definition MARK_QUIETLY : Z := 0x15d88.
Lemma MARK_QUIETLY_is_entry : MARK_QUIETLY = P_mark_quietly. Proof. reflexivity. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MARK_QUIETLY_K : Z := 17280.
Definition FILE_SIZE : Z := 1304.

(* What one call may change outside the allocator`s own blocks: the fake kernel up to its request
   ring, the three words of the harness`s stream, g_said, the open-file list head, the marks block
   and the FILE block. *)
Definition mq_writes (marks sink : Z) (a : Z) : Prop :=
  (A_G_NL <= a < A_G_NL + NK_N_SENT + 4)
  \/ (A_G_SINK <= a < A_G_SINK + 8) \/ (A_G_SAY <= a < A_G_SAY + 8)
  \/ (A_G_SAID <= a < A_G_SAID + SAID_SIZE)
  \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
  \/ (marks <> 0 /\ marks <= a < marks + MK_SIZE)
  \/ (sink <= a < sink + FILE_BLOCK).

(* `call_post_k` of lib/Reusable/YO0d.v:401-413, with its user-block clause excepting the two
   blocks this call writes: the marks block (remember) and the FILE block (the printf path). Every
   other conjunct is the frame`s own, word for word. *)
Definition mq_post_k (E except : Z -> Prop) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (L' : layout) (A' : astate)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') ->
     ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (@YM05.alloc_ceiling rc <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B MARK_QUIETLY_K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\
     (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     ~ except (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B MARK_QUIETLY_K regs a -> writable_at segs mem' a).

Definition mark_quietly_contract : Prop :=
  forall L A regs mem md (b : sbound) (tab : list (list byte * Z))
         (kbs : list byte) (nm : option (list byte)) (sink : Z),
    segs = rsegs ->
    call_pre_k B MR MARK_QUIETLY_K L A regs mem md -> ro_agree segs mem ->
    nlk_at mem kbs -> nlk_wf kbs -> nk_open kbs = 0 -> iftab_at mem kbs tab ->
    frame_apart_gnl regs MARK_QUIETLY_K ->
    nk_opened kbs + 2 < 2 ^ 31 -> nk_closed kbs + 2 < 2 ^ 31 ->
    policy_ro mem -> str_arg mem (bv_unsigned (getr regs 11)) nm ->
    u64_at mem A_G_SINK sink ->
    (* what reac_served_mark asks of its caller, at this K: ONE form for both (gaps 3c, 6, 7) *)
    mark_errno_ok mem regs MARK_QUIETLY_K sink ->
    mark_table_ok mem regs MARK_QUIETLY_K sink tab ->
    spZ regs <= TASK_SIZE ->
    (bv_unsigned (getr regs 10) <> 0 ->
       exists q n, In (q, n) (blocks L A) /\ q <= bv_unsigned (getr regs 10)
                   /\ bv_unsigned (getr regs 10) + MK_SIZE <= q + n) ->
    (sink <> 0 -> In (sink, FILE_SIZE) (blocks L A)) ->
    (forall s, nm = Some s -> kept_str (bv_unsigned (getr regs 11)) (name_span (bv_unsigned (getr regs 11)) s)) ->
    (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
       u64_at mem (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
       0 <= p < 2 ^ 64 -> kept_str p (Z.of_nat (length n2) + 1)) ->
    mark_name_ok mem regs MARK_QUIETLY_K sink nm ->
    mark_block_ok mem regs MARK_QUIETLY_K sink ->
    A_IMG_TOP <= spZ regs - MARK_QUIETLY_K ->
    guard_words mem ->
    (* the FILE, when one is already open (gap 2); rewind empties it, so any k will do *)
    (sink <> 0 ->
       (exists k, memfile_k mem sink k) /\ u64_at mem A_G_SAY sink
       /\ u64_at mem A_OFL_HEAD sink
       /\ sink + FILE_BLOCK <= spZ regs - MARK_QUIETLY_K) ->
    (* what fmemopen asks on the first call (lib/Prog/fmemopen_c.v) *)
    (sink = 0 ->
       stdio_ok mem /\ ofl_empty mem /\ guard_ok mem
       /\ wr_at rsegs mem A_G_SAID SAID_SIZE) ->
    YK0o.frm_zero (@YK11.fp_csr fx) ->
    res_ok_slots A b -> room_slots b FILE_SIZE ->
    SR segs (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 MARK_QUIETLY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' (sink' : Z),
         c' = mkCfg (@YK11.mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md'
         /\ YK0o.frm_zero (@YK11.fp_csr fx')
         (* gap 8 (a): the frame`s own post over the footprint above *)
         /\ mq_post_k (mq_writes (bv_unsigned (getr regs 10)) sink')
              (fun a => (bv_unsigned (getr regs 10) <> 0
                         /\ bv_unsigned (getr regs 10) <= a < bv_unsigned (getr regs 10) + MK_SIZE)
                        \/ sink' <= a < sink' + FILE_BLOCK)
              L A regs mem md L' A' regs' mem' md'
         /\ ro_agree segs mem'
         /\ u64_at mem' A_G_SINK sink' /\ u64_at mem' A_G_SAY sink'
         /\ u64_at mem' A_OFL_HEAD sink'
         /\ sink' <> 0
         /\ (exists k', k' <= MARK_LINE_MAX /\ memfile_k mem' sink' k')
         /\ (sink <> 0 -> sink' = sink /\ L' = L /\ A' = A /\ res_ok_slots A' b)
         /\ (sink = 0 ->
               fresh_block B sink' FILE_SIZE
               /\ (exists b1 b2, blocks L' A' = b1 ++ (sink', FILE_SIZE) :: b2
                     /\ blocks L A = b1 ++ b2)
               /\ res_ok_slots A' (sb_malloc b FILE_SIZE)
               /\ (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true)
         (* gap 8 (b): a refused mark asks the kernel nothing *)
         /\ (bv_unsigned (getr regs 10) = 0 ->
               getr regs' 10 = Z_to_bv 64 (- E_INVAL) /\ nlk_at mem' kbs)
         /\ (bv_unsigned (getr regs 10) <> 0 -> forall gbs,
               marks_at mem (bv_unsigned (getr regs 10)) gbs ->
               let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
               getr regs' 10 = Z_to_bv 64 (m_rc M)
               /\ (exists gbs', marks_at mem' (bv_unsigned (getr regs 10)) gbs'
                     /\ marks_wf gbs' /\ mk_names gbs' = m_marks M
                     /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
               /\ (exists kbs', nlk_at mem' kbs' /\ nlk_wf kbs'
                     /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
                     /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at mem' kbs' tab
                     /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
                     /\ nk_sent kbs' = m_reqs M
                     /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
                     /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
                     /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
                     /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2))).

End K.
