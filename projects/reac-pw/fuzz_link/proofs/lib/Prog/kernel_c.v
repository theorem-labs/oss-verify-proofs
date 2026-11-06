(* kernel (fuzz_link.c:256-282): the fake kernel of one operation, as the input spells it.

   a0 = in, the input cursor. It takes the two failure flags and three errno bytes, empties the
   chunk queue and fills it with at most three chunks: either the input`s own bytes or messages
   msg_build makes.
   THE WEAKEST FORM THE CALLER NEEDS: plain_halts does not need to know WHICH reply bytes
   msg_build makes. Both readers walk the same chunk, whatever it holds, so the agreement does not
   depend on the grammar of the reply. The contract therefore says only what the OPERATION needs:
   the queue is replaced by at most three chunks of at most 4096 bytes each, the cursor is reset
   to 0, the three errnos come from nl_errno`s six-entry table, and NOTHING else of the fake
   kernel moves - not the socket bookkeeping, not the request ring, not the interface table. That
   last part is what keeps check_socket, check_requests and index_of true across an operation.
   A later lane that wants the reply`s shape can strengthen the Post without touching the
   premises. K = 4416 (4336 of its own, then nl_error`s 80).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
   A TEXTS ENTRY IS NOT NULL (a Theorem Labs lane, 2026-10-30): the texts clause gives each entry `p <> 0`.
   attr_text's Pre asks `arg regs 2 <> 0`, kernel passes texts[(a >> 3) mod 11] there (+0x590,
   +0x790), and the table is in the writable segment, so the image alone does not fix p. Every
   entry the harness has is the address of a .rodata string, so the caller can supply it.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition KERNEL : Z := 0x14190.
Lemma KERNEL_is_entry : KERNEL = P_kernel. Proof. reflexivity. Qed.

(* the n bytes at `a` are apart from all kernel writes: its frame of K = 4416, g_nl, long_alias
   with the 3 slack bytes strlen reads after it, and the cursor at a0 (the same helper as the UBSan
   twin, at the plain K) *)
Definition kernel_apart (regs : bvmap 5 word) (a n : Z) : Prop :=
  apart_frame regs 4416 a n /\ apart_gnl a n
  /\ (a + n <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= a)
  /\ (a + n <= arg regs 0 \/ arg regs 0 + 16 <= a).

(* AMEND-slot item 1: the wn input bytes at wp are readable (fuzz_u8 and fuzz_take read them, and
   nl_queue_raw hands them to memcpy) and apart from everything kernel writes; the Post says where
   the cursor is afterwards, a suffix of the same input. The texts table, the long alias and the
   interface names are the regions kernel and its attr_text calls read: attr_text calls strlen on a
   texts string and on long_alias, so each comes with the slack strlen reads (strlen_c.v).
   The UBSan twin states the same groups and adds its guard premises. *)
Definition kernel_contract : Prop :=
  leaf KERNEL 4416
    (fun regs m => exists kbs (wp wn : word),
       nlk_at m kbs /\ frame_apart_gnl regs 4416 /\ nlk_wf kbs
       /\ rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn]
       /\ apart_gnl (arg regs 0) 16 /\ apart_frame regs 4416 (arg regs 0) 16
       /\ (exists d, bytes_at rsegs m (bv_unsigned wp) d /\ Z.of_nat (length d) = bv_unsigned wn)
       /\ kernel_apart regs (bv_unsigned wp) (bv_unsigned wn)
       /\ kernel_apart regs A_TEXTS (8 * TEXTS_N)
       /\ (forall i, 0 <= i < TEXTS_N -> exists p s slack,
             u64_at m (A_TEXTS + 8 * i) p /\ p <> 0
             /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
             /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
             /\ Z.of_nat (length s) < NL_CHUNK_MAX
             /\ kernel_apart regs p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)))
       /\ (exists la sl,
             rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]
             /\ bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat)
       /\ apart_frame regs 4416 A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
       /\ (arg regs 0 + 16 <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= arg regs 0)
       /\ (forall tab i nm ix p, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             kernel_apart regs p (Z.of_nat (length nm) + 1)))
    (fun regs m => [(A_G_NL + NK_CHUNK, A_G_NL + NK_OPEN);
                    (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE);
                    (arg regs 0, arg regs 0 + 16)])
    (fun regs m regs' m' => forall kbs, nlk_at m kbs ->
       exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
       /\ nk_next kbs' = 0 /\ 0 <= nk_n_chunks kbs' <= 3
       /\ In (nk_end_errno kbs') nl_errno_tab
       /\ (nk_socket_errno kbs' = 0 \/ In (nk_socket_errno kbs') nl_errno_tab)
       /\ (nk_send_errno kbs' = 0 \/ In (nk_send_errno kbs') nl_errno_tab)
       /\ nk_open kbs' = nk_open kbs /\ nk_opened kbs' = nk_opened kbs
       /\ nk_closed kbs' = nk_closed kbs /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_n_sent kbs' = nk_n_sent kbs /\ nk_sent kbs' = nk_sent kbs
       /\ nk_n_if kbs' = nk_n_if kbs
       /\ (forall tab, iftab_at m kbs tab -> iftab_at m' kbs' tab)
       /\ (forall wp wn : word, rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn] ->
             exists adv, 0 <= adv <= bv_unsigned wn
             /\ rw_cells rsegs m' (arg regs 0)
                  [C8 (Z_to_bv 64 (bv_unsigned wp + adv)); C8 (Z_to_bv 64 (bv_unsigned wn - adv))])
       /\ (exists la, rw_cells rsegs m' A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)])).
