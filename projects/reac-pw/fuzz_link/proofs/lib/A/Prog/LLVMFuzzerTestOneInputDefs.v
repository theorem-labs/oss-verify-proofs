(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 357 of its 392 lines of code are new or changed and 1270 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/nl_talk_defs.v, with its module names, addresses and numbers changed; 526 of its 581 lines of code are new or changed and 337 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput (fuzz_link.c:764-790) on image A (fuzz_link.asan, the PUBLISHED pin, sha256
   059dae63e07c...; listing (internal path)
   (internal record, sha256 e84d6f0c6974), 0x827d4, 5468 bytes, 1367 instructions): the data the phases of its walk
   share. The statement the phases prove together is lib/A/Prog/LinkEntry.v `tfib_lib_contract_xf` at the instance of
   LinkEntryA.v; the top is lib/A/Prog/LLVMFuzzerTestOneInput.v. The form is pcap's A/Prog/PcapEntryDefs.v
   (origin/ossv/recipes) and nl_talk's lib/A/Prog/nl_talk_defs.v (the phase shape
   `*_from POST GI_next -> *_from POST GI_self`), with boxreg's FP-state threading (lib/A/Prog/BoxBase.v `fxr`,
   `apostF_continue`) because the call reaches the snprintf wrapper.

   THE SHAPE OF THE CODE (offsets from 0x827d4; every number here is read from the listing).
   - +0x000..+0x048  a 416-byte machine frame (`addi sp,sp,-0x1a0`; `sd zero,0(sp)` probes its lowest word), ra
     and s0..s11 saved at sp0-8 .. sp0-104, s0 := sp0, `andi sp,sp,-0x20` (the realigned stack pointer, lf_sp1)
     and s1 := it. Every call of the body is made with sp = s1; the spill slots lie at s1+0x18 .. s1+0x138.
   - +0x04c..+0x068  s2 := n, s5 := p, the side-stack switch cell (.got+0xb8) and the shadow base cell
     (.got+0x60, into s6). The switch is 1 in every state AR allows, so the real-stack arm +0x088..+0x0a0 is
     not entered.
   - +0x06c..+0x074  frame_alloc_4(0x380): the class-4 side frame F, in s4 and a6. With `aside_room Sc [(4,1)]`
     the frame address is at least 4096, so the second entry to the real-stack arm is not taken either.
   - +0x0a4..+0x2a4  the frame's header (magic, descriptor string, own pc) and its 112 shadow bytes (LF_SH0),
     and the early-return test `beqz a3` on n >> 26 (+0x2a8): under the Pre n < 2 ^ 26, so the arm +0x2ac is
     not taken.
   - +0x2b0..+0x304  the 11 constant spill slots that name the frame's objects, the cursor (p, n) at
     s1+0x118 / s1+0x120, and checked_memset(g_nl, 0, 271992).
   - +0x30c..+0x3c8  the 64-turn loop that writes g_names[k] with snprintf(g_names + 8k, 8, "nl%d", k) and, for
     k mod 16 <> 15, appends (g_names + 8k, k + 2) to g_nl's interface table.
   - +0x3cc..+0x490  the 4-turn loop that appends odd[1..4] with the indices 101..104.
   - +0x494..+0x594  calloc(1, 8856) (the model m) and calloc(1, 516) (the marks mk), their two NULL arms
     (+0x1440 before_abort, refuted by the allocator's room premises), and the 26 constant spill slots.
   - +0x598..+0x604  THE LOOP HEAD of operation i: n = 0 leaves to the exit; else one input byte b is read, the
     cursor advances, and b mod 6 picks the arm through the jump table at 0x20f64 (5 entries) or, for b mod 6 = 5,
     the default arm +0x958.
   - the six arms: +0x608 op_read, +0x8e4 op_write, +0x6a8 op_mark, +0x6e8 op_unmark, +0x648 op_decide,
     +0x958 op_refused (the plain order of lib/Prog/Slot/LDefs.v L_OP0..L_OP5). Each ends at +0x1110.
   - +0x1110..+0x1118  the loop tail: s9 := s9 + 1, back to the head while s9 <> 48.
   - +0x13b0..+0x13c0  the exit: free(mk), free(m).
   - +0x13c0..+0x143c  the retired magic at F, meta_fill_f5(shadow(F), 128) and the flag store that gives the
     class-4 frame back (the real-stack arm meta_fill_00(shadow(F), 112) is not reached), a0 := 0, the epilogue.

   THE PHASES. Each phase lemma has the shape `lf_from POST GI_next -> lf_from POST GI_self`; the entry phase
   proves `lf_start POST`. The three loops are proved by induction (64 - k, 4 - j, 48 - i).

   THE FLOATING-POINT STATE. The call reaches the snprintf wrapper (64 times in the g_names loop, once in the
   op_mark arm) and mark_quietly, whose contracts return at SOME fx' with `BoxBase.fxr fx fx'`. Every invariant
   below therefore carries the running FP state fy explicitly and the phases run at any fy with `fxr fx fy`;
   `fxr` is reflexive and transitive, so the composition is against the ENTRY fx (boxreg Prog/BoxLxDefs.v
   lx_fxr, Prog/BoxLxLoop.v).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The cuts of the walk, as listing offsets
   ========================================================================== *)

Local Notation AFL := AF_LLVMFuzzerTestOneInput.   (* 0x608; link_text + AFL = 0x827d4 *)

Definition LF_entry : Z := AFL.                (* 0x827d4 the first slot                               *)
Definition LF_sm_ra : Z := AFL + 0x74.         (* 0x82848 frame_alloc_4 (0x82844) returned             *)
Definition LF_frame : Z := AFL + 0xa4.         (* 0x82878 the frame is taken; both arms join here      *)
Definition LF_ms_ra : Z := AFL + 0x308.        (* 0x82adc checked_memset of g_nl (0x82ad8) returned    *)
Definition LF_gl : Z := AFL + 0x32c.           (* 0x82b00 the g_names loop head (back edge +0x3b4)     *)
Definition LF_sn_ra : Z := AFL + 0x344.        (* 0x82b18 snprintf (0x82b14) returned                  *)
Definition LF_odd : Z := AFL + 0x3cc.          (* 0x82ba0 the odd table's set-up                       *)
Definition LF_ol : Z := AFL + 0x408.           (* 0x82bdc the odd loop head (back edge +0x47c)         *)
Definition LF_ca : Z := AFL + 0x494.           (* 0x82c68 the arguments of the first calloc            *)
Definition LF_ca1_ra : Z := AFL + 0x4a4.       (* 0x82c78 calloc(1, 8856) (0x82c74) returned           *)
Definition LF_ca2_ra : Z := AFL + 0x4b4.       (* 0x82c88 calloc(1, 516) (0x82c84) returned            *)
Definition LF_blk : Z := AFL + 0x4c4.          (* 0x82c98 both blocks are non-NULL                     *)
Definition LF_lh : Z := AFL + 0x598.           (* 0x82d6c THE LOOP HEAD of operation i                 *)
Definition LF_op0 : Z := AFL + 0x608.          (* 0x82ddc op_read                                      *)
Definition LF_op1 : Z := AFL + 0x8e4.          (* 0x830b8 op_write                                     *)
Definition LF_op2 : Z := AFL + 0x6a8.          (* 0x82e7c op_mark                                      *)
Definition LF_op3 : Z := AFL + 0x6e8.          (* 0x82ebc op_unmark                                    *)
Definition LF_op4 : Z := AFL + 0x648.          (* 0x82e1c op_decide                                    *)
Definition LF_op5 : Z := AFL + 0x958.          (* 0x8312c op_refused (the default arm of `bltu`)       *)
Definition LF_tail : Z := AFL + 0x1110.        (* 0x838e4 the loop tail: s9 := s9 + 1                  *)
Definition LF_exit : Z := AFL + 0x13b0.        (* 0x83b84 free(mk), free(m)                            *)
Definition LF_leave : Z := AFL + 0x13c0.       (* 0x83b94 the frame is given back                      *)
Definition LF_ret : Z := AFL + 0x143c.         (* 0x83c10 the `ret`                                    *)
Definition LF_abort : Z := AFL + 0x1440.       (* 0x83c14 before_abort, then abort (not reached)       *)

(* The arm of an operation byte's residue (the plain order of lib/Prog/Slot/LDefs.v L_OP0 .. L_OP5:
   read, write, mark, unmark, decide, refused). The head phase proves that the jump table at 0x20f64 sends
   b mod 6 here. *)
Definition lf_op_pc (op : Z) : Z :=
  if op =? 0 then LF_op0 else if op =? 1 then LF_op1 else if op =? 2 then LF_op2
  else if op =? 3 then LF_op3 else if op =? 4 then LF_op4 else LF_op5.

(* The cuts, at the pin's addresses. *)
Lemma LF_addrs :
  map (fun o => link_text + o)
    [LF_entry; LF_sm_ra; LF_frame; LF_ms_ra; LF_gl; LF_sn_ra; LF_odd; LF_ol; LF_ca; LF_ca1_ra; LF_ca2_ra;
     LF_blk; LF_lh; LF_op0; LF_op1; LF_op2; LF_op3; LF_op4; LF_op5; LF_tail; LF_exit; LF_leave; LF_ret;
     LF_abort] =
    [0x827d4; 0x82848; 0x82878; 0x82adc; 0x82b00; 0x82b18; 0x82ba0; 0x82bdc; 0x82c68; 0x82c78; 0x82c88;
     0x82c98; 0x82d6c; 0x82ddc; 0x830b8; 0x82e7c; 0x82ebc; 0x82e1c; 0x8312c; 0x838e4; 0x83b84; 0x83b94;
     0x83c10; 0x83c14] /\ LF_entry = AF_LLVMFuzzerTestOneInput.
Proof. split; reflexivity. Qed.

(* ==========================================================================
   2. The call sites, as listing offsets of their return addresses
   ========================================================================== *)

Definition LF_CALLOC_SITES : list Z := [LF_ca1_ra; LF_ca2_ra].
Definition LF_FREE_SITES : list Z :=
  [AFL + 0x69c; AFL + 0x6a4; AFL + 0xf84; AFL + 0xf8c; AFL + 0x1108; AFL + 0x13b8; AFL + 0x13c0].
Definition LF_TEXT_OF_SITES : list Z := [AFL + 0x654; AFL + 0x664; AFL + 0x1008].
Definition LF_TEXT_BUF_SITES : list Z := [AFL + 0xe24; AFL + 0xe30].
Definition LF_MARK_SITES : list Z := [AFL + 0xa28; AFL + 0xcac].
Definition LF_SNPRINTF_SITES : list Z := [LF_sn_ra; AFL + 0x11f4].
(* every site at which a callee of this call reaches the allocator *)
Definition LF_ALLOC_SITES : list Z :=
  LF_CALLOC_SITES ++ LF_FREE_SITES ++ LF_TEXT_OF_SITES ++ LF_TEXT_BUF_SITES ++ LF_MARK_SITES.

(* The calls the listing holds, each at the slot before its return cut. *)
Lemma LF_calls_listed :
  map (fun o => nth_error link_listing (Z.to_nat ((o - 4) / 4)))
    ([LF_sm_ra; LF_ms_ra; LF_sn_ra] ++ LF_CALLOC_SITES ++ LF_FREE_SITES ++ LF_TEXT_OF_SITES
     ++ LF_TEXT_BUF_SITES ++ LF_MARK_SITES) =
  [Some (PCall LS___asan_stack_malloc_4 (1%bv : bv 5));
   Some (PCall LS___asan_memset (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_snprintf (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_calloc (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_calloc (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall LS_text_of (1%bv : bv 5));
   Some (PCall LS_text_of (1%bv : bv 5));
   Some (PCall LS_text_of (1%bv : bv 5));
   Some (PCall LS_text_buf (1%bv : bv 5));
   Some (PCall LS_text_buf (1%bv : bv 5));
   Some (PCall LS_mark_quietly (1%bv : bv 5));
   Some (PCall LS_mark_quietly (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3. The geometry of the two frames
   ========================================================================== *)

Definition LF_MFRAME : Z := 416.          (* addi sp,sp,-0x1a0          +0x000 *)
(* the realigned stack pointer the body runs on (`andi sp,sp,-0x20` +0x040) *)
Definition lf_sp1_of (sp0 : Z) : Z := 32 * ((sp0 - LF_MFRAME) / 32).

Lemma lf_sp1_range : forall sp0, 0 <= sp0 - LF_MFRAME -> sp0 mod 16 = 0 ->
  sp0 - LF_MFRAME - 16 <= lf_sp1_of sp0 <= sp0 - LF_MFRAME /\
  lf_sp1_of sp0 mod 32 = 0 /\ lf_sp1_of sp0 mod 16 = 0.
Proof.
  intros sp0 H0 H16. unfold lf_sp1_of.
  assert (Hm : (sp0 - LF_MFRAME) mod 16 = 0)
    by (rewrite <- Zminus_mod_idemp_l, H16; reflexivity).
  set (x := sp0 - LF_MFRAME) in *.
  pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
  pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
  assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
  split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

(* the class-4 side frame: 0x380 bytes asked, a 1024-byte slot, 112 shadow bytes written by the prologue and
   128 by meta_fill_f5 at the end *)
Definition LF_CID : Z := 4.
Definition LF_FREQ : Z := 896.            (* addi a0,zero,0x380         +0x06c *)
Definition LF_NSH : nat := 112%nat.       (* LF_FREQ / 8                       *)
Definition LF_NSH_RET : Z := 128.         (* addi a1,zero,0x80          +0x3d8 *)
Definition LF_NSH_MACH : Z := 112.        (* addi a1,zero,0x70          +0x3f0 *)
Definition LF_FLAGOFF : Z := 0x3f8.       (* ld a0,0x3f8(s4)            +0x3e4 *)
Definition LF_MAGIC : Z := 0x41b58ab3.    (* lui a2,0x41b59; addiw a2,a2,-0x54d  +0x0ac, +0x0c4 *)
Definition LF_RETIRED : Z := 0x45e0360e.  (* lui a0,0x45e03; addiw a0,a0,0x60e   +0x3c8, +0x3cc *)

(* the frame's objects, by offset from F (the addresses the spill slots hold) *)
Definition LO_WA : Z := 0x20.             (* addi a0,a6,0x20   -> s1+0x78 *)
Definition LO_B160 : Z := 0x160.          (* addi a0,a6,0x160  -> s1+0x68 *)
Definition LO_B1A0 : Z := 0x1a0.          (* addi a0,a6,0x1a0  -> s1+0x48 *)
Definition LO_B2E0 : Z := 0x2e0.          (* addi a0,a6,0x2e0  -> s1+0x88 *)
Definition LO_B330 : Z := 0x330.          (* addi a0,a6,0x330  -> s1+0x80 *)

(* The 112 shadow bytes of the frame as the prologue leaves them (+0x0e4 .. +0x2a4, the values
   a3 = 0xf1 (left redzone), a0 = 0xf8 (an object out of scope), a1 = 0xf2 (between objects),
   a2 = 0xf3 (right redzone)). Every arm that sets some of them to 0 sets them back to 0xf8 before the loop
   tail, so this list holds at every loop head. *)
Definition LF_SH0 : list Z :=
  repeat 241 4 ++ repeat 248 32 ++ repeat 242 8 ++ repeat 248 4 ++ repeat 242 4 ++ repeat 248 32
  ++ repeat 242 8 ++ repeat 248 5 ++ repeat 242 5 ++ repeat 248 5 ++ repeat 243 5.

Lemma LF_SH0_len : length LF_SH0 = LF_NSH.
Proof. reflexivity. Qed.
Lemma LF_frame_slot : fs_frame_bytes LF_CID = 1024 /\ LF_FREQ <= 1024 /\ Z.of_nat LF_NSH = LF_FREQ / 8.
Proof. split; [vm_compute; reflexivity|]. split; [unfold LF_FREQ; lia | vm_compute; reflexivity]. Qed.

(* ==========================================================================
   4. The spill slots, as offsets from the realigned stack pointer s1
   ========================================================================== *)

Definition LS_J18 : Z := 0x18.    (* (m + MD_N_REQ) mod 8 + 3           sd a1,0x18(s1)  +0x580 *)
Definition LS_J20 : Z := 0x20.    (* (m + MD_NEXT) mod 8 + 3            sd a4,0x20(s1)  +0x568 *)
Definition LS_J28 : Z := 0x28.    (* (m + MD_SEND_ERRNO) mod 8 + 3      sd a2,0x28(s1)  +0x558 *)
Definition LS_J30 : Z := 0x30.    (* m mod 8 + 3                        sd a4,0x30(s1)  +0x510 *)
Definition LS_F : Z := 0x38.      (* F                                  sd a6,0x38(s1)  +0x2d8 *)
Definition LS_FK : Z := 0x40.     (* frame_alloc_4's result (0 on the real-stack arm)
                                                                        sd s4,0x40(s1)  +0x2b4 *)
Definition LS_B1A0 : Z := 0x48.   (* F + 0x1a0                          sd a0,0x48(s1)  +0x2c8 *)
Definition LS_ODD : Z := 0x50.    (* odd (0xa1760)                      sd a6,0x50(s1)  +0x3ec *)
Definition LS_MARK0 : Z := 0x58.  (* m + MD_MARK                        sd a0,0x58(s1)  +0x548 *)
Definition LS_STR1 : Z := 0x60.   (* .str.1 (0x20fc0)                   sd a5,0x60(s1)  +0x538 *)
Definition LS_B160 : Z := 0x68.   (* F + 0x160                          sd a0,0x68(s1)  +0x2c4 *)
Definition LS_NIF : Z := 0x70.    (* g_nl.n_if, re-read inside op_read (not a loop invariant)  *)
Definition LS_WA : Z := 0x78.     (* F + 0x20                           sd a0,0x78(s1)  +0x2bc *)
Definition LS_B330 : Z := 0x80.   (* F + 0x330                          sd a0,0x80(s1)  +0x2e0 *)
Definition LS_B2E0 : Z := 0x88.   (* F + 0x2e0                          sd a0,0x88(s1)  +0x2d4 *)
Definition LS_MK : Z := 0x90.     (* the marks block                    sd a0,0x90(s1)  +0x4c4 *)
Definition LS_NMARK : Z := 0x98.  (* m + MD_N_MARK                      sd s5,0x98(s1)  +0x594 *)
Definition LS_SH_NREQ : Z := 0xa0. (* shadow(m + MD_N_REQ)              sd a0,0xa0(s1)  +0x578 *)
Definition LS_SH_NEXT : Z := 0xa8. (* shadow(m + MD_NEXT)               sd a3,0xa8(s1)  +0x560 *)
Definition LS_SH_SE : Z := 0xb0.  (* shadow(m + MD_SEND_ERRNO)          sd a1,0xb0(s1)  +0x550 *)
Definition LS_JT : Z := 0xb8.     (* the jump table (0x20f64)           sd a5,0xb8(s1)  +0x540 *)
Definition LS_GNL42 : Z := 0xc0.  (* g_nl + 0x42000                     sd a5,0xc0(s1)  +0x530 *)
Definition LS_SH_M : Z := 0xc8.   (* shadow(m)                          sd a3,0xc8(s1)  +0x508 *)
Definition LS_NREQ : Z := 0xd0.   (* m + MD_N_REQ                       sd t2,0xd0(s1)  +0x584 *)
Definition LS_NEXT : Z := 0xd8.   (* m + MD_NEXT                        sd t1,0xd8(s1)  +0x524 *)
Definition LS_SE : Z := 0xe0.     (* m + MD_SEND_ERRNO                  sd t0,0xe0(s1)  +0x518 *)
Definition LS_M : Z := 0xe8.      (* m                                  sd s6,0xe8(s1)  +0x58c *)
Definition LS_GNL40 : Z := 0xf0.  (* g_nl + 0x40000                     sd s7,0xf0(s1)  +0x590 *)
Definition LS_SHB : Z := 0xf8.    (* the shadow base                    sd s6,0xf8(s1)  +0x2b0 *)
Definition LS_F0 : Z := 0x110.    (* F, first copy                      sd a6,0x110(s1) +0x0a4 *)
Definition LS_P : Z := 0x118.     (* the input cursor's pointer         sd s5,0x118(s1) +0x2e4 *)
Definition LS_N : Z := 0x120.     (* the input cursor's length          sd s2,0x120(s1) +0x2e8 *)
Definition LS_T128 : Z := 0x128.  (* text_of's out slot (op_decide)     addi a1,s1,0x128 +0x65c *)
Definition LS_T130 : Z := 0x130.  (* text_of's out slot (op_decide, op_write)                   *)

(* the image data the body names, from LinkAddr.v's object table (lv_obj): the jump table, the two literals *)
Definition LA_JT : Z := 0x20f64.
Definition LA_STR : Z := 0x20fa0.      (* "nl%d"                                 *)
Definition LA_STR1 : Z := 0x20fc0.
Definition LA_STR11 : Z := 0x21100.
Definition LA_STR21 : Z := 0x21240.
Definition LA_DESCR : Z := 0x1672f.    (* the frame's description string          *)

(* the fields of g_nl the body reads through the two bases s7 = g_nl + 0x40000 and s1+0xc0 = g_nl + 0x42000 *)
Lemma LF_gnl_fields :
  0x40000 + 0x20c = NK_SOCKET_ERRNO /\ 0x40000 + 0x210 = NK_SEND_ERRNO /\
  0x40000 + 0x218 = NK_OPENED /\ 0x42000 + 0x2a8 = NK_N_SENT /\ 0x42000 + 0x670 = NK_N_IF /\
  0x42000 + 0x2b0 = NK_IF_NAME /\ 0x42000 + 0x530 = NK_IF_INDEX.
Proof. unfold NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPENED, NK_N_SENT, NK_N_IF, NK_IF_NAME, NK_IF_INDEX.
  repeat split; reflexivity. Qed.

(* ==========================================================================
   5. The interface table the two set-up loops build
   (the pure data of lib/Prog/Slot/LDefs.v sections 3; restated here so that this file's closure holds no
   plain-image module. The A addresses are link_aaddr.v's.)
   ========================================================================== *)

Definition lf_dec2 (k : Z) : list Z := if k <? 10 then [48 + k] else [48 + k / 10; 48 + k mod 10].
Definition lf_gname_z (k : Z) : list Z := 110 :: 108 :: lf_dec2 k.
Definition lf_gname (k : Z) : list byte := map (fun z => Z_to_bv 8 z) (lf_gname_z k).

Definition LF_S_ENP : list byte := map (fun z => Z_to_bv 8 z) [101;110;112;49;51;49;115;48;46;51;51].
Definition LF_S_ETH0 : list byte := map (fun z => Z_to_bv 8 z) [101;116;104;48].
Definition LF_S_WLAN0 : list byte := map (fun z => Z_to_bv 8 z) [119;108;97;110;48].
Definition LF_S_VETH : list byte := map (fun z => Z_to_bv 8 z) [118;101;116;104;45;98;111;120].
Definition LF_S_GONE0 : list byte := map (fun z => Z_to_bv 8 z) [103;111;110;101;48].
Definition lf_odd_strs : list (list byte) := [[]; LF_S_ENP; LF_S_ETH0; LF_S_WLAN0; LF_S_VETH; LF_S_GONE0].

(* the 60 g_names entries with k mod 16 <> 15, then odd[1..4] with the indices 101..104 *)
Definition lf_gtab : list (list byte * Z) :=
  map (fun k => (lf_gname (Z.of_nat k), Z.of_nat k + 2))
      (filter (fun k => negb (Nat.eqb (Nat.modulo k 16) 15)) (seq 0 64)).
Definition lf_tab : list (list byte * Z) :=
  lf_gtab ++ [(LF_S_ENP, 101); (LF_S_ETH0, 102); (LF_S_WLAN0, 103); (LF_S_VETH, 104)].
(* the first j entries, as the g_names loop has them after j turns *)
Definition lf_tab_at (j : Z) : list (list byte * Z) := firstn (Z.to_nat j) lf_tab.

Lemma lf_tab_len : length lf_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma lf_tab_full : lf_tab_at 64 = lf_tab.
Proof. unfold lf_tab_at. change (Z.to_nat 64) with 64%nat. rewrite <- lf_tab_len. apply firstn_all. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
(* the contexts whose allocator traces the start-up universe lists (`In (raZ regs :: spine ch) CTX`, the CTX
   parameter of the allocating callees' contracts text_of / text_buf / mark_quietly and of the allocator
   rules amalloc04_rule / afree04_rule) *)
Variable LF_CTX : list (list Z).
(* The meter charges of the three parts of a call. They are Section VARIABLES, not numbers: each arm lane
   states `<the sum of its callees' MO> <= LF_MO_OP` as a Section hypothesis of its own file and names it in
   its report; the assembly discharges them at the meter the closing passes (ameter_triv, every charge 0). *)
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

(* ==========================================================================
   6. The call's context and its premises
   ========================================================================== *)

Record lcx := mkLCX {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model;
  c_p : Z;                    (* the driver's input buffer (a0)                 *)
  c_pl : list byte;           (* its bytes                                      *)
  c_T : list (Z * Z);         (* the blocks kept from the previous target calls *)
  c_E0 : env                  (* the atoms of the entry registers               *)
}.
Definition c_n (cx : lcx) : Z := Z.of_nat (length (c_pl cx)).
Definition lf_sp1 (cx : lcx) : Z := lf_sp1_of (spZ (c_regs cx)).
(* the side frame this call owns, its flag and its shadow *)
Definition lf_F (cx : lcx) (fp : Z) : Z := frame_addr (c_ly cx) LF_CID fp.
Definition lf_FL (cx : lcx) (fp : Z) : Z := flag_addr (c_ly cx) LF_CID fp.
Definition lf_SH (cx : lcx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (lf_F cx fp).
Definition lf_m0 (cx : lcx) : word -> option byte := rdW (c_W cx) (c_mem cx).
(* The frame chain this call hands to the functions it calls, in closed form (pcap's PcapEntryDefs.v `pch`,
   cgif lib/A/ACf5.v:128-131): the caller's frame record is on the chain when it fits under the layout's top,
   and its own next pointer is target_run's s0, an integer, so the chain ends there (ACejSites.v:48-55). At a
   callee's entry sp is this call's realigned stack pointer and s0 is this call's s0, so the callee's chain is
   `(lf_sp1 cx, <the call site's return address>, spZ (c_regs cx)) :: lf_chain cx` and its spine is
   `<the site's return address> :: spine (lf_chain cx)`, which is what ACej.v's CTX_<callee> lists hold. *)
Definition lf_chain (cx : lcx) : list (Z * Z * Z) :=
  if spZ (c_regs cx) + 16 <? ly_top (c_ly cx)
  then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].

(* What every phase may assume of the call: exactly the premises of LinkEntry.v's tfib_lib_pre_x at this
   image, plus the facts the frame's consumer supplies and the walk needs at every cut:
   the atoms of the entry registers, the journal's side condition gx_ok, the allocator-trace contexts of the
   allocating call sites, the meter budget, and rounding mode 0 at the entry FP state. *)
Definition lf_base (cx : lcx) : Prop :=
  @tfib_lib_pre_x rc SK SEGS PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB MS la_nul
    (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_pl cx) (c_T cx) /\
  YK0o.frm_zero (@fp_csr fx) /\
  gx_ok SEGS B G_HARNESS /\
  (* the instance's two records: the NUL that ends msg_build.long_alias, and the memory FILE's record. The
     phases need them placed (kernel writes long_alias, and every callee's akept keeps the FILE's stdio words
     only outside its own write set), and the contract is stated at exactly these two (LinkEntryA.v). *)
  la_nul = LA_NUL /\ MS = link_amf /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
  bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
  (* the allocator-trace contexts of the call's allocating sites, over the chain in closed form: the CTX of
     text_of / text_buf / mark_quietly's contracts, and (through `spine`) the chain the allocator rules
     unwind. The walk shows at each site that the real chain IS this one. *)
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) LF_ALLOC_SITES ->
     In (raZ regsT :: spine (lf_chain cx)) LF_CTX) /\
  0 <= LF_MO_SET /\ 0 <= LF_MO_OP /\ 0 <= LF_MO_END /\
  LF_MO_SET + 48 * LF_MO_OP + LF_MO_END <= XM_LIB (c_n cx) /\
  XM_LIB (c_n cx) <= XN_LIB (c_n cx) /\
  ameter_laws MT /\
  (* every `aleaf` callee returns at `S2 = set_fs (st_fs S2) Sc` (the side stack's hint may move), so the
     meter clause is re-stated at S2 through YC5d.v's mo_le_set_fs_r (finding G6 of the read arms' walk). The
     instance's trivial meter satisfies it. *)
  ameter_fs_laws MT.

(* The post of the whole call, in the shape tfib_lib_contract_xf asks: the machine is back at the driver's
   return address at SOME FP state with rounding mode 0, and tfib_lib_post_x holds with the lleaf
   `LL 0 (m_fs (c_md cx)) []` (the call returns 0 and writes nothing). *)
Definition lf_post (cx : lcx) : world SEGS -> config -> Prop :=
  fun W' c' => exists (fy : YK11.FPState) ly' S' regs' mem' md' k T',
    c' = mkCfg (@YK11.mkst fy regs' (w64 RA_LLVMF) mem' (YK11.seg_rom SEGS)) md' /\
    YK0o.frm_zero (@fp_csr fy) /\
    @tfib_lib_post_x rc SK SEGS LLVMF_STK G_HARNESS B MT XN_LIB MS la_nul
      (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_T cx)
      (LL 0 (m_fs (c_md cx)) []) ly' S' W' regs' mem' md' k T'.

(* ==========================================================================
   7. A phase
   ========================================================================== *)

(* `lf_from POST GI`: from any machine state GI describes, at any FP state fy the entry's calls can reach
   (`fxr fx fy`), with the class-4 frame taken at slot fp and the caller's journal extended by it, the run
   reaches POST. *)
Definition lf_from (POST : lcx -> world SEGS -> config -> Prop)
  (GI : lcx -> YK11.FPState -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop)
  : Prop :=
  forall (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  lf_base cx -> @BoxBase.fxr fx fy ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  GI cx fy fp k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under lf_base to the same post. The entry phase proves it. *)
Definition lf_start (POST : lcx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : lcx, lf_base cx ->
  SRr SEGS (c_W cx) (cfg_at SEGS (BASE + LF_entry) (c_regs cx) (c_mem cx) (c_md cx)) (POST cx).

(* ==========================================================================
   8. The state at a cut
   ========================================================================== *)

(* a machine word at an address, as the walk reads a spill slot or the frame's header back *)
Definition lf_at (W3 : world SEGS) (ms3 : machine_state) (a v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v.
Definition lf_slot (cx : lcx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  lf_at W3 ms3 (lf_sp1 cx + off) v.

(* the fixed fields of a machine state at a cut, at the running FP state fy *)
Definition lf_shape (fy : YK11.FPState) (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = @YK11.fp_regs fy /\ ms_fcsr ms3 = @YK11.fp_csr fy.

(* the registers every cut of the body keeps: the realigned stack pointer in sp and s1, the entry stack
   pointer in s0, gp and tp *)
Definition lf_core (cx : lcx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (lf_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (lf_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4.

(* the saved registers of the machine frame, which the epilogue reads back (+0x004..+0x038, +0x404..+0x434) *)
Definition lf_saved (cx : lcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  lf_at W3 ms3 (spZ (c_regs cx) - 8) (raZ (c_regs cx)) /\
  forall j, 0 <= j < 12 ->
    lf_at W3 ms3 (spZ (c_regs cx) - 16 - 8 * j)
      (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))).

(* the frame's header as the prologue writes it (+0x0d0..+0x0d8), and the flag pointer the slot's last word
   holds (frame_alloc_4's post; the epilogue loads it at +0x3e4 to give the frame back) *)
Definition lf_header (cx : lcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  lf_at W3 ms3 (lf_F cx fp) LF_MAGIC /\
  lf_at W3 ms3 (lf_F cx fp + 8) LA_DESCR /\
  lf_at W3 ms3 (lf_F cx fp + 16) (link_text + AFL) /\
  lf_at W3 ms3 (lf_F cx fp + fs_frame_bytes LF_CID - 8) (lf_FL cx fp).

(* the frame's shadow bytes *)
Definition lf_fshadow (cx : lcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (lf_SH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* ==========================================================================
   9. The journal's bookkeeping, the kept sets and the counters
   ========================================================================== *)

(* What the journal and the allocator look like at a cut after `ev` allocator events, `mo` of meter and `wl`
   wild traces: the frame addresses are the call's, the side stack holds only this call's frame, the
   descriptors and the file system are the call's, the memory FILE's invariant holds at the kept set T3, and
   the driver's input bytes are untouched. *)
(* The block list at a cut: the call's own live blocks `own` (the model and the marks block once the two
   callocs have run), then the blocks the kept set grew by (the memory FILE on the call that marks first),
   then the caller's. It is `amf_blocks_post (c_T cx) T3` refined with `own` (AMemFileSink.v: the kept blocks
   only grow and the live blocks at the return are the caller's plus that growth), which `lf_bl_amf` below
   reads off it when `own = []`. A caller's Pre needs it twice: a store into the model block is admitted by
   the journal only as `in_tmp_block` (the block is NOT one of the call's start state), and the exit's two
   frees need the list's shape (finding G4 of the read arms' walk). *)
Definition lf_bl (cx : lcx) (own T3 : list (Z * Z)) (ly3 : alayout) (S3 : astate) : Prop :=
  exists D, T3 = c_T cx ++ D /\
    Permutation (ablocks B ly3 S3) (own ++ D ++ ablocks B (c_ly cx) (c_S cx)).

Lemma lf_bl_amf : forall cx T3 ly3 S3,
  lf_bl cx [] T3 ly3 S3 ->
  amf_blocks_post (c_T cx) T3 (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3).
Proof. intros cx T3 ly3 S3 (D & HT & HP). exists D. split; [exact HT | exact HP]. Qed.

(* The live heap bytes this call has added at a cut: 0 before the two callocs, and from the loop head on the
   model block, the marks block and at most one memory FILE. With lf_base's `blocks_bytes (c_S cx) + LIVE_LIB
   <= LIVE_MAX` (LIVE_LIB = 8856 + 516 + 1304 + 2 * 320, LinkEntry.v) this is what gives an allocating callee
   its own room premise `blocks_bytes Sc + LIVE <= LIVE_MAX` at the CALL state: at an arm's text_of pair
   (LIVE = 320 each) the slack left is exactly 2 * 320 (the write arms' finding at 0x82e24). *)
Definition LF_LIVE_HELD : Z := MD_SIZE + MK_SIZE + AMF_BLOCK.
Lemma LF_LIVE_HELD_room : LF_LIVE_HELD + 2 * 320 = LIVE_LIB.
Proof. unfold LF_LIVE_HELD, MD_SIZE, MK_SIZE, AMF_BLOCK, LIVE_LIB. lia. Qed.

Definition lf_jbk (cx : lcx) (fp k2 ev mo : Z) (wl : nat) (lv : Z)
    (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    (T3 own : list (Z * Z)) : Prop :=
  k2 <= ev /\
  blocks_bytes S3 <= blocks_bytes (c_S cx) + lv /\
  (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) /\
  ~ In (LF_CID, fp) (frames (c_S cx)) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  mo_le MT (c_S cx) S3 mo /\
  (length (wild_part (as_universe B) (st_depot S3)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl)%nat /\
  amf_gi SEGS MS T3 (rdW W3 (ms_mem ms3)) /\ amf_env SEGS MS (rdW W3 (ms_mem ms3)) /\
  lf_bl cx own T3 ly3 S3 /\
  incl T3 (ablocks B ly3 S3) /\
  val_mem SEGS (rdW W3 (ms_mem ms3)) la_nul 1 0 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem ms3)) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (c_p cx) (c_pl cx) /\
  (forall a, 0 <= a < c_n cx ->
     aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)).

(* The counters at the loop head of operation i (0 <= i <= 48): at most 2 allocator events for the two
   callocs and 4 per operation (op_decide: two text_of and two free; op_read: two text_buf and two free), at most 2 wild
   traces per operation (one per text_of call, link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779);
   LINK_WILD_PER_CALL = 96 = 2 * 48), and the meter charge of the set-up plus i operations. *)
Definition LF_EV_SET : Z := 2.
Definition LF_EV_OP : Z := 4.
Definition LF_WILD_OP : nat := 2%nat.
Definition lf_ev (i : Z) : Z := LF_EV_SET + LF_EV_OP * i.
Definition lf_mo (i : Z) : Z := LF_MO_SET + LF_MO_OP * i.
Definition lf_wl (i : Z) : nat := (LF_WILD_OP * Z.to_nat i)%nat.

Lemma lf_ev_bound : lf_ev 48 + 2 = EV_LIB.
Proof. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB. lia. Qed.
Lemma lf_wl_bound : (lf_wl 48 <= LINK_WILD_PER_CALL)%nat.
Proof. unfold lf_wl, LF_WILD_OP, LINK_WILD_PER_CALL. cbn. lia. Qed.

(* ==========================================================================
   10. The model: what the call's own data looks like at a loop head
   ========================================================================== *)

(* g_names: each 8-byte slot holds its name "nl<k>", a NUL and bytes no one reads *)
Definition lf_gnames_at (j : Z) (m : word -> option byte) : Prop :=
  forall k, 0 <= k < j -> exists rest,
    abytes SEGS m (LA_G_NAMES + 8 * k) (lf_gname k ++ Z_to_bv 8 0 :: rest) /\
    length (lf_gname k ++ Z_to_bv 8 0 :: rest) = 8%nat.

(* the whole array is writable (snprintf's destination, and the interface table points into it) *)
Definition lf_gnames_w (m : word -> option byte) : Prop := abuf SEGS m LA_G_NAMES G_NAMES_SIZE.

(* the odd table (.data.rel.ro) and its six strings, which are read-only bytes: so a step that changes no
   read-only byte keeps them (the loop walk's finding K1: with q free, no exception set can be shown to miss
   the string's bytes) *)
Definition lf_odd_at (m : word -> option byte) : Prop :=
  forall i, (i < 6)%nat -> exists q,
    au64_at SEGS m (LA_ODD + 8 * Z.of_nat i) q /\ q <> 0 /\
    acstr_at SEGS m q (nth i lf_odd_strs []) /\
    (forall j, 0 <= j <= Z.of_nat (length (nth i lf_odd_strs [])) -> in_roP SEGS PCAP_RLO PCAP_RHI (q + j)).

(* the texts table kernel reads (.data.rel.ro): eleven non-NULL C strings *)
Definition lf_texts_at (m : word -> option byte) : Prop :=
  forall i, (i < 11)%nat -> exists q s,
    au64_at SEGS m (LA_TEXTS + 8 * Z.of_nat i) q /\ q <> 0 /\ acstr_at SEGS m q s /\
    (forall j, 0 <= j <= Z.of_nat (length s) -> in_roP SEGS PCAP_RLO PCAP_RHI (q + j)).

(* msg_build.long_alias: kernel fills its first 300 bytes and reads it with strlen, so the NUL at [300] and
   the three slack bytes after it are carried (the plain la_ok) *)
Definition lf_la_at (m : word -> option byte) : Prop :=
  (exists la, au8arr SEGS m LA_LONG_ALIAS la /\ Z.of_nat (length la) = 300) /\
  val_mem SEGS m (LA_LONG_ALIAS + 300) 1 0 /\
  (exists sl, au8arr SEGS m (LA_LONG_ALIAS + 301) sl /\ length sl = 3%nat).

(* Where the n name pointers of g_nl's interface table point (finding G5 of the read arms' walk: `aiftab_at` leaves
   the pointer of each entry free, and kernel's `kernel_apart`, model_read / model_write's `astrcmp_arg` and
   reac_served_unmark_all's / mark_quietly's `amk_table_ok` all have to place it). Entry e of the table is the
   e-th turn of the g_names loop with k mod 16 <> 15, i.e. k = e + e / 15 (+0x34c `beq a0,a1` skips the
   append), so the pointer is g_names + 8 k; entries 60..63 hold odd[1..4], whose values the odd loop copies
   out of the read-only window at LA_ODD + 8 + 8 j, so `arodata_okP` pins them. *)
Definition lf_ifp (m : word -> option byte) (n : Z) : Prop :=
  forall e, 0 <= e < n -> exists q,
    au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * e) q /\
    (e < 60 -> q = LA_G_NAMES + 8 * (e + e / 15)) /\
    (60 <= e -> au64_at SEGS m (LA_ODD + 8 * (e - 59)) q).

(* the input cursor: a suffix of the payload, in the two spill slots *)
Definition lf_cur (cx : lcx) (W3 : world SEGS) (ms3 : machine_state) (P N : Z) : Prop :=
  lf_slot cx W3 ms3 LS_P P /\ lf_slot cx W3 ms3 LS_N N /\
  exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q.

(* The data of one operation's state: g_nl, the model block and the marks block, with the link_spec relations
   the plain walk's loop head carries (lib/Prog/Slot/LDefs.v lh_mem), over the A views at image A's
   addresses. `md` is the calloc(1, 8856) block, `mk` the calloc(1, 516) block. *)
Definition lf_data (cx : lcx) (md mk : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  anlk_at SEGS m LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at SEGS m LA_G_NL kbs lf_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\
  amodel_at SEGS m md mbs /\ model_wf mbs /\
  amarks_at SEGS m mk gbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  lf_ifp m 64 /\
  lf_gnames_at 64 m /\ lf_gnames_w m /\ lf_odd_at m /\ lf_texts_at m /\ lf_la_at m.

(* The two blocks are blocks of the allocator's ledger, apart from each other and from the input, and their
   shadow lets the instrumented checks of the body pass. *)
Definition lf_blocks (cx : lcx) (md mk : Z) (T3 : list (Z * Z)) (ly3 : alayout) (S3 : astate)
    (m : word -> option byte) : Prop :=
  In (md, MD_SIZE) (ablocks B ly3 S3) /\ In (mk, MK_SIZE) (ablocks B ly3 S3) /\
  ~ In (md, MD_SIZE) (ablocks B (c_ly cx) (c_S cx)) /\
  ~ In (mk, MK_SIZE) (ablocks B (c_ly cx) (c_S cx)) /\
  ~ In (md, MD_SIZE) T3 /\ ~ In (mk, MK_SIZE) T3 /\
  md mod 16 = 0 /\ mk mod 16 = 0 /\
  (* off the image, which is ALL that AR's block law gives (YG0d.v AR_blocks_law: 4096 <= p and off_img p
     (req_size n); LinkPaLib.v blk_off_imgP): the model admits a block below IMG_LO as well as above IMG_TOP.
     Interface v10 asked IMG_TOP <= md / mk here, which no lemma can give (the loop walk's finding G-TOP at the
     two callocs). The two callee premises that asked for it (LinkSnpDef.v link_snp_place for snprintf's
     destination in the model block, remember_c.v amarks_ledger for the marks block) are routed to their owners
     to accept a block below the image too; a block below IMG_LO is as far from every image cell as one above
     IMG_TOP. *)
  off_img md MD_SIZE /\ off_img mk MK_SIZE /\
  apart md MD_SIZE mk MK_SIZE /\
  (0 < c_n cx -> apart md MD_SIZE (c_p cx) (c_n cx)) /\
  (0 < c_n cx -> apart mk MK_SIZE (c_p cx) (c_n cx)) /\
  range_addressable (ard SEGS m) SHADOW_OFF md MD_SIZE /\
  range_addressable (ard SEGS m) SHADOW_OFF mk MK_SIZE /\
  amem_range md MD_SIZE /\ amem_range mk MK_SIZE.
(* The eight bytes AFTER the marks block, which reac_served_mark's amarks_blk_ok asks at mark_quietly's two
   sites (0x831f8, 0x8347c), are NOT a conjunct here: no clause of akept, apost or AR carries a presence fact
   past `req_size n` across a callee (finding G7 of the read arms' walk, against the text of link_amem.v akept's
   clauses 5 and 6 and YG0d.v AR_blocks_law). They are instead DERIVED at each of those two instructions from
   the AR of the journal and `In (mk, MK_SIZE) (ablocks B ly3 S3)` above, by
   `srm_blk_tail_vis16` (lib/A/Prog/reac_served_markKitAt.v: the rest of the block's chunk is a range of AR's
   am_junk and the chunk's extent minus the left redzone is a multiple of 16, and round_up 516 16 = 528). *)

(* ==========================================================================
   11. The invariants at the cuts
   ========================================================================== *)

(* The registers the body keeps from the end of the set-up to the loop tail: the shadow base in s11, the
   frame's shadow in s3, the model and its two cursors in s6 / s5, g_nl's high base in s7, the constant -8
   in s8, the operation counter in s9 and the frame's first object in s10. *)
Definition lf_lregs (cx : lcx) (md fp i : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK) /\
  getr (ms_regs ms3) 22 = w64 md /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* the 26 constant spill slots of the loop *)
Definition lf_slots (cx : lcx) (md mk fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  lf_slot cx W3 ms3 LS_J18 ((md + MD_N_REQ) mod 8 + 3) /\
  lf_slot cx W3 ms3 LS_J20 ((md + MD_NEXT) mod 8 + 3) /\
  lf_slot cx W3 ms3 LS_J28 ((md + MD_SEND_ERRNO) mod 8 + 3) /\
  lf_slot cx W3 ms3 LS_J30 (md mod 8 + 3) /\
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_FK (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_B1A0 (lf_F cx fp + LO_B1A0) /\
  lf_slot cx W3 ms3 LS_ODD LA_ODD /\
  lf_slot cx W3 ms3 LS_MARK0 (md + MD_MARK) /\
  lf_slot cx W3 ms3 LS_STR1 LA_STR1 /\
  lf_slot cx W3 ms3 LS_B160 (lf_F cx fp + LO_B160) /\
  lf_slot cx W3 ms3 LS_WA (lf_F cx fp + LO_WA) /\
  lf_slot cx W3 ms3 LS_B330 (lf_F cx fp + LO_B330) /\
  lf_slot cx W3 ms3 LS_B2E0 (lf_F cx fp + LO_B2E0) /\
  lf_slot cx W3 ms3 LS_MK mk /\
  lf_slot cx W3 ms3 LS_NMARK (md + MD_N_MARK) /\
  lf_slot cx W3 ms3 LS_SH_NREQ (shadow_of_addr SHADOW_OFF (md + MD_N_REQ)) /\
  lf_slot cx W3 ms3 LS_SH_NEXT (shadow_of_addr SHADOW_OFF (md + MD_NEXT)) /\
  lf_slot cx W3 ms3 LS_SH_SE (shadow_of_addr SHADOW_OFF (md + MD_SEND_ERRNO)) /\
  lf_slot cx W3 ms3 LS_JT LA_JT /\
  lf_slot cx W3 ms3 LS_GNL42 (LA_G_NL + 0x42000) /\
  lf_slot cx W3 ms3 LS_SH_M (shadow_of_addr SHADOW_OFF md) /\
  lf_slot cx W3 ms3 LS_NREQ (md + MD_N_REQ) /\
  lf_slot cx W3 ms3 LS_NEXT (md + MD_NEXT) /\
  lf_slot cx W3 ms3 LS_SE (md + MD_SEND_ERRNO) /\
  lf_slot cx W3 ms3 LS_M md /\
  lf_slot cx W3 ms3 LS_GNL40 (LA_G_NL + 0x40000) /\
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF /\
  lf_slot cx W3 ms3 LS_F0 (lf_F cx fp).

(* --- the end of the prologue: LF_ms_ra (+0x308), the g_nl fill has returned ----------------------------- *)
(* Registers here: s2 = g_nl, s4 = 0x42000, s6 = m (not yet), s5 = g_names (not yet). The set-up phases keep
   only what they need, so this cut names the five slots the prologue wrote, the frame and the cursor. *)
Definition lf_setup_inv (pc : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  lf_shape fy pc ms3 /\ lf_core cx ms3 /\ lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\
  lf_fshadow cx fp W3 ms3 LF_SH0 /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF /\ lf_slot cx W3 ms3 LS_FK (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) /\ lf_slot cx W3 ms3 LS_F0 (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_WA (lf_F cx fp + LO_WA) /\
  lf_slot cx W3 ms3 LS_B160 (lf_F cx fp + LO_B160) /\
  lf_slot cx W3 ms3 LS_B1A0 (lf_F cx fp + LO_B1A0) /\
  lf_slot cx W3 ms3 LS_B2E0 (lf_F cx fp + LO_B2E0) /\
  lf_slot cx W3 ms3 LS_B330 (lf_F cx fp + LO_B330) /\
  lf_cur cx W3 ms3 (c_p cx) (c_n cx) /\
  lf_jbk cx fp k2 0 0 0%nat 0 ly3 S3 W3 ms3 md3 (c_T cx) [] /\
  lf_gnames_w (rdW W3 (ms_mem ms3)) /\ lf_odd_at (rdW W3 (ms_mem ms3)) /\
  lf_texts_at (rdW W3 (ms_mem ms3)) /\ lf_la_at (rdW W3 (ms_mem ms3)).

(* g_nl is zero over its whole object (what the checked fill leaves) *)
Definition lf_gnl_zero (m : word -> option byte) : Prop :=
  exists kbs, anlk_at SEGS m LA_G_NL kbs /\ forall q, 0 <= q < NK_SIZE -> val_mem SEGS m (LA_G_NL + q) 1 0.

(* --- the g_names loop head (+0x32c), turn j of 64 ------------------------------------------------------- *)
(* Registers: s5 = g_names + 8j, s6 = "nl%d", s7 = 64 - j, s8 = j + 2, s2 = g_nl,
   s10 = g_nl + 0x42000, s9 = 0x42530, s11 = 0x422b0. The table has as many entries as the turns with
   k mod 16 <> 15 so far. *)
Definition lf_gl_inv (j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists kbs : list byte,
  0 <= j < 64 /\
  lf_setup_inv LF_gl cx fy fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 18 = w64 LA_G_NL /\
  getr (ms_regs ms3) 21 = w64 (LA_G_NAMES + 8 * j) /\
  getr (ms_regs ms3) 22 = w64 LA_STR /\
  getr (ms_regs ms3) 23 = w64 (64 - j) /\
  getr (ms_regs ms3) 24 = w64 (j + 2) /\
  getr (ms_regs ms3) 25 = w64 0x42530 /\
  getr (ms_regs ms3) 26 = w64 (LA_G_NL + 0x42000) /\
  getr (ms_regs ms3) 27 = w64 0x422b0 /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs /\
  nk_n_if kbs = Z.of_nat (length (lf_tab_at (j - j / 16))) /\
  aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs (lf_tab_at (j - j / 16)) /\
  lf_ifp (rdW W3 (ms_mem ms3)) (j - j / 16) /\
  (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + q) 1 0) /\
  lf_gnames_at j (rdW W3 (ms_mem ms3)).

(* --- the odd loop head (+0x408), turn j of 4 ------------------------------------------------------------ *)
Definition lf_ol_inv (j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists kbs : list byte,
  0 <= j < 4 /\
  lf_setup_inv LF_ol cx fy fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 18 = w64 LA_G_NL /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF /\
  lf_slot cx W3 ms3 LS_ODD LA_ODD /\
  getr (ms_regs ms3) 11 = w64 (- 8 - 8 * j) /\
  getr (ms_regs ms3) 12 = w64 (101 + j) /\
  getr (ms_regs ms3) 13 = w64 (LA_G_NL + 0x42000) /\
  getr (ms_regs ms3) 14 = w64 (0x422b0) /\
  getr (ms_regs ms3) 15 = w64 (0x42530) /\
  getr (ms_regs ms3) 16 = w64 (LA_ODD + 8 + 8 * j) /\
  getr (ms_regs ms3) 17 = w64 (SHADOW_OFF + (LA_ODD + 8 + 8 * j) / 8) /\
  getr (ms_regs ms3) 5 = w64 (- 0x28) /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs /\
  nk_n_if kbs = Z.of_nat (length (lf_tab_at (60 + j))) /\
  aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs (lf_tab_at (60 + j)) /\
  lf_ifp (rdW W3 (ms_mem ms3)) (60 + j) /\
  (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + q) 1 0) /\
  lf_gnames_at 64 (rdW W3 (ms_mem ms3)).

(* --- the two callocs (+0x494) --------------------------------------------------------------------------- *)
(* The tables are built; neither block exists yet. The blocks phase proves the loop head of operation 0. *)
Definition lf_ca_inv (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists kbs : list byte,
  lf_setup_inv LF_ca cx fy fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 18 = w64 LA_G_NL /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF /\
  lf_slot cx W3 ms3 LS_ODD LA_ODD /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs /\ nlk_wf kbs /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\
  nk_n_if kbs = 64 /\ aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs lf_tab /\
  lf_ifp (rdW W3 (ms_mem ms3)) 64 /\
  nk_n_chunks kbs = 0 /\ nk_n_sent kbs = 0 /\ nk_next kbs = 0 /\
  (* no netlink socket has been opened yet: g_nl is zero outside the interface table after the checked fill,
     which lf_ol_inv's zero clause carries (NK_OPENED is outside the table fields); lf_lh_inv 0's
     `nk_opened kbs <= 64 * 0` needs it (the loop walk's finding G-OPENED) *)
  nk_opened kbs = 0 /\
  lf_gnames_at 64 (rdW W3 (ms_mem ms3)).

(* --- THE LOOP HEAD (+0x598), operation i ---------------------------------------------------------------- *)
Definition lf_lh_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  0 <= i <= 47 /\
  lf_shape fy LF_lh ms3 /\ lf_core cx ms3 /\ lf_lregs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk cx fp k2 (lf_ev i) (lf_mo i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i.

(* --- an arm's entry (lf_op_pc op), operation i ---------------------------------------------------------- *)
(* The loop head has read the operation byte b at the cursor and advanced it; op = b mod 6 picked this arm. *)
Definition lf_arm_inv (op : Z) (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout)
    (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (b : byte),
  0 <= i <= 47 /\ 0 <= op <= 5 /\
  lf_shape fy (lf_op_pc op) ms3 /\ lf_core cx ms3 /\ lf_lregs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\
  (* the byte just consumed, and the cursor after it *)
  1 <= N /\ abytes SEGS (rdW W3 (ms_mem ms3)) P [b] /\ bv_unsigned b mod 6 = op /\
  lf_cur cx W3 ms3 (P + 1) (N - 1) /\
  (exists q, 0 <= q < c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) /\
  lf_jbk cx fp k2 (lf_ev i) (lf_mo i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i.

(* --- the loop tail (+0x1110), after operation i --------------------------------------------------------- *)
Definition lf_tail_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  0 <= i <= 47 /\
  lf_shape fy LF_tail ms3 /\ lf_core cx ms3 /\ lf_lregs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk cx fp k2 (lf_ev (i + 1)) (lf_mo (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * (i + 1).

(* --- the exit (+0x13b0): free(mk), free(m) --------------------------------------------------------------- *)
(* Reached from the loop head when the input is used up (any i <= 48) and from the loop tail after operation
   47. s6 = m and the marks block is in its slot; nothing of the model is needed any more. *)
Definition lf_exit_inv (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk : Z) (T3 : list (Z * Z)),
  lf_shape fy LF_exit ms3 /\ lf_core cx ms3 /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\ getr (ms_regs ms3) 22 = w64 md /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slot cx W3 ms3 LS_MK mk /\ lf_slot cx W3 ms3 LS_F (lf_F cx fp) /\
  lf_slot cx W3 ms3 LS_FK (lf_F cx fp) /\
  lf_jbk cx fp k2 (lf_ev 48) (lf_mo 48) (lf_wl 48) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] /\
  In (md, MD_SIZE) (ablocks B ly3 S3) /\ In (mk, MK_SIZE) (ablocks B ly3 S3) /\
  ~ In (md, MD_SIZE) (ablocks B (c_ly cx) (c_S cx)) /\
  ~ In (mk, MK_SIZE) (ablocks B (c_ly cx) (c_S cx)) /\
  ~ In (md, MD_SIZE) T3 /\ ~ In (mk, MK_SIZE) T3 /\
  md <> mk /\
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF md MD_SIZE /\
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF mk MK_SIZE.

(* --- the frame's release (+0x13c0) ----------------------------------------------------------------------- *)
Definition lf_leave_inv (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists T3 : list (Z * Z),
  lf_shape fy LF_leave ms3 /\ lf_core cx ms3 /\
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) /\ lf_slot cx W3 ms3 LS_FK (lf_F cx fp) /\
  lf_jbk cx fp k2 EV_LIB (lf_mo 48 + LF_MO_END) (lf_wl 48) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3 [].

(* ==========================================================================
   12. Facts the phases share
   ========================================================================== *)

(* Two byte lists at one address with one length are one list: the Post quantifies over g_nl's bytes and the
   payload again, and this identifies them with the context's. *)
Lemma lf_abytes_unique : forall (m : word -> option byte) a bs bs',
  abytes SEGS m a bs -> abytes SEGS m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (H0 & H1 & H2) (H0' & H1' & H2') Hlen.
  apply lw_list_ext; [exact Hlen|]. intros k Hk.
  rewrite <- (H2 k Hk), <- (H2' k ltac:(lia)). reflexivity.
Qed.

(* the five arms of the jump table and the default arm are the six pcs above *)
Lemma lf_op_pc_cases : forall op, 0 <= op <= 5 ->
  lf_op_pc op = LF_op0 \/ lf_op_pc op = LF_op1 \/ lf_op_pc op = LF_op2 \/
  lf_op_pc op = LF_op3 \/ lf_op_pc op = LF_op4 \/ lf_op_pc op = LF_op5.
Proof.
  intros op H. unfold lf_op_pc.
  destruct (op =? 0); [left; reflexivity|].
  destruct (op =? 1); [right; left; reflexivity|].
  destruct (op =? 2); [right; right; left; reflexivity|].
  destruct (op =? 3); [right; right; right; left; reflexivity|].
  destruct (op =? 4); [right; right; right; right; left; reflexivity|].
  right; right; right; right; right; reflexivity.
Qed.

End b.
End a.

(* The sink head is an EXPLICIT argument of every statement above (Context (SK : YI16.sink_head), no braces):
   the only global sink_head instance of this closure is the plain build's (lib/Reusable/YI5b.v), so it must
   never be inferred. *)
