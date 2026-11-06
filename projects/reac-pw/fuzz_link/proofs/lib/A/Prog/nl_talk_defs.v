(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 357 of its 392 lines of code are new or changed and 1270 lines of the source are left out. *)
(* nl_talk (reac_link_alias.c:37-93) on image A (fuzz_link.asan 0x88974, 1504 bytes, 376 instructions; listing
   (internal path) (internal record, sha256 628c2741aace)): the data the phases of its walk
   share. The contract itself is lib/A/Prog/nl_talk_c.v; the walk's phases are lib/A/Prog/nl_talk_*.v and its top is
   lib/A/Prog/nl_talk.v.

   THE SHAPE OF THE CODE (offsets from 0x88974; every number here is read from the listing).
   - +0x00..+0x38  a 192-byte machine frame (`addi sp, sp, -0xc0`; `sd zero, 0(sp)` probes its lowest word), ra and
     s0..s11 saved at sp0-8 .. sp0-104;
   - +0x3c..+0x44  s0 := sp0, `andi sp, sp, -0x20` (the realigned stack pointer, nt_sp1), s1 := it. Every call of
     the body is made with sp = s1, and the spill slots lie at s1 + 8 .. s1 + 80;
   - +0x5c..+0x78  the side-stack switch (.got+0xb8 -> the cell) and the shadow base (.got+0x60 -> the cell, into
     s5). The switch is 1 in every state AR allows, so the real-stack arm +0x90..+0xbc is not entered;
   - +0x7c..+0x98  frame_alloc_9(16672): the class-9 side frame F, in s4 and s2. With `aside_room Sc [(9, 1)]` the
     frame address is at least 4096, so the second entry to the real-stack arm is not taken either;
   - +0xc0..+0x19c the frame's header (magic, descriptor, pc) and its 2084 shadow bytes: 0xf1 x 4 (left redzone),
     meta_fill_f8(SH + 4, 2048) (the 16384-byte buffer marked unusable), 0xf3 x 32 (right redzone);
   - +0x1a0..+0x1b4 fuzz_socket(16, 0x80003, 0), and its failure arm;
   - +0x1bc..+0x1cc fuzz_send(fd, req, len, 0), and its failure arm;
   - +0x1d4..+0x204 meta_fill_00(SH + 4, 2048) (the buffer usable), fuzz_recv(fd, F + 32, 16384, 0), its failure arm;
   - +0x208..+0x270 the walk over the messages of the chunk recv answered, and +0x294..+0x2a8 the next recv;
   - +0x314..+0x4a0 the attribute walk of the first RTM_NEWLINK, with the nested IFLA_LINKINFO walk and the two
     copy_attr calls (+0x38c on the alias buffer, +0x3f4 on the kind buffer);
   - +0x2ac..+0x30c the three failure arms (___errno_location, the instrumented check of the 4-byte load of errno,
     rc := -errno; the send arm closes the socket first);
   - +0x4ac..+0x4d8 an NLMSG_ERROR: rc := -EIO when the message is too short, else the message's code;
   - +0x4dc..+0x56c fuzz_close, meta_fill_f8 (the buffer unusable again), the retired magic, frame_release_9 and
     the epilogue.

   THE PHASES. Each phase lemma has the shape `nt_from POST GI_next -> nt_from POST GI_self` (pcap's
   PcapSourceNextDefs.v `nx_from`): from any machine state its invariant GI describes, with the class-9 frame
   taken at slot fp, the run reaches POST. The entry phase proves `nt_start POST` from the phases it reaches. The
   two loops (the message walk, the attribute walk with its nested kind walk) are proved by induction on the bytes
   left, and the receive loop by induction on the chunks left.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c copy_attr_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_close_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The cuts of the walk, as listing offsets
   ========================================================================== *)

Definition NT_entry : Z := AF_nl_talk.              (* 0x88974 the first slot                            *)
Definition NT_mv : Z := AF_nl_talk + 0x44.          (* 0x889b8 `mv s1, sp`, after the realignment        *)
Definition NT_sm_ra : Z := AF_nl_talk + 0x88.       (* 0x889fc frame_alloc_9 (0x889f8) returned          *)
Definition NT_frame : Z := AF_nl_talk + 0xc0.       (* 0x88a34 the frame is taken; both arms join here   *)
Definition NT_shadow : Z := AF_nl_talk + 0xf0.      (* 0x88a64 s8 = the frame's shadow address           *)
Definition NT_mf1_ra : Z := AF_nl_talk + 0x118.     (* 0x88a8c meta_fill_f8 (0x88a88) returned           *)
Definition NT_sock : Z := AF_nl_talk + 0x1a0.      (* 0x88b14 the arguments of fuzz_socket              *)
Definition NT_so_ra : Z := AF_nl_talk + 0x1b4.      (* 0x88b28 fuzz_socket (0x88b24) returned            *)
Definition NT_se_ra : Z := AF_nl_talk + 0x1cc.      (* 0x88b40 fuzz_send (0x88b3c) returned              *)
Definition NT_mf0_ra : Z := AF_nl_talk + 0x1ec.     (* 0x88b60 meta_fill_00 (0x88b5c) returned           *)
Definition NT_rv_ra : Z := AF_nl_talk + 0x204.      (* 0x88b78 fuzz_recv (0x88b74) returned              *)
Definition NT_walk : Z := AF_nl_talk + 0x214.       (* 0x88b88 the message walk's entry test             *)
Definition NT_loop : Z := AF_nl_talk + 0x21c.       (* 0x88b90 the message loop head (back edge +0x26c)  *)
Definition NT_next : Z := AF_nl_talk + 0x294.       (* 0x88c08 the next receive                          *)
Definition NT_rv2_ra : Z := AF_nl_talk + 0x2a8.     (* 0x88c1c fuzz_recv (0x88c18) returned              *)
Definition NT_fail_rv : Z := AF_nl_talk + 0x2ac.    (* 0x88c20 the recv failure arm                      *)
Definition NT_fail_so : Z := AF_nl_talk + 0x2cc.    (* 0x88c40 the socket failure arm                    *)
Definition NT_fail_se : Z := AF_nl_talk + 0x2ec.    (* 0x88c60 the send failure arm                      *)
Definition NT_attr : Z := AF_nl_talk + 0x314.       (* 0x88c88 the first RTM_NEWLINK                     *)
Definition NT_aloop : Z := AF_nl_talk + 0x338.      (* 0x88cac the attribute loop head                   *)
Definition NT_ca_a_ra : Z := AF_nl_talk + 0x390.    (* 0x88d04 copy_attr on the alias buffer returned    *)
Definition NT_info : Z := AF_nl_talk + 0x3ac.       (* 0x88d20 the nested IFLA_LINKINFO loop head        *)
Definition NT_ca_k_ra : Z := AF_nl_talk + 0x3f8.    (* 0x88d6c copy_attr on the kind buffer returned     *)
Definition NT_istep : Z := AF_nl_talk + 0x400.      (* 0x88d74 the nested loop's step                    *)
Definition NT_astep : Z := AF_nl_talk + 0x454.      (* 0x88dc8 the attribute loop's step                 *)
Definition NT_err : Z := AF_nl_talk + 0x4ac.        (* 0x88e20 an NLMSG_ERROR                            *)
Definition NT_adone : Z := AF_nl_talk + 0x4bc.      (* 0x88e30 the attribute walk ended: rc := 0         *)
Definition NT_exit : Z := AF_nl_talk + 0x4dc.       (* 0x88e50 fuzz_close and the buffer unusable again  *)
Definition NT_cl_ra : Z := AF_nl_talk + 0x4e4.      (* 0x88e58 fuzz_close (0x88e54) returned             *)
Definition NT_mf2_ra : Z := AF_nl_talk + 0x4f4.     (* 0x88e68 meta_fill_f8 (0x88e64) returned           *)
Definition NT_tail : Z := AF_nl_talk + 0x4f8.       (* 0x88e6c the retired magic; the two arms join here *)
Definition NT_fr_ra : Z := AF_nl_talk + 0x518.      (* 0x88e8c frame_release_9 (0x88e88) returned        *)
Definition NT_epi : Z := AF_nl_talk + 0x52c.        (* 0x88ea0 a0 := rc, then the epilogue               *)
Definition NT_ret : Z := AF_nl_talk + 0x56c.        (* 0x88ee0 the `ret`                                 *)

(* The cuts, at the pin's addresses. *)
Lemma NT_addrs :
  map (fun o => link_text + o)
    [NT_entry; NT_mv; NT_sm_ra; NT_frame; NT_shadow; NT_mf1_ra; NT_sock; NT_so_ra; NT_se_ra; NT_mf0_ra; NT_rv_ra;
     NT_walk; NT_loop; NT_next; NT_rv2_ra; NT_fail_rv; NT_fail_so; NT_fail_se; NT_attr; NT_aloop; NT_ca_a_ra;
     NT_info; NT_ca_k_ra; NT_istep; NT_astep; NT_err; NT_adone; NT_exit; NT_cl_ra; NT_mf2_ra; NT_tail;
     NT_fr_ra; NT_epi; NT_ret] =
    [0x88974; 0x889b8; 0x889fc; 0x88a34; 0x88a64; 0x88a8c; 0x88b14; 0x88b28; 0x88b40; 0x88b60; 0x88b78;
     0x88b88; 0x88b90; 0x88c08; 0x88c1c; 0x88c20; 0x88c40; 0x88c60; 0x88c88; 0x88cac; 0x88d04;
     0x88d20; 0x88d6c; 0x88d74; 0x88dc8; 0x88e20; 0x88e30; 0x88e50; 0x88e58; 0x88e68; 0x88e6c;
     0x88e8c; 0x88ea0; 0x88ee0] /\ NT_entry = AF_nl_talk.
Proof. split; reflexivity. Qed.

(* The ten calls the listing holds, each at the slot before its return cut. *)
Lemma NT_calls_listed :
  map (fun o => nth_error link_listing (Z.to_nat ((o - 4) / 4)))
    [NT_sm_ra; NT_mf1_ra; NT_so_ra; NT_se_ra; NT_mf0_ra; NT_rv_ra; NT_rv2_ra; NT_ca_a_ra; NT_ca_k_ra;
     NT_cl_ra; NT_mf2_ra; NT_fr_ra] =
  [Some (PCall LS___asan_stack_malloc_9 (1%bv : bv 5));
   Some (PCall LS___asan_set_shadow_f8 (1%bv : bv 5));
   Some (PCall LS_fuzz_socket (1%bv : bv 5));
   Some (PCall LS_fuzz_send (1%bv : bv 5));
   Some (PCall LS___asan_set_shadow_00 (1%bv : bv 5));
   Some (PCall LS_fuzz_recv (1%bv : bv 5));
   Some (PCall LS_fuzz_recv (1%bv : bv 5));
   Some (PCall LS_copy_attr (1%bv : bv 5));
   Some (PCall LS_copy_attr (1%bv : bv 5));
   Some (PCall LS_fuzz_close (1%bv : bv 5));
   Some (PCall LS___asan_set_shadow_f8 (1%bv : bv 5));
   Some (PCall LS___asan_stack_free_9 (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2. The geometry of the frame
   ========================================================================== *)

(* The realigned stack pointer the body runs on (`andi sp, sp, -0x20` at +0x40). *)
Definition nt_sp1 (sp0 : Z) : Z := 32 * ((sp0 - NL_TALK_AFRAME) / 32).

Lemma nt_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
  intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
  pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
  assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
  split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma nt_sp1_range : forall sp0, 0 <= sp0 - NL_TALK_AFRAME -> sp0 mod 16 = 0 ->
  sp0 - NL_TALK_AFRAME - 16 <= nt_sp1 sp0 <= sp0 - NL_TALK_AFRAME /\
  nt_sp1 sp0 mod 32 = 0 /\ nt_sp1 sp0 mod 16 = 0.
Proof.
  intros sp0 H0 H16. unfold nt_sp1.
  assert (Hm : (sp0 - NL_TALK_AFRAME) mod 16 = 0)
    by (rewrite <- Zminus_mod_idemp_l, H16; reflexivity).
  destruct (nt_sp1_facts (sp0 - NL_TALK_AFRAME) H0 Hm) as (A & B & C). split; [lia | split; assumption].
Qed.

(* The spill slots, as offsets from the realigned stack pointer. *)
Definition NS_ALIAS : Z := 8.      (* the alias buffer:   sd s9, 8(s1)     +0x320; ld a1, 8(s1)     +0x384 *)
Definition NS_ALIASN : Z := 16.    (* its cap:            sd s7, 0x10(s1)  +0x324; ld a2, 0x10(s1)  +0x388 *)
Definition NS_SH4 : Z := 24.       (* the frame's shadow + 4: sd s3, 0x18(s1) +0x1e0; ld a0, 0x18(s1) +0x4ec *)
Definition NS_FK : Z := 32.        (* frame_alloc_9's result: sd s4, 0x20(s1) +0x1d0; ld s4, 0x20(s1) +0x4f4 *)
Definition NS_FD : Z := 40.        (* the socket:         sd s6, 0x28(s1)  +0x1f0; ld a0, 0x28(s1)  +0x294, +0x4dc *)
Definition NS_KIND : Z := 48.      (* the kind buffer:    sd a2, 0x30(s1)  +0x54;  ld a1, 0x30(s1)  +0x3ec *)
Definition NS_KINDN : Z := 56.     (* its cap:            sd a3, 0x38(s1)  +0x50;  ld a2, 0x38(s1)  +0x3f0 *)
Definition NS_F : Z := 80.         (* the frame:          sd s2, 0x50(s1)  +0xc0 (never read)               *)
Definition NT_SPILL : Z := 88.     (* the bytes of [s1, s1 + 88) the body writes                            *)

(* The frame's own numbers (class 9: 32768-byte slots, 2084 shadow bytes for the 16672 the code asks for). *)
Definition NT_CID : Z := 9.
Definition NT_FSZ : Z := 16672.    (* lui a0, 4; addiw a0, a0, 0x120   +0x7c, +0x80 *)
Definition NT_NSH : Z := 2084.     (* NT_FSZ / 8                                     *)
Definition NT_BUFOFF : Z := 32.    (* addi s10, s2, 0x20               +0x1d4        *)
Definition NT_BUFLEN : Z := 16384. (* lui a2, 4                        +0x1ec        *)
Definition NT_MAGIC : Z := 0x41b58ab3.   (* lui a0, 0x41b59; addiw a0, a0, -0x54d  +0xc4, +0xd4 *)
Definition NT_RETIRED : Z := 0x45e0360e. (* lui a0, 0x45e03; addiw a0, a0, 0x60e   +0x4f8, +0x4fc *)

Lemma NT_sizes : NT_FSZ = 16672 /\ NT_NSH * 8 = NT_FSZ /\ NT_BUFOFF + NT_BUFLEN <= NT_FSZ /\
  NL_TALK_AK = NL_TALK_AFRAME + NL_TALK_ASLACK + COPY_ATTR_AK /\ NL_TALK_AK = 8448.
Proof. unfold NT_FSZ, NT_NSH, NT_BUFOFF, NT_BUFLEN. repeat split; first [reflexivity | lia]. Qed.

(* ==========================================================================
   3. The call's context and its premises
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.

(* Everything the contract's premises fix, in one record, so that a phase lemma states one hypothesis instead
   of forty and the phases can be split across files (pcap's ncx, PcapSourceNextDefs.v:235-250). *)
Record ntcx := mkNTCX {
  n_G : list (Z * Z); n_XO : Z; n_OUT : list (Z * Z);
  n_STK : Z; n_sp0 : Z; n_FP : list (Z * Z);
  n_ly : alayout; n_S : astate; n_W0 : world SEGS; n_mem0 : word -> option byte; n_md0 : Model;
  n_own : list (Z * Z);
  n_lyc : alayout; n_Sc : astate; n_W : world SEGS; n_memc : word -> option byte; n_mdc : Model;
  n_k : Z;
  n_regs : bvmap 5 word;
  n_kbs : list byte;               (* g_nl's bytes at the call                                     *)
  n_reqb : list byte;              (* the request's bytes                                          *)
  n_E0 : env                       (* the atoms of the entry registers                             *)
}.

(* the arguments, by name *)
Definition n_req (cx : ntcx) : Z := aarg (n_regs cx) 0.
Definition n_len (cx : ntcx) : Z := aarg (n_regs cx) 1.
Definition n_kind (cx : ntcx) : Z := aarg (n_regs cx) 2.
Definition n_kindn (cx : ntcx) : Z := aarg (n_regs cx) 3.
Definition n_alias (cx : ntcx) : Z := aarg (n_regs cx) 4.
Definition n_aliasn (cx : ntcx) : Z := aarg (n_regs cx) 5.
(* the memory the walk sees at the call, the realigned stack pointer, and the frame's addresses *)
Definition n_m (cx : ntcx) : word -> option byte := rdW (n_W cx) (n_memc cx).
Definition n_sp1 (cx : ntcx) : Z := nt_sp1 (spZ (n_regs cx)).
Definition nF (cx : ntcx) (fp : Z) : Z := frame_addr (n_lyc cx) NT_CID fp.
Definition nSH (cx : ntcx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (nF cx fp).
Definition nBUF (cx : ntcx) (fp : Z) : Z := nF cx fp + NT_BUFOFF.

(* The write set and the read set of the contract, at this call. *)
Definition n_Wr (cx : ntcx) : list (Z * Z) := nl_talk_awr (n_regs cx) (n_m cx).
Definition n_E (cx : ntcx) : Z -> Prop := fun a => inFP (n_Wr cx) a.
Definition n_Rd (cx : ntcx) : Z -> Prop := nl_talk_ard (n_regs cx) (n_m cx).

(* What every phase may assume of the call: exactly the premises of nl_talk_acontract at
   segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi, plus the atoms of the entry registers. *)
Definition nt_base (cx : ntcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B NL_TALK_AK 0 NL_TALK_ASIDE (n_Wr cx)
    (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
    (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx) /\
  (forall a, n_Rd cx a -> akb SEGS B (n_lyc cx) (n_Sc cx) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) a) /\
  nl_talk_apre SEGS B (n_regs cx) (n_m cx) /\
  anlk_at SEGS (n_m cx) LA_G_NL (n_kbs cx) /\
  abytes SEGS (n_m cx) (n_req cx) (n_reqb cx) /\ Z.of_nat (length (n_reqb cx)) = n_len cx /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (n_E0 cx) n = getr (n_regs cx) r) /\
  bv_unsigned (ew (n_E0 cx) 2) = spZ (n_regs cx).

(* The post of the whole call, in the shape nl_talk_acontract asks. *)
Definition nt_post (cx : ntcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B NL_TALK_AK 0 (n_E cx)
    (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
    (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (n_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (n_lyc cx) (n_Sc cx)) /\
       nl_talk_apost SEGS (n_regs cx) (n_m cx) regs2 (rdW W2 mem2)).

(* ==========================================================================
   4. A phase
   ========================================================================== *)

(* `nt_from POST GI`: from any machine state GI describes, with the class-9 frame taken at slot fp and the
   caller's journal extended by it, the run reaches POST. *)
Definition nt_from (POST : ntcx -> world SEGS -> config -> Prop)
  (GI : ntcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ntcx) (fp k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  nt_base cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  GI cx fp k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under nt_base to the same post. The entry phase proves it. *)
Definition nt_start (POST : ntcx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : ntcx, nt_base cx ->
  SRr SEGS (n_W cx) (cfg_at SEGS (BASE + NT_entry) (n_regs cx) (n_memc cx) (n_mdc cx)) (POST cx).

(* ==========================================================================
   5. The state at a cut
   ========================================================================== *)

(* The journal's bookkeeping at every cut while the class-9 frame at slot fp is live: no allocator event
   (EV = 0), the caller's blocks up to a permutation (an own callee's post picks a fresh layout, so equality
   is too strong), the side stack as the only part of the allocator state that moved, the layout's frame
   addresses unchanged, a witness state at the CALL's layout for `apost_side`, and no descriptor or
   file-system change. *)
Definition nt_jbk (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (md3 : Model) : Prop :=
  k2 = n_k cx /\
  Permutation (ablocks B ly3 S3) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  S3 = set_fs (st_fs S3) (n_Sc cx) /\
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) /\
  ~ In (NT_CID, fp) (frames (n_Sc cx)) /\
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) /\
  (exists S1 W1 mem1 md1, AR SEGS B (n_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (NT_CID, fp) :: frames (n_Sc cx) /\
     ablocks B (n_lyc cx) S1 = ablocks B (n_lyc cx) (n_Sc cx)) /\
  m_fds md3 = m_fds (n_mdc cx) /\ m_fs md3 = m_fs (n_mdc cx).

(* What the call keeps of the caller's memory at a cut: ONE akept clause, whose exception set is the bytes E
   (inside the contract's write set) and the bytes of the class-9 frame the call took — its range, its shadow
   and its flag byte, which frame_alloc_9 itself writes (LinkWalkSide.v `aside_rng`; the side-frame recipe, which
   `apost_side` consumes and `akept_drop_side` closes). The heap-block shadow is not carried: `ashadow_kept_AR`
   gives it from the two ends' AR. *)
Definition nt_kept (cx : ntcx) (E : Z -> Prop) (fp : Z) (W3 : world SEGS)
    (mem3 : word -> option byte) : Prop :=
  akept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem3
    (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx))
    (fun a => E a \/ aside_rng (n_lyc cx) NT_CID fp a) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem3) /\
  (forall a, E a -> n_E cx a).

(* A machine word at an address, as the walk reads a spill slot or the frame's header back. *)
Definition nt_at (W3 : world SEGS) (ms3 : machine_state) (a v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v.

(* The spill slots the body writes before the first call of fuzz_socket, and keeps to the end. *)
Definition nt_slots0 (cx : ntcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nt_at W3 ms3 (n_sp1 cx + NS_KIND) (n_kind cx) /\
  nt_at W3 ms3 (n_sp1 cx + NS_KINDN) (n_kindn cx) /\
  nt_at W3 ms3 (n_sp1 cx + NS_F) (nF cx fp).

(* ... and the three the body writes after fuzz_send (the frame's shadow + 4, the frame, the socket). *)
Definition nt_slots1 (cx : ntcx) (fp fd : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nt_slots0 cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) fd.

(* The saved registers of the machine frame, which the epilogue reads back (+0x08..+0x38, +0x534..+0x568). *)
Definition nt_saved (cx : ntcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nt_at W3 ms3 (spZ (n_regs cx) - 8) (raZ (n_regs cx)) /\
  forall j, 0 <= j < 12 ->
    nt_at W3 ms3 (spZ (n_regs cx) - 16 - 8 * j)
      (bv_unsigned (getr (n_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))).

(* The frame's header as the prologue writes it (+0xe0..+0xe8): the live magic, the frame's description string
   (an image object of LinkAddr.v) and the function's own address; and the slot's last word, which
   frame_alloc_9 leaves holding the address of the slot's flag byte (LinkWalkSide.v aj_gx_stack_malloc_sz_at's
   post) and which frame_release_9 reads (aj_gx_stack_free_at's premise). The body writes only
   [F, F + 16672) and the frame's shadow, so that word is kept to the end. *)
Definition nt_header (cx : ntcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nt_at W3 ms3 (nF cx fp) NT_MAGIC /\
  nt_at W3 ms3 (nF cx fp + 8) 0x201ef /\
  nt_at W3 ms3 (nF cx fp + 16) (link_text + AF_nl_talk) /\
  nt_at W3 ms3 (nF cx fp + fs_frame_bytes NT_CID - 8) (flag_addr (n_lyc cx) NT_CID fp).

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the entry stack
   pointer in s0, the shadow base in s5, the frame in s2, its shadow address in s8, gp and tp. *)
Definition nt_regs (cx : ntcx) (fp : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (n_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 18 = w64 (nF cx fp) /\
  getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 24 = w64 (nSH cx fp) /\
  getr (ms_regs ms3) 3 = getr (n_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (n_regs cx) 4.

(* The fixed fields of a machine state at a cut. *)
Definition nt_shape (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr.

(* ==========================================================================
   6. The model, and what the caller's memory looks like at the phase boundaries
   ========================================================================== *)

(* The exchange this call computes: link_spec's kstate of g_nl at the call. *)
Definition n_K0 (cx : ntcx) : kstate := nk_kstate (n_kbs cx).

(* g_nl while the socket is open: fuzz_socket has run and, when `sent` is true, fuzz_send has run too.
   `nextv` is the cursor the receives have reached. *)
Definition nt_gnl_open (cx : ntcx) (bs : list byte) (sent : bool) (nextv : Z) : Prop :=
  nlk_wf bs /\
  nk_chunks bs = nk_chunks (n_kbs cx) /\ nk_n_chunks bs = nk_n_chunks (n_kbs cx) /\
  nk_end_errno bs = nk_end_errno (n_kbs cx) /\ nk_n_if bs = nk_n_if (n_kbs cx) /\
  nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  nk_open bs = 1 /\ nk_misuse bs = nk_misuse (n_kbs cx) /\
  nk_opened bs = nk_opened (n_kbs cx) + 1 /\ nk_closed bs = nk_closed (n_kbs cx) /\
  nk_next bs = nextv /\
  nk_sent bs = (if sent then owe (nk_sent (n_kbs cx)) (n_reqb cx) else nk_sent (n_kbs cx)) /\
  nk_n_sent bs = Z.of_nat (length (nk_sent bs)).

(* g_nl at the end of the call: the kernel clause of nl_talk_apost, at the byte list bs. *)
Definition nt_gnl_fin (cx : ntcx) (bs : list byte) : Prop :=
  nlk_wf bs /\
  nk_chunks bs = nk_chunks (n_kbs cx) /\ nk_end_errno bs = nk_end_errno (n_kbs cx) /\
  nk_n_if bs = nk_n_if (n_kbs cx) /\
  nk_socket_errno bs = 0 /\
  nk_send_errno bs = k_send (talk_after (n_K0 cx)) /\
  nk_next bs = Z.of_nat (k_next (talk_after (n_K0 cx))) /\
  nk_sent bs = (if talk_owes (n_K0 cx) then owe (nk_sent (n_kbs cx)) (n_reqb cx) else nk_sent (n_kbs cx)) /\
  nk_n_sent bs = Z.of_nat (length (nk_sent bs)) /\
  nk_open bs = 0 /\ nk_misuse bs = nk_misuse (n_kbs cx) /\
  nk_opened bs - nk_closed bs = nk_opened (n_kbs cx) - nk_closed (n_kbs cx) /\
  (nk_socket_errno (n_kbs cx) <> 0 -> nk_opened bs = nk_opened (n_kbs cx)) /\
  (nk_socket_errno (n_kbs cx) = 0 -> nk_opened bs = nk_opened (n_kbs cx) + 1).

(* The caller's two buffers, as the entry memory left them (no copy_attr call has written them yet). *)
Definition nt_bufs_same (cx : ntcx) (m' : word -> option byte) : Prop :=
  (n_kind cx <> 0 -> forall s, Z.of_nat (length s) < n_kindn cx -> acstr_at SEGS (n_m cx) (n_kind cx) s ->
     acstr_at SEGS m' (n_kind cx) s) /\
  (n_alias cx <> 0 -> forall s, Z.of_nat (length s) < n_aliasn cx -> acstr_at SEGS (n_m cx) (n_alias cx) s ->
     acstr_at SEGS m' (n_alias cx) s) /\
  (n_kind cx <> 0 -> 1 <= n_kindn cx -> abuf SEGS m' (n_kind cx) (n_kindn cx)) /\
  (n_alias cx <> 0 -> 1 <= n_aliasn cx -> abuf SEGS m' (n_alias cx) (n_aliasn cx)).

(* ... and as the call must leave them: the four buffer clauses of nl_talk_apost. *)
Definition nt_bufs_fin (cx : ntcx) (m' : word -> option byte) : Prop :=
  (forall pay, a_kind (talk_attrs (n_K0 cx)) = Some pay -> n_kind cx <> 0 -> 1 <= n_kindn cx ->
     acstr_at SEGS m' (n_kind cx) (cut_text pay (n_kindn cx))) /\
  (forall pay, a_alias (talk_attrs (n_K0 cx)) = Some pay -> n_alias cx <> 0 -> 1 <= n_aliasn cx ->
     acstr_at SEGS m' (n_alias cx) (cut_text pay (n_aliasn cx))) /\
  (a_kind (talk_attrs (n_K0 cx)) = None -> n_kind cx <> 0 -> forall s,
     Z.of_nat (length s) < n_kindn cx -> acstr_at SEGS (n_m cx) (n_kind cx) s ->
     acstr_at SEGS m' (n_kind cx) s) /\
  (a_alias (talk_attrs (n_K0 cx)) = None -> n_alias cx <> 0 -> forall s,
     Z.of_nat (length s) < n_aliasn cx -> acstr_at SEGS (n_m cx) (n_alias cx) s ->
     acstr_at SEGS m' (n_alias cx) s) /\
  (n_kind cx <> 0 -> 1 <= n_kindn cx -> abuf SEGS m' (n_kind cx) (n_kindn cx)) /\
  (n_alias cx <> 0 -> 1 <= n_aliasn cx -> abuf SEGS m' (n_alias cx) (n_aliasn cx)).

(* The shadow of the class-9 frame, as the prologue and the two meta_fill calls leave it: the left redzone
   (4 bytes 0xf1, +0xf4..+0x100), the 2048 bytes of the buffer (v: 0xf8 unusable, 0 usable) and the right
   redzone (32 bytes 0xf3, +0x120..+0x19c). *)
Definition nt_frame_shadow (cx : ntcx) (fp v : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i) = Some 0xf1) /\
  (forall i, 0 <= i < 2048 -> aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 4 + i) = Some v) /\
  (forall i, 0 <= i < 32 -> aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 2052 + i) = Some 0xf3).


(* When the exchange saw no attribute, the buffers the call must leave are the buffers it found: the two
   failure arms and the arms that answer an NLMSG_ERROR or run out of chunks go through this. *)
Lemma nt_bufs_same_fin : forall cx m',
  talk_attrs (n_K0 cx) = no_attrs -> nt_bufs_same cx m' -> nt_bufs_fin cx m'.
Proof.
  intros cx m' Ha (K1 & K2 & K3 & K4). unfold nt_bufs_fin. rewrite Ha. cbn [a_kind a_alias no_attrs].
  split; [intros pay Hp; discriminate Hp|].
  split; [intros pay Hp; discriminate Hp|].
  split; [intros _ Hk s Hs Hc; exact (K1 Hk s Hs Hc)|].
  split; [intros _ Ha2 s Hs Hc; exact (K2 Ha2 s Hs Hc)|].
  split; [exact K3 | exact K4].
Qed.
(* ==========================================================================
   7. The phase boundaries
   ========================================================================== *)

(* NT_sock (+0x1a0): the class-9 frame is taken, its header and its 2084 shadow bytes are written (the
   16384-byte buffer marked unusable) and the two kind slots are spilled. Nothing of the caller's memory has
   changed yet. The entry phase proves this; the socket phase consumes it.
   Registers here: s3 = the frame's shadow + 4, s4 = s2 = the frame, s7 = alias_n, s9 = alias, s10 = len,
   s11 = req. *)
Definition nt_sock_inv (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_sock ms3 /\ nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\
  nt_slots0 cx fp W3 ms3 /\
  getr (ms_regs ms3) 19 = w64 (nSH cx fp + 4) /\
  getr (ms_regs ms3) 20 = w64 (nF cx fp) /\
  getr (ms_regs ms3) 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms3) 25 = w64 (n_alias cx) /\
  getr (ms_regs ms3) 26 = w64 (n_len cx) /\
  getr (ms_regs ms3) 27 = w64 (n_req cx) /\
  nt_frame_shadow cx fp 0xf8 W3 ms3 /\
  nt_jbk cx fp k2 ly3 S3 md3 /\ nt_kept cx (fun _ => False) fp W3 (ms_mem ms3) /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL (n_kbs cx) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (n_req cx) (n_reqb cx) /\
  nt_bufs_same cx (rdW W3 (ms_mem ms3)) /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN.

(* NT_mf0_ra (+0x1ec): the socket is open, the request is sent, the receive buffer is usable, and the first
   fuzz_recv is about to be made. The entry and send phases prove this; the receive phase consumes it.
   Registers here: s3 = the frame's shadow + 4, s4 = the frame, s6 = the socket, s10 = the buffer. *)
Definition nt_recv_inv (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_mf0_ra ms3 /\ nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\
  nt_slots0 cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  getr (ms_regs ms3) 19 = w64 (nSH cx fp + 4) /\
  getr (ms_regs ms3) 20 = w64 (nF cx fp) /\
  getr (ms_regs ms3) 22 = w64 NL_FD /\
  getr (ms_regs ms3) 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms3) 25 = w64 (n_alias cx) /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp) /\
  nt_frame_shadow cx fp 0 W3 ms3 /\
  nt_jbk cx fp k2 ly3 S3 md3 /\ nt_kept cx (n_E cx) fp W3 (ms_mem ms3) /\
  (exists bs, anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\
     nt_gnl_open cx bs true (Z.of_nat (k_next (n_K0 cx)))) /\
  talk_owes (n_K0 cx) = true /\
  nt_bufs_same cx (rdW W3 (ms_mem ms3)) /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN.

(* NT_attr (+0x314): the message walk found the first RTM_NEWLINK. a1 is the message's address inside the
   buffer and a3 its length; the model's answer is that message's attribute walk. The receive phase proves
   this; the attribute phase consumes it. *)
Definition nt_attr_inv (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (c rest : list byte) (off ml : Z) (f : nat) (bs : list byte),
  nt_shape NT_attr ms3 /\ nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\
  nt_slots0 cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\
  getr (ms_regs ms3) 11 = w64 (nBUF cx fp + off) /\
  getr (ms_regs ms3) 13 = w64 ml /\
  getr (ms_regs ms3) 25 = w64 (n_alias cx) /\
  getr (ms_regs ms3) 23 = w64 (n_aliasn cx) /\
  nt_frame_shadow cx fp 0 W3 ms3 /\
  nt_jbk cx fp k2 ly3 S3 md3 /\ nt_kept cx (n_E cx) fp W3 (ms_mem ms3) /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\
  nt_gnl_open cx bs true (Z.of_nat (k_next (talk_after (n_K0 cx)))) /\
  talk_owes (n_K0 cx) = true /\
  nt_bufs_same cx (rdW W3 (ms_mem ms3)) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) (c ++ rest) /\
  Z.of_nat (length (c ++ rest)) = NT_BUFLEN /\ (length c <= Z.to_nat NL_CHUNK_MAX)%nat /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN /\
  0 <= off /\ NL_HDR <= ml /\ off + ml <= Z.of_nat (length c) /\
  (Z.to_nat (ml - NL_HDR - IFI_LEN) < f)%nat /\
  talk_rc_lib (n_K0 cx) = 0 /\
  talk_attrs (n_K0 cx) = attr_scan f c (off + NL_HDR + IFI_LEN) (ml - NL_HDR - IFI_LEN) no_attrs.

(* NT_exit (+0x4dc): the answer is in s11 and the caller's buffers are final; the socket is still open and
   the buffer still usable. fuzz_close and the second meta_fill_f8 are still to come. *)
Definition nt_exit_inv (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_exit ms3 /\ nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\
  getr (ms_regs ms3) 27 = w64 (talk_rc_lib (n_K0 cx)) /\
  nt_frame_shadow cx fp 0 W3 ms3 /\
  nt_jbk cx fp k2 ly3 S3 md3 /\ nt_kept cx (n_E cx) fp W3 (ms_mem ms3) /\
  (exists bs, anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\
     nt_gnl_open cx bs (talk_owes (n_K0 cx)) (Z.of_nat (k_next (talk_after (n_K0 cx))))) /\
  talk_owes (n_K0 cx) = true /\
  nt_bufs_fin cx (rdW W3 (ms_mem ms3)).

(* NT_tail (+0x4f8): everything the call does to the caller's memory is done. The socket failure arm and the
   send failure arm join here too, so g_nl is final (they never opened it, or they closed it themselves) and
   the frame's buffer is marked unusable on every path. s2 and s4 hold the frame. *)
Definition nt_tail_inv (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_tail ms3 /\ nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\
  getr (ms_regs ms3) 20 = w64 (nF cx fp) /\
  getr (ms_regs ms3) 27 = w64 (talk_rc_lib (n_K0 cx)) /\
  nt_jbk cx fp k2 ly3 S3 md3 /\ nt_kept cx (n_E cx) fp W3 (ms_mem ms3) /\
  (exists bs, anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\ nt_gnl_fin cx bs) /\
  nt_bufs_fin cx (rdW W3 (ms_mem ms3)).

(* Two byte lists at one address with one length are one list: the Post quantifies over g_nl's bytes and the
   request's bytes again, and this identifies them with the context's. *)
Lemma nt_abytes_unique : forall (m : word -> option byte) a bs bs',
  abytes SEGS m a bs -> abytes SEGS m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (H0 & H1 & H2) (H0' & H1' & H2') Hlen.
  apply lw_list_ext; [exact Hlen|]. intros k Hk.
  rewrite <- (H2 k Hk), <- (H2' k ltac:(lia)). reflexivity.
Qed.

End b.
End a.

(* SK is an explicit argument of every statement above (Context (SK : YI16.sink_head), no braces): the only
   global sink_head instance of this closure is the plain build's (lib/Reusable/YI5b.v), so it must never be
   inferred. *)
