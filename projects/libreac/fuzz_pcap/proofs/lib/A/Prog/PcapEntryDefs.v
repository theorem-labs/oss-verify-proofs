(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryDefs.v, with its module paths changed; 265 of its 330 lines of code are new or changed and 295 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* The walk of fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x807c8, listing offset
   AF_LLVMFuzzerTestOneInput = 0x90) on the ASan build of libreac v1.9.0, cut into phases:
   the data every phase shares. The form is a Theorem Labs lane's lib/A/Prog/GrantEntryDefs.v
   (a working branch); the statement the phases prove together is lib/A/Prog/PcapEntry.v.

   Every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...;
   symbols from its unstripped twin, capstone 5 disassembly). The comment beside a number
   names the instruction it comes from, by its address.

   The entry function keeps two frames at once:
   - a machine-stack frame of 224 bytes (`addi sp,sp,-0xe0` 0x807c8; `sd zero,0(sp)` 0x807cc
     probes its lowest word). ra and s0..s11 are saved at sp0-8 .. sp0-104 (0x807d0..0x80800),
     s0 := sp0 (`addi s0,sp,0xe0` 0x80804), the stack is realigned to 32 bytes (`andi sp,sp,-0x20`
     0x80808) and s1 := that stack pointer (`mv s1,sp` 0x8080c). s1 is the base of the spill
     slots, and every call of the body is made with sp = s1;
   - a frame on the side stack for frames, class 1 (128-byte slots). When the use-after-return
     flag (the word at 0xa18c0, through its GOT word 0x99888: 0x80818, 0x8081c, 0x80824) is not
     zero, `__asan_stack_malloc_1(0x80)` (a0 := 0x80 at 0x80834, `jal` 0x80838, return address
     0x8083c) gives the frame F in a0; s4 := a0 (0x8083c), s7 := s4 (0x80848). When the flag is 0
     or the call returns 0, the body takes F on the machine stack instead (0x80850..0x80868:
     s7 := (sp - 0x80) & -32, a 4096-byte probe, sp := s7). F stays in s7 until 0x80b1c; it is
     spilled at 0x70(s1) (0x8086c) and 0x10(s1) (0x80ac8), and the side-stack result at 0x18(s1)
     (0x80ac4). The 16 shadow bytes of F start at shadow_of_addr SHADOW_OFF F, which s9 holds
     (`srli s9,s7,3` 0x8087c, `add s9,s9,s11` 0x808a8; spilled at 0x8(s1), 0x80ad0) with s11 the
     shadow base (`ld s11,0(a1)` 0x80828 from the cell 0xa18b8 through its GOT word 0x99830).

   One phase = one file; the cut between two phases is semantic (`pe_from` below), never a
   symbolic state, so that no phase has to compute another phase's state. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry.
(* lib/A's image data and instance (split out of PcapEntry.v, which names no image). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntryA.
(* The asan stdio pcs have ONE home, lib/A/Stdio/PStdioImgA.v (a Theorem Labs lane's single-home rule); take FM_MALLOC_RA from it. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PStdioImgA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
(* The plain functional model of the reader and of the harness's output, required without Import
   (their own imports include lib/Lib): every use below is fully qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
(* The allocation-trace universe and its per-site facts. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require ACej ACejSites.
(* The journal with program-global ranges (W_journal.v, by path from fuzz_reply's lib/A/W_journal.v at commit 6328acea202). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
(* cgif's trivial meter, the one the closing side instantiates (donor AD1q.v:50 LIBX with XL0 XL0). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the output of a call ---- *)

(* v1.9.0's pcap_source_next prints nothing (lib/Prog/pcap_source_struct_next.v:21-25), so the
   output the agreement shape gives a call, PWalk.OUT (lib/Prog/Slot/PWalk.v:205), is empty: the
   walk's chain outputs are all [] (chain_out_nil, pcap_source_struct_next.v:93), and so is the
   walk that strings them (by induction on its fuel). PcapEntry.tfib_lib_post_x states
   `ll_out l = PWalk.OUT pl`; the bridge from pe_post takes l := LL 0 (m_fs md) (PWalk.OUT pl) and
   meets the shape's `wr ch_stderr (PWalk.OUT pl) _` with this lemma. *)
Lemma pcap_walk_out_nil : forall fuel sw F cap p,
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.walk_out fuel sw F cap p = [].
Proof.
  induction fuel as [|f IH]; intros sw F cap p; [reflexivity|].
  rewrite OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.walk_out_S.
  unfold OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.psn_chain.
  rewrite OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.chain_out_nil.
  cbn [app].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [apply IH | reflexivity].
Qed.

Lemma pcap_OUT_nil : forall pl, OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl = [].
Proof.
  intros pl. unfold OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT.
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct pl as [|d F]; [reflexivity|].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [|reflexivity].
  cbv zeta. rewrite pcap_walk_out_nil. cbn [app].
  unfold OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.psn_chain.
  apply OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.chain_out_nil.
Qed.

(* ---- the machine frame ---- *)

Definition PE_MFRAME : Z := 224.          (* addi sp,sp,-0xe0               0x807c8 *)
(* The realigned stack pointer that s1 holds for the whole body. *)
Definition pe_sp1 (sp0 : Z) : Z := 32 * ((sp0 - PE_MFRAME) / 32).
                                          (* andi sp,sp,-0x20 0x80808; mv s1,sp 0x8080c *)

(* ---- the frame on the side stack ---- *)

Definition PE_CID : Z := 1.               (* jal __asan_stack_malloc_1      0x80838 *)
Definition PE_FREQ : Z := 128.            (* addi a0,zero,0x80 (the request) 0x80834 *)
Definition PE_FRAME : Z := 128.           (* the slot, fs_frame_bytes 1 *)
Definition PE_NSH : nat := 16%nat.        (* its shadow bytes, 0(s9)..0xf(s9) *)
(* The frame's header, written before any check: the live-frame magic, the address of the
   frame's description string (object 5) and the function's own address (object 6). *)
Definition PE_MAGIC : Z := 0x41b58ab3.    (* lui a0,0x41b59 0x80870; addiw a0,a0,-0x54d 0x8088c; sd a0,0(s7) 0x80898 *)
Definition PE_DESCR : Z := Eval compute in (Symbols.Asan.Sec.s_rodata + 0x3414)%Z.  (* auipc a1,0xfff93 0x80874; addi a1,a1,-0x180 0x80890; sd a1,8(s7) 0x8089c *)
Definition PE_FNPC : Z := Eval compute in Symbols.Asan.s_LLVMFuzzerTestOneInput.  (* auipc a2,0 0x80878; addi a2,a2,-0xb0 0x80894; sd a2,0x10(s7) 0x808a0 *)
(* What the epilogue writes when it gives the frame back: the retired-frame magic at F, and,
   for a side-stack frame, 0 through the flag pointer the slot keeps in its last word. *)
Definition PE_RETIRED : Z := 0x45e0360e.  (* lui a0,0x45e03 0x81134; addiw a0,a0,0x60e 0x81138; sd a0,0(s7) 0x8113c *)
Definition PE_FLAGPTR : Z := 120.         (* ld a0,0x78(s4) 0x81188; sb zero,0(a0) 0x8118c *)

(* ---- the frame's objects ---- *)

Definition PO_PS : Z := 32.               (* struct pcap_source ps: addi a0,s7,0x20 0x80950 *)
Definition PO_PS_LEN : Z := 24.           (* memset(&ps,0xa5,24): addi a2,zero,0x18 0x80984 *)
Definition PE_PS_FILL : Z := 165.         (* addi a1,zero,0xa5 0x80980; __asan_memset 0x8098c *)
Definition PO_TS : Z := 96.               (* uint64_t ts: addi a3,s7,0x60 0x80acc *)
(* ts := ~0 before the walk (sd a0,0(a3) 0x80adc) and after each record (sd a0,0(a3) 0x80f80). *)
Definition PE_TS_NONE : Z := 2 ^ 64 - 1.  (* addi a0,zero,-1 0x80ad8, 0x80f78 *)

(* ---- the frame's shadow ---- *)

(* The 16 shadow bytes as the prologue leaves them (0x808ac..0x808ec, the values in a5 = 0xf1,
   a4 = 0xf8, a3 = 0xf2, a0 = 0xf3 from 0x80880..0x808a4): 0xf1 the left redzone (F+0..31),
   0xf8 `ps` out of scope (F+32..55), 0xf2 between the objects (F+56..95), 0xf8 `ts` out of scope
   (F+96..103), 0xf3 the right redzone (F+104..127). *)
Definition PSH_entry : list Z :=
  [241;241;241;241; 248;248;248; 242; 242;242;242;242; 248; 243;243;243].

Definition psh_set (sh : list Z) (lo n : nat) (v : Z) : list Z :=
  firstn lo sh ++ repeat v n ++ skipn (lo + n) sh.
(* `ps` in scope: sb zero,4(s9) / 5(s9) / 6(s9) 0x80974..0x8097c (before __asan_memset). *)
Definition PSH_ps : list Z := psh_set PSH_entry 4 3 0.
(* `ts` in scope: sb zero,0xc(s9) 0x80ad4 (after the record buffer is allocated). *)
Definition PSH_ts : list Z := psh_set PSH_ps 12 1 0.
(* `ts` out of scope again: sb a0,0xc(s9) with a0 = 0xf8, 0x81118..0x81120 (end of the body). *)
Definition PSH_tsout : list Z := psh_set PSH_ts 12 1 248.
(* `ps` out of scope again: sb a0,4/5/6(s9) with a0 = 0xf8, 0x81124..0x81130, reached from the
   end of the body (PSH_tsout) and from the refused open (PSH_ps); both give PSH_entry back. *)
Definition PSH_out (sh : list Z) : list Z := psh_set sh 4 3 248.
(* The frame given back: every shadow byte 0xf5 for a side-stack frame (a0 = -0xb 0x81144,
   0x81148..0x81184), every shadow byte 0 for a frame on the machine stack (0x81194..0x811d0). *)
Definition PSH_retired : list Z := repeat 245 16.
Definition PSH_machine : list Z := repeat 0 16.

Lemma PSH_entry_len : length PSH_entry = PE_NSH.
Proof. reflexivity. Qed.
Lemma PE_FRAME_slot : fs_frame_bytes PE_CID = PE_FRAME /\ PE_FREQ <= PE_FRAME /\ Z.of_nat PE_NSH = PE_FRAME / 8.
Proof. split; [vm_compute; reflexivity|]. split; [unfold PE_FREQ, PE_FRAME; lia | vm_compute; reflexivity]. Qed.
Lemma PSH_out_body : PSH_out PSH_tsout = PSH_entry.
Proof. reflexivity. Qed.
Lemma PSH_out_refused : PSH_out PSH_ps = PSH_entry.
Proof. reflexivity. Qed.

(* ---- the spill slots, as offsets from s1 ---- *)

Definition PS_SH : Z := 8.        (* s9 = the shadow of F:       sd s9,8(s1) 0x80ad0; reloaded 0x8111c *)
Definition PS_F : Z := 16.        (* s7 = F:                     sd s7,0x10(s1) 0x80ac8; reloaded 0x81090 *)
Definition PS_FK : Z := 24.       (* s4 = __asan_stack_malloc_1's result (0 for a machine frame):
                                     sd s4,0x18(s1) 0x80ac4; reloaded 0x8108c *)
Definition PS_D : Z := 32.        (* the first input byte d (cap = 8 d), 0 for an empty input:
                                     sd a0,0x20(s1) 0x8090c / sd zero,0x20(s1) 0x80920 *)
Definition PS_VMASK : Z := 40.    (* 0xf00, the high byte of the VLAN-id mask: sd a2,0x28(s1) 0x80b24 *)
Definition PS_BUF12 : Z := 48.    (* buf + 12: sd a1,0x30(s1) 0x80b08 *)
Definition PS_USEC : Z := 56.     (* 10^6 * 2^32 (lui a3,0x3d09 0x80b18; slli a3,a3,0x1a 0x80b28):
                                     sd a3,0x38(s1) 0x80b2c *)
Definition PS_GLEN : Z := 64.     (* the auipc value 0x5d3928 (hi 8), g_file_len = it + 0x618:
                                     sd a1,0x40(s1) 0x80934 *)
Definition PS_FIRST : Z := 72.    (* the reader's first answer: sd a3,0x48(s1) 0x80b5c *)
Definition PS_TSP : Z := 80.      (* &ts = F + PO_TS: sd a3,0x50(s1) 0x80aec *)
Definition PS_PSP : Z := 88.      (* &ps = F + PO_PS: sd a0,0x58(s1) 0x80954 *)
Definition PS_F0 : Z := 112.      (* F, first copy: sd s7,0x70(s1) 0x8086c *)
(* The harness's two globals and the path literal, and the values the frame's header and the
   g_file_len spill hold, as the pin gives them and as the listing names them (PcapAddr). *)
Definition PE_G_FILE : Z := Eval compute in Symbols.Asan.s_g_file.  (* object 2: auipc a0,0x553 0x80924; addi s2,a0,0x63c 0x8092c *)
Definition PE_G_FILE_LEN : Z := Eval compute in Symbols.Asan.s_g_file_len.  (* object 4; hi 8 + 0x618: auipc a1,0x553 0x80928; sd s6,0x618(a1) 0x80938 *)
(* g_file_len's low part: the code reaches g_file_len as hi 8 + lo, hi 8 the value of `auipc a1` at
   LLVMFuzzerTestOneInput + 0x160 (0x80928) and lo the signed 12-bit rest (0x618 on the pin), both from Symbols.v.
   PE_GLEN_LO8 = lo + 8 ends the 8-byte object. They elaborate to the numerals. *)
Abbreviation PE_GLEN_LO := (symaddr ((Symbols.Asan.s_g_file_len - (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x160)) -
  (Symbols.Asan.s_g_file_len - (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x160) + 0x800) / 4096 * 4096)%Z) (only parsing).
Abbreviation PE_GLEN_LO8 := (symaddr ((Symbols.Asan.s_g_file_len - (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x160)) -
  (Symbols.Asan.s_g_file_len - (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x160) + 0x800) / 4096 * 4096 + 8)%Z) (only parsing).
Definition PE_PATH : Z := Eval compute in (Symbols.Asan.Sec.s_rodata + 0x10a20)%Z.  (* .rodata + 0x10a20, as .str names several objects; object 3, "<fuzz-input>": auipc a0,0xfffa0 0x80990 / 0x810b8;
                                             addi a1,a0,0x370 0x80994 / addi a1,a0,-0x3b8 0x810bc *)
Lemma PE_pin_values :
  pcap_obj 2 = PE_G_FILE /\ pcap_obj 3 = PE_PATH /\ pcap_obj 4 = PE_G_FILE_LEN /\
  pcap_hi 8 + PE_GLEN_LO = PE_G_FILE_LEN /\ pcap_obj 5 = PE_DESCR /\ pcap_obj 6 = PE_FNPC /\
  pcap_obj 15 = (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address) /\ pcap_obj 16 = (symaddr Symbols.Asan.s___asan_option_detect_stack_use_after_return) /\ pcap_obj 0 = (symaddr (Symbols.Asan.Sec.s_got + 0xb8)%Z) /\ pcap_obj 1 = (symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z).
Proof. repeat split; reflexivity. Qed.

(* ---- the pcs of the phase cuts, as offsets in the listing (address - 0x80738) ---- *)

Definition PP_entry : Z := Eval compute in (Symbols.Asan.s_LLVMFuzzerTestOneInput - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x807c8, the first slot                                  *)
Definition PP_early : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x128) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x808f0, bnez a1 to the return of an input of 2^26+ bytes *)
Definition PP_K1 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x17c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x80944, malloc (0x80940) of the copy of the file returned  *)
Definition PP_dup0 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x180) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x80948, beqz s6: an empty copy (size - 1 = 0) skips the NULL test *)
Definition PP_dupnull : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x184) - Symbols.Asan.s_libreac_fuzz_fopen)%Z. (* 0x8094c, beqz s3 to PP_abort: fuzz_dup's abort when malloc
                                       of size - 1 >= 1 bytes returned NULL *)
Definition PP_K2 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x1d8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x809a0, pcap_source_open (0x8099c) returned               *)
Definition PP_ref : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2ac) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x80a74, open refused or accepted: beqz a0 to the accept arm *)
Definition PP_K3 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2f4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x80abc, malloc (0x80ab8) of the record buffer returned; this
                                       slot is `beqz a0` to PP_abort, the harness's `if (!buf) abort();` *)
Definition PP_KD : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x32c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x80af4, the first pcap_source_next (0x80af0) returned     *)
Definition PP_K4 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x36c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x80b34, the head of the record loop (back edge 0x80fac)   *)
Definition PP_KR : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x3a8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x80b70, the head of the harness's skip loop (back edge 0x80c30) *)
Definition PP_KL2 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x7dc) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x80fa4, the loop's pcap_source_next (0x80fa0) returned    *)
Definition PP_K5 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x8b4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x8107c, the record loop is done                          *)
Definition PP_KW : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xa5c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x81224, the head of the end-of-walk check loop (back edge 0x812f8) *)
Definition PP_K6 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x8e4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x810ac, pcap_source_close (0x810a8) returned              *)
Definition PP_K7 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x900) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x810c8, the second pcap_source_open (0x810c4) returned    *)
Definition PP_K8 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x918) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x810e0, pcap_source_next (0x810dc) returned               *)
Definition PP_K9 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x924) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x810ec, the second pcap_source_close (0x810e8) returned   *)
Definition PP_K10 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x938) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81100, pcap_source_next of the closed reader (0x810fc) returned *)
Definition PP_K11 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x948) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81110, the record buffer is freed (free 0x8110c)         *)
Definition PP_K12 : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x950) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81118, the copy of the file is freed (free 0x81114)      *)
Definition PP_K12r : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x95c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81124, `ps` out of scope; the refused open lands here (j 0x80a88) *)
Definition PP_leave : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x96c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x81134, the frame is given back; the early return lands here *)
Definition PP_ret : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xa4c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81214, the `ret`                                        *)
Definition PP_abort : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xb78) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x81340, __asan_handle_no_return, then abort 0x81344       *)
(* The 17 walks (a Theorem Labs lane's stage list, slot_lscps.v (sha256 15a609daf420; internal record) at 6954866e3be, at the v1.9.0 pcs):
     entry   the first slot: ENTRY (size < 2^26) or EARLY, no instruction
     E       PP_entry -> __asan_stack_malloc_1 0x80838 -> malloc 0x80940 -> PP_K1
     EARLY   PP_entry -> __asan_stack_malloc_1 0x80838 -> PP_early -> PP_leave -> PP_ret
     A       PP_K1 -> __asan_memcpy 0x80968, __asan_memset 0x8098c -> pcap_source_open 0x8099c -> PP_K2
     B_acc   PP_K2 (a0 = 0) -> malloc 0x80ab8 -> PP_K3
     B_ref   PP_K2 (a0 = -1) -> free 0x80a84 -> PP_K12r
     C       PP_K3 -> pcap_source_next 0x80af0 -> PP_KD
     Walk    PP_KD -> PP_K5, through PP_K4, PP_KR, the bcmp wrapper 0x80d8c / 0x80da8 / 0x80e08
             and pcap_source_next 0x80fa0 (PP_KL2)
     W       PP_K5 -> the check loop at PP_KW -> pcap_source_close 0x810a8 -> PP_K6
     R1      PP_K6 -> pcap_source_open 0x810c4 -> PP_K7
     R2      PP_K7 -> pcap_source_next 0x810dc -> PP_K8
     R3      PP_K8 -> pcap_source_close 0x810e8 -> PP_K9
     R4      PP_K9 -> pcap_source_next 0x810fc -> PP_K10
     R5      PP_K10 -> free 0x8110c -> PP_K11
     R6      PP_K11 -> free 0x81114 -> PP_K12
     R7      PP_K12 -> PP_K12r -> PP_leave -> PP_ret
     BT      PP_K12r -> PP_leave -> PP_ret
   Every abort() check branches to PP_abort; every shadow check that fails branches to a call
   of __asan_report_load1 (0x81070, 0x8132c, 0x81348..0x813f0).
   The ASan allocator may return NULL (allocator_may_return_null = 1 in this image), so the two
   NULL arms (PP_dupnull, PP_K3) are branches of the walk like any other. They are closed only by
   the allocator rule's post, `4096 <= res` (YC5d.v:72, amalloc04_rule), whose room premises the
   call carries (st_nev S + EV_LIB <= EV_MAX, blocks_bytes S + LIVE_LIB <= LIVE_MAX, each request
   < MALLOC_MAX), never by an assumption that malloc does not fail. An empty copy (PP_dup0) takes
   no NULL test.

   Stack room at a call of the body. sp = s1 >= sp0 - 240 (sp0 - 368 with a machine-stack frame),
   and s1 mod 32 = 0. pe_base's afn_pre gives astk_ok LLVMF_STK ly sp0: ly_stk_lo + 32768 <= sp0
   and ly_bot + 32768 < sp0 + ASTACK with ly_bot = ly_top - kStackSpan (YG0f.v:36, :63) and
   ASTACK = 16384 (YG0d.v:18), so ly_top - sp0 < 2^23 - 16384. A callee of window STK at s1 needs
   ly_stk_lo + STK <= s1 and ly_top - s1 < 2^23 + 16384 - STK; both follow for STK <= 32400
   (32768 - 368). That covers pcap_source_open's window (at least 112 + 96 + AFMEMOPEN_STK =
   18832), pcap_source_close's (at least 32 + PFCLOSE_STK = 16560), pcap_source_next's (at least
   240 + 64 + AFREAD_STK = 8496), the bcmp wrapper's 2 * ESTACK, and the allocator rules'
   ASTACK - o <= LLVMF_STK (YC5d.v:60; o >= -368). *)

(* ---- the call sites, as listing offsets of their return addresses ---- *)

(* The wrappers for malloc and free that the body calls itself; a callee contract of the
   allocator asks for the call trace at each. *)
Definition PE_MALLOC_SITES : list Z := [0x20c; 0x384].        (* 0x80944, 0x80abc *)
Definition PE_FREE_SITES : list Z := [0x350; 0x9d8; 0x9e0].   (* 0x80a88, 0x81110, 0x81118 *)
Definition PE_SITES : list Z := PE_MALLOC_SITES ++ PE_FREE_SITES.
(* The program functions the body calls, and the other runtime entries. *)
Definition PE_OPEN_SITES : list Z := [0x268; 0x990].                (* 0x809a0, 0x810c8 *)
Definition PE_NEXT_SITES : list Z := [0x3bc; 0x86c; 0x9a8; 0x9c8].  (* 0x80af4, 0x80fa4, 0x810e0, 0x81100 *)
Definition PE_CLOSE_SITES : list Z := [0x974; 0x9b4].               (* 0x810ac, 0x810ec *)
Definition PE_BCMP_SITES : list Z := [0x658; 0x674; 0x6d4].         (* 0x80d90, 0x80dac, 0x80e0c *)
Definition PE_SM_SITE : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x74) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.                                 (* 0x8083c *)
Definition PE_MEMCPY_SITE : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x1a4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.                             (* 0x8096c *)
Definition PE_MEMSET_SITE : Z := Eval compute in ((Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x1c8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.                             (* 0x80990 *)
(* The allocator calls the callees make on the body's behalf (absolute addresses: they are
   musl's, outside the listing): the malloc of fmemopen, under each pcap_source_open, and the
   free(NULL) and free of fclose, under pcap_source_close and the failure arms of
   pcap_source_open (0x81674, 0x816b8). *)
Definition PE_FMEMOPEN_MALLOC_RA : Z := FM_MALLOC_RA.  (* = 0x8e90c, jal __wrap_malloc 0x8e908; single home PStdioImgA *)
Definition PE_FCLOSE_FREE_RAS : list Z :=
  Eval compute in [(Symbols.Asan.s_fclose + 0xa4)%Z; (Symbols.Asan.s_fclose + 0xac)%Z].  (* jal __wrap_free 0x8e2b4, 0x8e2bc *)

(* The cut pcs and the return addresses, as addresses of the pin, and the call each slot holds
   in the listing: checked once here against PcapAddr.pcap_text and PcapList.pcap_listing. *)
Lemma PP_addrs :
  map (fun o => pcap_text + o)
    [PP_entry; PP_early; PP_K1; PP_dup0; PP_dupnull; PP_K2; PP_ref; PP_K3; PP_KD; PP_K4; PP_KR;
     PP_KL2; PP_K5; PP_KW; PP_K6; PP_K7; PP_K8; PP_K9; PP_K10; PP_K11; PP_K12; PP_K12r; PP_leave;
     PP_ret; PP_abort] =
    [(symaddr Symbols.Asan.s_LLVMFuzzerTestOneInput); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x128)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x17c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x180)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x184)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x1d8)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2ac)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2f4)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x32c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x36c)%Z);
     (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x3a8)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x7dc)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x8b4)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xa5c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x8e4)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x900)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x918)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x924)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x938)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x948)%Z);
     (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x950)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x95c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x96c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xa4c)%Z); (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0xb78)%Z)] /\ PP_entry = AF_LLVMFuzzerTestOneInput.
Proof. split; reflexivity. Qed.
Lemma PE_calls_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat ((o - 4) / 4)))
    (PE_SM_SITE :: PE_MEMCPY_SITE :: PE_MEMSET_SITE :: PE_SITES ++ PE_OPEN_SITES ++ PE_NEXT_SITES
       ++ PE_CLOSE_SITES ++ PE_BCMP_SITES) =
  [Some (PCall PS___asan_stack_malloc_1 (1%bv : bv 5)); Some (PCall PS___asan_memcpy (1%bv : bv 5));
   Some (PCall PS___asan_memset (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_malloc (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_malloc (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_free (1%bv : bv 5));
   Some (PCall PS_pcap_source_open (1%bv : bv 5)); Some (PCall PS_pcap_source_open (1%bv : bv 5));
   Some (PCall PS_pcap_source_next (1%bv : bv 5)); Some (PCall PS_pcap_source_next (1%bv : bv 5));
   Some (PCall PS_pcap_source_next (1%bv : bv 5)); Some (PCall PS_pcap_source_next (1%bv : bv 5));
   Some (PCall PS_pcap_source_close (1%bv : bv 5)); Some (PCall PS_pcap_source_close (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_bcmp (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_bcmp (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_bcmp (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.
(* The three NULL-test slots, verbatim words of the listing: beqz s6,+8 (0x80948), beqz s3,+0x9f4
   to 0x81340 (0x8094c), beqz a0,+0x884 to 0x81340 (0x80abc). *)
Lemma PE_null_tests_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat (o / 4))) [PP_dup0; PP_dupnull; PP_K3] =
  [Some (PW 0x000b0463); Some (PW 0x1e098ae3); Some (PW 0x080502e3)].
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* ---- the entry function's context: what the call starts from ---- *)
Record ecx := mkECX {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model;
  c_p : Z;                   (* the caller's input buffer (a0)               *)
  c_pl : list byte;          (* its bytes                                    *)
  c_sp1 : Z;                 (* the realigned machine stack pointer, s1      *)
  c_E0 : env;                (* the atoms of the entry registers             *)
  c_M : Z;                   (* the base of the interceptors' meta region    *)
  c_T : Z                    (* the allocator budget the caller grants       *)
}.
Definition c_n (cx : ecx) : Z := Z.of_nat (length (c_pl cx)).

(* The frame this call owns on the side stack, the address of its flag, and its shadow. *)
Definition pF (cx : ecx) (fp : Z) : Z := frame_addr (c_ly cx) PE_CID fp.
Definition pFL (cx : ecx) (fp : Z) : Z := flag_addr (c_ly cx) PE_CID fp.
Definition pSH (cx : ecx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (pF cx fp).

(* The call chain this call hands to the functions it calls, as cgif's walk builds it
   (lib/A/ACf5.v:128-131): the caller's frame is on the chain when it fits under the
   layout's top. *)
Definition pch (cx : ecx) : list (Z * Z * Z) :=
  if spZ (c_regs cx) + 16 <? ly_top (c_ly cx)
  then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].

(* The harness's globals, the program-global ranges of the call's journal (W_journal.v ajournal_gx): g_file_len (object 4,
   8 bytes: sd s6,0x618(a1) 0x80938) and g_file (object 2, 8 bytes: sd s5,0(s2) 0x80930, sd s3,0(s2) 0x80970). On the pin
   they are PcapEntryA.G_HARNESS (pe_G_pin). *)
Definition pe_G : list (Z * Z) := [(pa_val (A_OBJ 4), 8); (pa_val (A_OBJ 2), 8)].

(* What the call may charge the allocator meter, at most, for an input of n bytes: the copy of
   the file (at most n bytes), two FILE blocks (one per pcap_source_open), the record buffer
   (at most 2040 bytes, 8 x one input byte, 0x80aa8) and six frees (each fclose frees twice,
   musl fclose 0x8e2b4 and 0x8e2bc, and the harness frees the buffer and the copy). *)
Definition pe_need (n : Z) : Z :=
  mo_malloc MT n + 2 * mo_malloc MT SRC_FILE_BLOCK + mo_malloc MT 2040 + 6 * mo_free MT.

(* What every phase may assume of the start: the pre-condition of PcapEntry.tfib_lib_pre_x
   at the listing's image, the realigned stack pointer, the atoms of the entry registers, the
   meter and its budget (the bridge sets c_T := XM_LIB n and needs pe_need n <= XM_LIB n), the side
   condition of the journal's global ranges (gx_ok SEGS B pe_G: image bytes outside as_owned_static; a Theorem Labs lane proves it for
   G_HARNESS on AF0m), that no byte of pe_G is a read-only byte, the AddrHashMap meta cell or errno (the callees'
   premises arodata_okP / asrc_meta_inv are stated at the harness's start memory, which the gx journal fixes only
   outside pe_G, and their kept clauses exclude errno; found by a Theorem Labs lane. On the pin G is .bss 0x5d3f40.. /
   0x5d3f60.., the RELRO window 0x992d0..0x9a528, the meta cell 0xa1108: disjoint; errno is B's TLS cell), and
   the call traces of the five calls of the wrappers for malloc and free, in the
   donor's form (cgif lib/A/ACf5.v:155-165): the malloc start only with the two malloc sites,
   the free start only with the three free sites. ACejSites.llvmf_site_in (a working branch)
   is the fact that discharges both, at pc_malloc_ra0 = 0x52e74, pc_free_ra0 = 0x52d14,
   BASE = 0x80738, raZ (c_regs cx) = RA_LLVMF and as_universe B = Tfib_universe, after
   call_trace0 is rewritten by ACejSites.unwind_of_chain_spine (the spine of pch cx is
   [0x80634] when the frame lies below the stack top, else []). *)
Definition pe_base (cx : ecx) : Prop :=
  afn_pre SEGS B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
  raZ (c_regs cx) = RA_LLVMF /\
  getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
  ((c_n cx = 0 /\ c_p cx = A_EMPTY) \/
   (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
  garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  frames (c_S cx) = [] /\
  st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
  asource_none SEGS KS (mrestrict (w_H (c_W cx)) (c_mem cx)) /\ as_ofl_head KS = AOFL_HEAD /\
  asrc_meta_inv SEGS KS (c_ly cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_M cx) /\
  c_sp1 cx = pe_sp1 (spZ (c_regs cx)) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
  bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
  mo_ok MT (c_S cx) (c_T cx) /\ pe_need (c_n cx) <= c_T cx /\
  gx_ok SEGS B pe_G /\
  (forall a, inG pe_G a -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a /\
     ~ (as_meta_mem KS <= a < as_meta_mem KS + 8) /\ ~ (as_errno B <= a < as_errno B + 4) /\
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) /\
     (* g_file / g_file_len (0x5d3f60 / 0x5d3f40) are written before an asource_none: no stream env byte in pe_G *)
     ~ asrc_env_addr KS a /\
     (* the harness's stores to g_file / g_file_len go through a region whose window bytes are writable_at *)
     (forall m, writable_at SEGS m a)) /\
  (* g_file_len (object 4) lies wholly below g_file (object 2): the two ranges of pe_G are disjoint, as the engine's
     st_ok pairwise_disjoint needs of the global regions (GI_K1 / GI_K2's p_glob). On the pin 0x5d3f48 <= 0x5d3f60. *)
  pa_val (A_OBJ 4) + 8 <= pa_val (A_OBJ 2) /\
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_MALLOC_SITES ->
     In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (pch cx)) (as_universe B)) /\
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_FREE_SITES ->
     In (call_trace0 (pc_free_ra0 (as_code B)) regsT (pch cx)) (as_universe B)).

(* The two trace conjuncts of pe_base follow from ACejSites.llvmf_site_in (a working branch,
   cgif ACf5.v:155-165 form) once the instance fixes the allocator's trace starts, the listing's
   base, the universe and the caller's return address. *)
Lemma pe_traces_of_sites : forall cx,
  raZ (c_regs cx) = RA_LLVMF -> BASE = pcap_text ->
  pc_malloc_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) -> pc_free_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) ->
  as_universe B = ACej.Tfib_universe ->
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_MALLOC_SITES ->
     In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (pch cx)) (as_universe B)) /\
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_FREE_SITES ->
     In (call_trace0 (pc_free_ra0 (as_code B)) regsT (pch cx)) (as_universe B)).
Proof.
  intros cx Hra HB Hm Hf HU. rewrite Hm, Hf, HU, HB.
  assert (Hsp : forall pc0 (regsT : bvmap 5 word), call_trace0 pc0 regsT (pch cx) =
    firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r])
      (raZ regsT :: (if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [(symaddr (Symbols.Asan.s_target_run + 0xcc)%Z)] else [])))).
  { intros pc0 regsT. unfold call_trace0, pch. rewrite ACejSites.unwind_of_chain_spine.
    destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); cbn [map fst snd]; [rewrite Hra|]; reflexivity. }
  split; intros regsT Hs; rewrite Hsp; apply ACejSites.llvmf_site_in;
    unfold PE_MALLOC_SITES, PE_FREE_SITES, pcap_text in *; cbn [In] in Hs; lia.
Qed.

(* ---- the memory of a phase ---- *)

(* The shadow bytes of the frame. *)
Definition pshadow (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (pSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* A byte of the frame. *)
Definition pfb (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  aview SEGS (w_H W3) (ms_mem ms3) (pF cx fp + off) = Some v.

(* An array of the frame, as a list of bytes. *)
Definition pfarr (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (off : Z) (l : list byte) : Prop :=
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (pF cx fp + off)
        (map (fun b : byte => bv_unsigned b) l).

(* The frame's header as the prologue writes it (0x80898..0x808a0): the magic, then the
   listing's objects 5 and 6 (PE_DESCR and PE_FNPC on the pin, PE_pin_values). *)
Definition pheader (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp) = Some PE_MAGIC /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + 8) = Some (pa_val (A_OBJ 5)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + 16) = Some (pa_val (A_OBJ 6)) /\
  (* the frame's last word holds its flag's address (aj_stack_malloc_atS's post at 0x80838); the epilogue loads it
     (0x81188) to give the frame back (0x8118c); found by a Theorem Labs lane *)
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + PE_FLAGPTR) = Some (pFL cx fp).

(* A spill slot of the machine frame: the body reads these back after every call. *)
Definition pslot (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v.

(* The slots every phase from the first pcap_source_next on keeps (PP_KD; written at 0x8090c / 0x80920, 0x80934,
   0x80954, 0x80ac4..0x80ad0 and 0x80aec), for a frame taken on the side stack (PS_FK holds F itself then).
   PS_GLEN holds the listing's auipc value 8 (0x5d3928 on the pin). PS_F0 (0x70(s1), written once at 0x8086c) is
   NOT here: no instruction of the function loads it (found by a Theorem Labs lane). *)
Definition pslots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  pslot cx W3 ms3 PS_PSP (pF cx fp + PO_PS) /\
  pslot cx W3 ms3 PS_GLEN (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_D (match c_pl cx with [] => 0 | d :: _ => bv_unsigned d end) /\
  pslot cx W3 ms3 PS_SH (pSH cx fp) /\
  pslot cx W3 ms3 PS_F (pF cx fp) /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\
  pslot cx W3 ms3 PS_TSP (pF cx fp + PO_TS).

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the
   entry stack pointer in s0, the shadow base in s11, gp and tp. *)
Definition pregs (cx : ecx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back
   (0x807d0..0x80800, 0x811dc..0x8120c): ra at sp0 - 8, then s0, s1, s2..s11. *)
Definition psaved (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* What every phase of the body carries: the pc (a listing offset), the registers, the saved
   registers, the frame's header and shadow, and the input block kept as the caller gave it. *)
Definition pe_body (cx : ecx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  pregs cx ms3 /\ psaved cx W3 ms3 /\ pheader cx fp W3 ms3 /\ pshadow cx fp W3 ms3 sh /\
  length sh = PE_NSH /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)).

(* ---- a phase ---- *)

(* The post-condition of the whole call, in the shape PcapEntry.tfib_lib_post_x asks: the
   machine is back at the caller's return address, the journal holds (W_journal.v's ajournal_gx
   over the harness's globals pe_G, XO = 0, OUT = []: the donor's journal outside g_file /
   g_file_len; its footprint is the sink token: musl's open-file list head changes while a FILE
   is open), a0 is 0, the blocks are a permutation of the caller's, the descriptors and the file
   system are the caller's, no stream is open, the meter is within the budget, and the caller's
   input bytes are unchanged. *)
Definition pe_post (cx : ecx) : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = mkCfg (mkst regs' (getr (c_regs cx) 1) mem' (seg_rom SEGS)) md' /\
    ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
    m_fds md' = m_fds (c_md cx) /\ m_fs md' = m_fs (c_md cx) /\
    asource_none SEGS KS (mrestrict (w_H W') mem') /\
    mo_le MT (c_S cx) S' (c_T cx) /\
    (forall i, 0 <= i < c_n cx ->
       aview SEGS (w_H W') mem' (c_p cx + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).

(* `pe_from POST GI` says: from any machine state that `GI` describes, with the class-1 frame
   taken at slot fp, the run reaches POST. A phase lemma has the shape
   `pe_from POST GI_next -> pe_from POST GI_self`; a loop phase is proved by induction on the
   number of turns left. *)
Definition pe_from (POST : ecx -> world SEGS -> config -> Prop)
  (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GI cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under `pe_base` to the same post-condition.
   The entry phase proves it from the phases that follow it. *)
Definition pe_start (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : ecx, pe_base cx ->
  SRr SEGS (c_W cx)
    (mkCfg (mkst (c_regs cx) (w64 (BASE + PP_entry)) (c_mem cx) (seg_rom SEGS)) (c_md cx))
    (POST cx).

End c.
End b.
End a.
(* The sink head is EXPLICIT on every exported statement that depends on it (a Theorem Labs lane, 21:57Z; see PcapEntry.v): the
   only global sink_head instance in this closure is the plain build's, so it must never be inferred. *)
Arguments pe_base {rc} SK {PI} B MT KS cx.
Arguments pe_post {fx rc} SK {PI} B MT KS cx _ _.
Arguments pe_from {rc} SK {PI} B MT KS POST GI.
Arguments pe_start {fx rc} SK {PI} B MT KS POST.

(* The meter budget conjunct of pe_base, pe_need (c_n cx) <= c_T cx, holds at the closing side's instantiation
   (OBLIGATIONS.md (sha256 781e8f81f164; internal record) row 11: tfib_lib_contract_x_all ... ameter_triv (fun _ => 0) (fun _ => 0) ..., so c_T = 0):
   under cgif's trivial meter every charge is 0, so pe_need is 0 for every input length. *)
Lemma pe_need_triv : forall n, pe_need YCbp.ameter_triv n = 0.
Proof. intros n. reflexivity. Qed.
Lemma pe_need_triv_budget : forall n, pe_need YCbp.ameter_triv n <= (fun _ : Z => 0) n.
Proof. intros n. rewrite pe_need_triv. cbv beta. lia. Qed.

(* The harness's global ranges on the pin: the listing's objects 4 and 2 are g_file_len and g_file (PE_pin_values). *)
Lemma pe_G_pin : [(pcap_obj 4, 8); (pcap_obj 2, 8)] = G_HARNESS.
Proof. reflexivity. Qed.
