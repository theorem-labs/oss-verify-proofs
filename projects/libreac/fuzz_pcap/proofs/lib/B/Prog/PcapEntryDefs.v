(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryDefs.v, with its module paths changed; 277 of its 342 lines of code are new or changed and 295 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* lib/B twin of lib/A/Prog/PcapEntryDefs.v for fuzz_pcap.asan-ubsan (a Theorem Labs lane 21:57Z convention: same path, file,
   definition and lemma names under ...lib.B). The walk of fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x80818,
   listing offset AF_LLVMFuzzerTestOneInput = 0x90 of lib/B/Prog/PcapList.v, pcap_text = 0x80788) on the asan-ubsan
   build of libreac v1.9.0, cut into phases: the data every phase shares. The statement the phases prove together is
   lib/B/Prog/PcapEntry.v's instance tfib_lib_contract_x_all_B of lib/A's image-generic contract.

   Every number is read from the pin fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...; symbols from its
   unstripped twin, capstone 5.0.7 disassembly; the dump with listing offsets is
   llvmf-au.dis (sha256 be945029c797; internal record), the asan / asan-ubsan map entry-au-map.md (sha256 3f4d6f638159; internal record)). The
   comment beside a number names the instruction it comes from, by its address. No number is an asan value shifted:
   this function is DIFFERENT CODE on this image (530 instructions against 779: rd32 is a call of its own here, six
   sites, where the asan build inlines it; another frame, other spill slots, other registers; 18 UBSan guards that
   branch to the one `unimp` at 0x8103c).

   The entry function keeps two frames at once:
   - a machine-stack frame of 256 bytes (`addi sp,sp,-0x100` 0x80818; `sd zero,0(sp)` 0x8081c probes its lowest
     word). ra and s0..s11 are saved at sp0-8 .. sp0-104 (0x80820..0x80850), s0 := sp0 (`addi s0,sp,0x100` 0x80854),
     the stack is realigned to 32 bytes (`andi sp,sp,-0x20` 0x80858) and s1 := that stack pointer (`mv s1,sp`
     0x8085c). s1 is the base of the spill slots, and every call of the body is made with sp = s1;
   - a frame on the side stack for frames, class 1 (128-byte slots). When the use-after-return flag (the word at
     0xa17c0, object 16, through its GOT word 0x99750, object 0: `auipc a2,0x19` 0x80868, `ld a2,-0x118(a2)` 0x8086c,
     `lw a2,0(a2)` 0x80874) is not zero, `__asan_stack_malloc_1(0x80)` (a0 := 0x80 at 0x80884, `jal` 0x80888, return
     address 0x8088c) gives the frame F in a0; s7 := a0 (0x8088c), s10 := s7 (0x80898). When the flag is 0 or the
     call returns 0, the body takes F on the machine stack instead (0x808a0..0x808b8: s10 := (sp - 0x80) & -32, a
     4096-byte probe, sp := s10). F stays in s10 until 0x80b1c; it is spilled at 0x90(s1) (0x808bc) and 0x20(s1)
     (0x80a28), and the side-stack result s7 at 0x10(s1) (0x80a20). The 16 shadow bytes of F start at
     shadow_of_addr SHADOW_OFF F, which s9 holds (`srli a3,s10,3` 0x808cc, `add s9,a3,s4` 0x808f8; spilled at
     0x28(s1), 0x80a24) with s4 the shadow base (`ld s4,0(a1)` 0x80878 from the cell 0xa17b8, object 15, through its
     GOT word 0x996f8, object 1: `auipc a1,0x19` 0x80864, `ld a1,-0x16c(a1)` 0x80870). Unlike the asan build, the
     shadow base does NOT stay in s11: s4 holds it until 0x809c4 (then &ps), and it is spilled at 0x48(s1) (0x80944)
     for the record checks' shadow tests (0x80c1c, 0x80c48, 0x80ce4); s11 is a data register of the record loop.

   One phase = one file; the cut between two phases is semantic (`pe_from` below), never a
   symbolic state, so that no phase has to compute another phase's state. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
(* The plain functional model of the reader and of the harness's output, required without Import
   (their own imports include lib/Lib): every use below is fully qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
(* The journal with program-global ranges (W_journal.v, by path from fuzz_reply's working branch 6328acea202). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
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
   walk that strings them (by induction on its fuel). The contract's post states
   `ll_out l = PWalk.OUT pl`; the bridge from pe_post takes l := LL 0 (m_fs md) (PWalk.OUT pl) and
   meets the shape's `wr ch_stderr (PWalk.OUT pl) _` with this lemma. (Image-free; restated here so
   that the lib/B closure does not import lib/A's PcapEntryDefs, whose names this file shares.) *)
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

Definition PE_MFRAME : Z := 256.          (* addi sp,sp,-0x100              0x80818 *)
(* The realigned stack pointer that s1 holds for the whole body. *)
Definition pe_sp1 (sp0 : Z) : Z := 32 * ((sp0 - PE_MFRAME) / 32).
                                          (* andi sp,sp,-0x20 0x80858; mv s1,sp 0x8085c *)

(* ---- the frame on the side stack ---- *)

Definition PE_CID : Z := 1.               (* jal __asan_stack_malloc_1      0x80888 *)
Definition PE_FREQ : Z := 128.            (* addi a0,zero,0x80 (the request) 0x80884 *)
Definition PE_FRAME : Z := 128.           (* the slot, fs_frame_bytes 1 *)
Definition PE_NSH : nat := 16%nat.        (* its shadow bytes, 0(s9)..0xf(s9) *)
(* The frame's header, written before any check: the live-frame magic, the address of the
   frame's description string (object 5: "2 32 24 5 ps:90 96 8 6 ts:131", read at 0x136f4 on this
   pin) and the function's own address (object 6). *)
Definition PE_MAGIC : Z := 0x41b58ab3.    (* lui a0,0x41b59 0x808c0; addiw a0,a0,-0x54d 0x808dc; sd a0,0(s10) 0x808e8 *)
Definition PE_DESCR : Z := Eval compute in (Symbols.AsanUbsan.Sec.s_rodata + 0x3414)%Z.  (* auipc a1,0xfff93 0x808c4; addi a1,a1,-0x1d0 0x808e0; sd a1,8(s10) 0x808ec *)
Definition PE_FNPC : Z := Eval compute in Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput.  (* auipc a2,0 0x808c8; addi a2,a2,-0xb0 0x808e4; sd a2,0x10(s10) 0x808f0 *)
(* What the epilogue writes when it gives the frame back: the retired-frame magic at F, and,
   for a side-stack frame, 0 through the flag pointer the slot keeps in its last word. *)
Definition PE_RETIRED : Z := 0x45e0360e.  (* lui a0,0x45e03 0x80ec4; addiw a0,a0,0x60e 0x80ec8; sd a0,0(s10) 0x80ecc *)
Definition PE_FLAGPTR : Z := 120.         (* ld a0,0x78(s7) 0x80f18; sb zero,0(a0) 0x80f1c *)

(* ---- the frame's objects ---- *)

(* The description string's offsets: ps at 32 (24 bytes), ts at 96 (8 bytes). *)
Definition PO_PS : Z := 32.               (* struct pcap_source ps: addi s4,s10,0x20 0x809c4 *)
Definition PO_PS_LEN : Z := 24.           (* memset(&ps,0xa5,24): addi a2,zero,0x18 0x809f0 *)
Definition PE_PS_FILL : Z := 165.         (* addi a1,zero,0xa5 0x809ec; __asan_memset 0x809fc *)
Definition PO_TS : Z := 96.               (* uint64_t ts: ld a0,0x20(s1) 0x80ad4 (F); addi a3,a0,0x60 0x80ad8 *)
(* ts := ~0 before the walk (sd a0,0(a3) 0x80ae8) and after each record (sd a0,0(a3) 0x80d98). *)
Definition PE_TS_NONE : Z := 2 ^ 64 - 1.  (* addi a0,zero,-1 0x80ae4, 0x80d90 *)

(* ---- the frame's shadow ---- *)

(* The 16 shadow bytes as the prologue leaves them (0x808fc..0x8093c, the values in a6 = 0xf1,
   a5 = 0xf8, a4 = 0xf2, a0 = 0xf3 from 0x808d0..0x808f4): 0xf1 the left redzone (F+0..31),
   0xf8 `ps` out of scope (F+32..55), 0xf2 between the objects (F+56..95), 0xf8 `ts` out of scope
   (F+96..103), 0xf3 the right redzone (F+104..127). *)
Definition PSH_entry : list Z :=
  [241;241;241;241; 248;248;248; 242; 242;242;242;242; 248; 243;243;243].

Definition psh_set (sh : list Z) (lo n : nat) (v : Z) : list Z :=
  firstn lo sh ++ repeat v n ++ skipn (lo + n) sh.
(* `ps` in scope: sb zero,4(s9) / 5(s9) / 6(s9) 0x809e0..0x809e8 (before __asan_memset). *)
Definition PSH_ps : list Z := psh_set PSH_entry 4 3 0.
(* `ts` in scope: sb zero,0xc(a0) 0x80ae0 with a0 = the shadow of F (ld a0,0x28(s1) 0x80adc), after the record
   buffer is allocated. *)
Definition PSH_ts : list Z := psh_set PSH_ps 12 1 0.
(* `ts` out of scope again: sb a0,0xc(s9) with a0 = 0xf8 (0x80ea0) and s9 reloaded (0x80ea4), 0x80ea8 (end of the
   body). *)
Definition PSH_tsout : list Z := psh_set PSH_ts 12 1 248.
(* `ps` out of scope again: sb a0,4/5/6(s9) with a0 = 0xf8 (0x80eac), 0x80eb0..0x80eb8, reached from the
   end of the body (PSH_tsout) and from the refused open (PSH_ps); both give PSH_entry back. *)
Definition PSH_out (sh : list Z) : list Z := psh_set sh 4 3 248.
(* The frame given back: every shadow byte 0xf5 for a side-stack frame (a0 = -0xb 0x80ed4,
   0x80ed8..0x80f14), every shadow byte 0 for a frame on the machine stack (0x80f24..0x80f60). *)
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

(* This image's slots (every store and every load at s1+off in the function, entry-au-map.md (sha256 3f4d6f638159; internal record)).
   lib/A's PS_GLEN and PS_PSP have no counterpart: this build keeps the auipc value 8 in s8 (`auipc s8,0x553`
   0x809a8, never spilled) and &ps in s4 (`addi s4,s10,0x20` 0x809c4, callee-saved). PS_SHB, PS_BUF, PS_CALLS, PS_N
   and PS_CAP are new: the asan build keeps the shadow base, buf, calls, n and cap in registers (s11, s6, s9, a2,
   s5). *)
Definition PS_FK : Z := 16.       (* s7 = __asan_stack_malloc_1's result (0 for a machine frame):
                                     sd s7,0x10(s1) 0x80a20; reloaded 0x80ebc *)
Definition PS_D : Z := 24.        (* the first input byte d (cap = 8 d), 0 for an empty input:
                                     sd a0,0x18(s1) 0x8096c / sd zero,0x18(s1) 0x8097c; reloaded 0x80ab4, 0x80ff8 *)
Definition PS_F : Z := 32.        (* s10 = F:                    sd s10,0x20(s1) 0x80a28; reloaded 0x80ad4, 0x80ec0 *)
Definition PS_SH : Z := 40.       (* s9 = the shadow of F:       sd s9,0x28(s1) 0x80a24; reloaded 0x80a94, 0x80adc, 0x80ea4 *)
Definition PS_VMASK : Z := 48.    (* 0xf00, the high byte of the VLAN-id mask (addi a1,zero,0xf 0x80b24; slli a1,a1,8
                                     0x80b2c): sd a1,0x30(s1) 0x80b30; reloaded 0x80d18 *)
Definition PS_BUF12 : Z := 56.    (* buf + 12 (addi s3,s3,0xc 0x80b10): sd s3,0x38(s1) 0x80b14; reloaded 0x80cc0 *)
Definition PS_USEC : Z := 64.     (* 10^6 * 2^32 (lui a2,0x3d09 0x80b28; slli a2,a2,0x1a 0x80b34):
                                     sd a2,0x40(s1) 0x80b38; reloaded 0x80d70 *)
Definition PS_SHB : Z := 72.      (* the shadow base SHADOW_OFF (s4, ld s4,0(a1) 0x80878): sd s4,0x48(s1) 0x80944;
                                     reloaded 0x80c1c, 0x80c48, 0x80ce4 *)
Definition PS_FIRST : Z := 80.    (* the reader's first answer: sd a0,0x50(s1) 0x80b64; reloaded 0x80dc0 *)
Definition PS_TSP : Z := 88.      (* &ts = F + PO_TS: sd a3,0x58(s1) 0x80afc; reloaded 0x80d48, 0x80d94 *)
Definition PS_BUF : Z := 96.      (* buf: sd a0,0x60(s1) 0x80acc; reloaded 0x80af0, 0x80c8c, 0x80c9c, 0x80d34, 0x80db0,
                                     0x80e58, 0x80e78, 0x80e90 *)
Definition PS_CALLS : Z := 104.   (* calls: sd zero,0x68(s1) 0x80b0c, sd a0,0x68(s1) 0x80b8c; reloaded 0x80b4c, 0x80b58,
                                     0x80b84 *)
Definition PS_N : Z := 112.       (* n: sd a0,0x70(s1) 0x80b3c, sd a1,0x70(s1) 0x80dc8, sd a0,0x70(s1) 0x80e08; reloaded
                                     0x80b54, 0x80b6c, 0x80c80, 0x80d2c, 0x80d3c, 0x80e14, 0x80e28 *)
Definition PS_CAP : Z := 120.     (* cap = 8 d (slli a0,a1,3 0x80ab8): sd a0,0x78(s1) 0x80abc; reloaded 0x80af8,
                                     0x80b68, 0x80bb8, 0x80db4, 0x80e5c, 0x80e7c, 0x80ff0 *)
Definition PS_F0 : Z := 144.      (* F, first copy: sd s10,0x90(s1) 0x808bc (never reloaded) *)
(* The harness's two globals and the path literal, and the values the frame's header holds, as the pin gives them and
   as the listing names them (PcapAddr). *)
Definition PE_G_FILE : Z := Eval compute in Symbols.AsanUbsan.s_g_file.  (* object 2: auipc a0,0x553 0x80984; addi s3,a0,0x4dc 0x80988 *)
Definition PE_G_FILE_LEN : Z := Eval compute in Symbols.AsanUbsan.s_g_file_len.  (* object 4; hi 8 + 0x498: auipc s8,0x553 0x809a8; sd s6,0x498(s8) 0x809ac *)
(* g_file_len's low part: the code reaches g_file_len as hi 8 + lo, hi 8 the value of `auipc s8` at
   LLVMFuzzerTestOneInput + 0x190 (0x809a8) and lo the signed 12-bit rest (0x498 on the pin), both from Symbols.v.
   PE_GLEN_LO8 = lo + 8 ends the 8-byte object. They elaborate to the numerals. *)
Abbreviation PE_GLEN_LO := (symaddr ((Symbols.AsanUbsan.s_g_file_len - (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x190)) -
  (Symbols.AsanUbsan.s_g_file_len - (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x190) + 0x800) / 4096 * 4096)%Z) (only parsing).
Abbreviation PE_GLEN_LO8 := (symaddr ((Symbols.AsanUbsan.s_g_file_len - (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x190)) -
  (Symbols.AsanUbsan.s_g_file_len - (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x190) + 0x800) / 4096 * 4096 + 8)%Z) (only parsing).
Definition PE_PATH : Z := Eval compute in (Symbols.AsanUbsan.Sec.s_rodata + 0x10a20)%Z.  (* .rodata + 0x10a20, as .str names several objects; object 3, "<fuzz-input>": auipc a0,0xfffa0 0x80a00 / 0x80e40;
                                             addi a1,a0,0x300 0x80a04 / addi a1,a0,-0x140 0x80e44 *)
Lemma PE_pin_values :
  pcap_obj 2 = PE_G_FILE /\ pcap_obj 3 = PE_PATH /\ pcap_obj 4 = PE_G_FILE_LEN /\
  pcap_hi 8 + PE_GLEN_LO = PE_G_FILE_LEN /\ pcap_obj 5 = PE_DESCR /\ pcap_obj 6 = PE_FNPC /\
  pcap_obj 15 = (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address) /\ pcap_obj 16 = (symaddr Symbols.AsanUbsan.s___asan_option_detect_stack_use_after_return) /\ pcap_obj 0 = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xb8)%Z) /\ pcap_obj 1 = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z).
Proof. repeat split; reflexivity. Qed.

(* ---- the pcs of the phase cuts, as offsets in the listing (address - 0x80788) ---- *)

Definition PP_entry : Z := Eval compute in (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x80818, the first slot                                  *)
Definition PP_early : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x128) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x80940, bnez a1 to the return of an input of 2^26+ bytes (srli a1,s2,0x1a 0x8090c) *)
Definition PP_K1 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x809b8, malloc (0x809b4) of the copy of the file returned  *)
Definition PP_dup0 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x809bc, beqz s6: an empty copy (size - 1 = 0) skips the NULL test *)
Definition PP_dupnull : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x809c0, beqz s2 to PP_abort: fuzz_dup's abort when malloc
                                       of size - 1 >= 1 bytes returned NULL *)
Definition PP_K2 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80a10, pcap_source_open (0x80a0c) returned               *)
Definition PP_KM : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x224) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80a3c, NEW: rd32 (0x80a38) of the magic, rd32(file, 0), returned; reached only
                                       when g_file_len >= 4 (0x80a2c) *)
Definition PP_ref : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x268) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80a80, open refused or accepted: beqz s3 to the accept arm 0x80a9c *)
Definition PP_K3 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80acc, malloc (0x80ac8) of the record buffer returned      *)
Definition PP_bufnull : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x80ad0, NEW constant (no phase): beqz a0 to PP_abort, the harness's
                                       `if (!buf) abort();` (the asan build tests at its PP_K3 slot itself) *)
Definition PP_KD : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2ec) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80b04, the first pcap_source_next (0x80b00) returned     *)
Definition PP_K4 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x328) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80b40, the head of the record loop (back edge 0x80dcc)   *)
Definition PP_KR : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x378) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80b90, the head of the harness's skip loop (back edge 0x80bd0) *)
Definition PP_KRI : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x390) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80ba8, NEW: rd32 (0x80ba4) of incl, rd32(file + e + 8, swapped), returned *)
Definition PP_KO : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x3e4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80bfc, NEW: rd32 (0x80bf8) of orig_len, rd32(file + at + 12, swapped), returned;
                                       this slot is `bne s6,a0` to PP_abort *)
Definition PP_KT1 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x544) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80d5c, NEW: rd32 (0x80d58) of the seconds, rd32(file + at, swapped), returned *)
Definition PP_KT2 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x568) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80d80, NEW: rd32 (0x80d7c) of the microseconds, rd32(file + at + 4, swapped),
                                       returned *)
Definition PP_KL2 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5a4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80dbc, the loop's pcap_source_next (0x80db8) returned    *)
Definition PP_K5 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5f4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80e0c, the record loop is done (from PP_KD by 0x80b04 -> 0x80e04, from PP_KL2 by
                                       j 0x80dd0) *)
Definition PP_KW : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x798) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80fb0, the head of the end-of-walk check loop (back edge 0x81014) *)
Definition PP_KWL : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x7cc) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80fe4, NEW: rd32 (0x80fe0) of len, rd32(file + e + 8, swapped), returned *)
Definition PP_K6 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x620) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80e38, pcap_source_close (0x80e34) returned              *)
Definition PP_K7 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80e50, the second pcap_source_open (0x80e4c) returned    *)
Definition PP_K8 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x650) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80e68, pcap_source_next (0x80e64) returned               *)
Definition PP_K9 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x65c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x80e74, the second pcap_source_close (0x80e70) returned   *)
Definition PP_K10 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x670) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80e88, pcap_source_next of the closed reader (0x80e84) returned *)
Definition PP_K11 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80e98, the record buffer is freed (free 0x80e94)         *)
Definition PP_K12 : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80ea0, the copy of the file is freed (free 0x80e9c)      *)
Definition PP_K12r : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x694) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x80eac, `ps` out of scope; the refused open lands here (j 0x80a98) *)
Definition PP_leave : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x6ac) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x80ec4, the frame is given back; the early return lands here *)
Definition PP_ret : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x78c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x80fa4, the `ret`                                        *)
Definition PP_abort : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x81c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81034, __asan_handle_no_return, then abort 0x81038       *)
(* The UBSan trap: the function's one `unimp` (word 0xc0001073; -fsanitize-trap=all merges every check of the
   function into it). No guard falls through into it (it follows `jal abort`), and no run reaches it. *)
Definition PE_TRAP : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x824) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x8103c, unimp                                            *)
(* The 18 guards that branch to PE_TRAP, as (listing offset of the branch, its displacement), with the condition
   under which the trap is taken (wrap(x + k): x + k > 2^64 - 1; the C line, fuzz_pcap.c / fuzz.h at d16f3f4e; the
   check kind is pointer-overflow for every one, from the code pattern) and the fact a walk refutes it with
   (a Theorem Labs lane's pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record) (b), G1..G4'):
     0x1cc  0x80954  bgeu a0(=1),s5(=data+1)   data + 1 <=u 1             fuzz.h:41 in->p++       G3: p >= 4096, p + n < 2^64 (pe_base)
     0x20c  0x80994  bltu a0(=p+n),s5(=p)      p + n <u p                 fuzz.h:62 in->p += n    G4: AR's block law, p + n <= alloc_ceiling
     0x21c  0x809a4  beqz a0 (snez p ^ seqz p+n) (p <> 0) = (p + n = 0)   fuzz.h:62               G3
     0x3f8  0x80b80  beqz s2(=file)            file = NULL                fuzz_pcap.c:157         G1: 4096 <= b (allocator post)
     0x408  0x80b90  bltu s7(=~file),s10(=at)  wrap(file + at)            fuzz_pcap.c:157         G4': b + |F| < 2^47, at <= |F|
     0x410  0x80b98  bgeu s3(=file+at),s5(=-8) wrap(file + at + 8)        fuzz_pcap.c:157         G2: at + 16 <= |F| (GI_KR)
     0x454  0x80bdc  bltu a0(=-17),s3          wrap(file + at + 16)       fuzz_pcap.c:162         G2
     0x488  0x80c10  bltu a0(=-13),s6(=rec)    wrap(rec + 12)             fuzz_pcap.c:173         G2: at + 16 + incl <= |F|
     0x4b4  0x80c3c  bltu a0(=-14),s6          wrap(rec + 13)             fuzz_pcap.c:173         G2
     0x51c  0x80ca4  bltu a1(=-13),a0(=buf)    wrap(buf + 12)             fuzz_pcap.c:193         G2: buf + bn below the ceiling
     0x524  0x80cac  bltu a0(=-17),s6          wrap(rec + 16)             fuzz_pcap.c:193         G2
     0x548  0x80cd0  bltu a0(=-15),s6          wrap(rec + 14)             fuzz_pcap.c:194         G2
     0x550  0x80cd8  bltu a0(=-16),s6          wrap(rec + 15)             fuzz_pcap.c:194         G2
     0x5d8  0x80d60  bltu a1(=-5),s3(=file+at) wrap(file + at + 4)        fuzz_pcap.c:212         G2
     0x838  0x80fc0  bltu a0(=file+e),s2       file + e <u file           fuzz_pcap.c:236         G4: e <= |F| (GI_KW), b + |F| below the ceiling
     0x844  0x80fcc  beqz a1 (snez file ^ seqz file+e) (file <> 0) = (file + e = 0)   fuzz_pcap.c:236   G1
     0x848  0x80fd0  beqz s2(=file)            file = NULL                fuzz_pcap.c:236         G1
     0x84c  0x80fd4  bltu s7(=-9),a0(=file+e)  wrap(file + e + 8)         fuzz_pcap.c:236         G2: e + 16 <= |F| (0x80fb8) *)
Definition PE_GUARDS : list (Z * Z) :=
  [(0x1cc, 0x6e8); (0x20c, 0x6a8); (0x21c, 0x698); (0x3f8, 0x4bc); (0x408, 0x4ac); (0x410, 0x4a4);
   (0x454, 0x460); (0x488, 0x42c); (0x4b4, 0x400); (0x51c, 0x398); (0x524, 0x390); (0x548, 0x36c);
   (0x550, 0x364); (0x5d8, 0x2dc); (0x838, 0x7c); (0x844, 0x70); (0x848, 0x6c); (0x84c, 0x68)].
Lemma PE_guards_to_trap : map (fun g => fst g + snd g) PE_GUARDS = repeat PE_TRAP 18.
Proof. reflexivity. Qed.
(* The guards' words and the trap word, verbatim slots of the listing. *)
Lemma PE_guards_listed :
  map (fun g => nth_error pcap_listing (Z.to_nat (fst g / 4))) PE_GUARDS =
  [Some (PW 0x6f557463); Some (PW 0x6b556463); Some (PW 0x68050c63); Some (PW 0x4a090e63);
   Some (PW 0x4babe663); Some (PW 0x4b59f263); Some (PW 0x47356063); Some (PW 0x43656663);
   Some (PW 0x41656063); Some (PW 0x38a5ec63); Some (PW 0x39656863); Some (PW 0x37656663);
   Some (PW 0x37656263); Some (PW 0x2d35ee63); Some (PW 0x07256e63); Some (PW 0x06058863);
   Some (PW 0x06090663); Some (PW 0x06abe463)].
Proof. vm_compute. reflexivity. Qed.
Lemma PE_trap_listed : nth_error pcap_listing (Z.to_nat (PE_TRAP / 4)) = Some (PW 0xc0001073).
Proof. vm_compute. reflexivity. Qed.

(* The walks (a Theorem Labs lane's stage list, slot_lscps.v (sha256 15a609daf420; internal record) at 6954866e3be, at this image's pcs; M is new, and the rd32 cuts
   PP_KRI, PP_KO, PP_KT1, PP_KT2, PP_KWL split Walk and W):
     entry   the first slot: ENTRY (size < 2^26) or EARLY, no instruction
     E       PP_entry -> __asan_stack_malloc_1 0x80888 -> guards 0x80954, 0x80994, 0x809a4 -> malloc 0x809b4 -> PP_K1
     EARLY   PP_entry -> __asan_stack_malloc_1 0x80888 -> PP_early -> PP_leave -> PP_ret
     A       PP_K1 -> __asan_memcpy 0x809d8, __asan_memset 0x809fc -> pcap_source_open 0x80a0c -> PP_K2
     M       PP_K2 (g_file_len >= 4) -> rd32 0x80a38 -> PP_KM
     B_acc   PP_KM (s3 = 0) -> PP_ref -> malloc 0x80ac8 -> PP_K3
     B_ref   PP_K2 (g_file_len < 4) or PP_KM (s3 = -1) -> PP_ref -> free 0x80a90 -> PP_K12r
     C       PP_K3 -> pcap_source_next 0x80b00 -> PP_KD
     Walk    PP_KD -> PP_K5, through PP_K4, PP_KR, PP_KRI (rd32 0x80ba4), PP_KO (rd32 0x80bf8), the bcmp wrapper
             0x80c94 / 0x80cc4 / 0x80d40, PP_KT1 (rd32 0x80d58), PP_KT2 (rd32 0x80d7c) and pcap_source_next 0x80db8
             (PP_KL2)
     W       PP_K5 -> the check loop at PP_KW, PP_KWL (rd32 0x80fe0) -> pcap_source_close 0x80e34 -> PP_K6
     R1      PP_K6 -> pcap_source_open 0x80e4c -> PP_K7
     R2      PP_K7 -> pcap_source_next 0x80e64 -> PP_K8
     R3      PP_K8 -> pcap_source_close 0x80e70 -> PP_K9
     R4      PP_K9 -> pcap_source_next 0x80e84 -> PP_K10
     R5      PP_K10 -> free 0x80e94 -> PP_K11
     R6      PP_K11 -> free 0x80e9c -> PP_K12
     R7      PP_K12 -> PP_K12r -> PP_leave -> PP_ret
     BT      PP_K12r -> PP_leave -> PP_ret
   Every abort() check branches to PP_abort; every shadow check that fails branches to a call
   of __asan_report_load1 (0x80e00, 0x8104c, 0x81050, 0x81054, 0x8105c); every UBSan guard branches to PE_TRAP.
   The ASan allocator may return NULL (allocator_may_return_null = 1 in this image), so the two
   NULL arms (PP_dupnull, PP_bufnull) are branches of the walk like any other. They are closed only by
   the allocator rule's post, `4096 <= res` (YC5d.v:72, amalloc04_rule), whose room premises the
   call carries (st_nev S + EV_LIB <= EV_MAX, blocks_bytes S + LIVE_LIB <= LIVE_MAX, each request
   < MALLOC_MAX), never by an assumption that malloc does not fail. An empty copy (PP_dup0) takes
   no NULL test.

   The side-stack frame. The flag is read at 0x80874 (object 16 through object 0, PcapPaLib.v pal_got_uar /
   pal_uar_cell); AR_const_law (YG0d.v:465) gives it the value 1, so the flag = 0 arm is refuted. Every cut below
   carries the granted arm only (pe_from: frames S3 = [(PE_CID, fp)]): the walk of `entry` refutes the fallback to a
   machine frame (__asan_stack_malloc_1 returns 0) by discharging astack_malloc_realizes 1's two premises (YG0d.v:285)
   at 0x80888: count_cid 1 (frames S) < fs_frames 1 from pe_base's frames (c_S cx) = [], and
   apath (stack_malloc 1 S) [] (PFake 1 pos, S') from stack_malloc_progressP (YCbq.v:803) under the same count.

   The rd32 sites (lib/B/Prog/Rd32.v trd32_specX is the callee contract: a0 = p, a1 = the swap flag, the four bytes
   inside a live block (b, n) of the caller's state, b <= p, p + 4 <= b + n). At each site the block is the copy
   (g_file, g_file_len) = (b, |F|), in the cut's block list from PP_K1 to PP_K11, and the bound is:
     0x80a38 (PP_KM)   p = file             a1 = 0             4 <= |F| (0x80a2c)
     0x80ba4 (PP_KRI)  p = file + e + 8     a1 = ps.swapped    e + 16 <= |F| (0x80b7c on the first turn, 0x80bd0 after)
     0x80bf8 (PP_KO)   p = file + at + 12   a1 = ps.swapped    at + 16 + incl <= |F| (0x80be8)
     0x80d58 (PP_KT1)  p = file + at        a1 = ps.swapped    at + 16 + incl <= |F|
     0x80d7c (PP_KT2)  p = file + at + 4    a1 = ps.swapped    at + 16 + incl <= |F|
     0x80fe0 (PP_KWL)  p = file + e + 8     a1 = ps.swapped    e + 16 <= |F| (0x80fb8)
   ps.swapped is the 32-bit field at ps + 8 loaded by `lw a1,8(s4)` (0x80b9c, 0x80bec, 0x80d50, 0x80d64, 0x80fd8), so
   a1 = pcap_sw F; the value comes back sign-extended from bit 31 (trd32_val, `bv_swrap 32`). rd_u32 is not called
   by this function: its four sites are pcap_source_next's (PE_RDU32_SITES).

   Stack room at a call of the body. sp = s1 >= sp0 - 272 (sp0 - 400 with a machine-stack frame),
   and s1 mod 32 = 0. pe_base's afn_pre gives astk_ok LLVMF_STK ly sp0: ly_stk_lo + 32768 <= sp0
   and ly_bot + 32768 < sp0 + ASTACK with ly_bot = ly_top - kStackSpan (YG0f.v:36, :63) and
   ASTACK = 16384 (YG0d.v:18), so ly_top - sp0 < 2^23 - 16384. A callee of window STK at s1 needs
   ly_stk_lo + STK <= s1 and ly_top - s1 < 2^23 + 16384 - STK; both follow for STK <= 32368
   (32768 - 400). That covers pcap_source_open's window (at least 112 + 96 + AFMEMOPEN_STK =
   18832), pcap_source_close's (at least 32 + PFCLOSE_STK = 16560), pcap_source_next's (at least
   272 + 64 + AFREAD_STK = 8528), rd32's 16, the bcmp wrapper's 2 * ESTACK, and the allocator rules'
   ASTACK - o <= LLVMF_STK (YC5d.v:60; o >= -400). *)

(* ---- the call sites, as listing offsets of their return addresses ---- *)

(* The wrappers for malloc and free that the body calls itself; a callee contract of the
   allocator asks for the call trace at each. *)
Definition PE_MALLOC_SITES : list Z := [0x230; 0x344].        (* 0x809b8, 0x80acc *)
Definition PE_FREE_SITES : list Z := [0x30c; 0x710; 0x718].   (* 0x80a94, 0x80e98, 0x80ea0 *)
Definition PE_SITES : list Z := PE_MALLOC_SITES ++ PE_FREE_SITES.
(* The program functions the body calls, and the other runtime entries. *)
Definition PE_OPEN_SITES : list Z := [0x288; 0x6c8].                (* 0x80a10, 0x80e50 *)
Definition PE_NEXT_SITES : list Z := [0x37c; 0x634; 0x6e0; 0x700].  (* 0x80b04, 0x80dbc, 0x80e68, 0x80e88 *)
Definition PE_CLOSE_SITES : list Z := [0x6b0; 0x6ec].               (* 0x80e38, 0x80e74 *)
Definition PE_BCMP_SITES : list Z := [0x510; 0x540; 0x5bc].         (* 0x80c98, 0x80cc8, 0x80d44 *)
(* NEW: the harness's rd32, a function of its own on this image (0x81060, AF_rd32 = 0x8d8), and libreac's rd_u32
   (0x81c38, AF_rd_u32 = 0x14b0), which only pcap_source_next calls (0x81788, 0x817a8, 0x817c8, 0x817f0): listing
   offsets of the return addresses, like the others. *)
Definition PE_RD32_SITES : list Z := [0x2b4; 0x420; 0x474; 0x5d4; 0x5f8; 0x85c].
                                     (* 0x80a3c, 0x80ba8, 0x80bfc, 0x80d5c, 0x80d80, 0x80fe4 *)
Definition PE_RDU32_SITES : list Z := [(symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x1d4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z); (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x1f4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z); (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x214) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z); (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x23c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z)].
                                     (* 0x8178c, 0x817ac, 0x817cc, 0x817f4, inside pcap_source_next *)
Definition PE_SM_SITE : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x74) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.                                 (* 0x8088c *)
Definition PE_MEMCPY_SITE : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1c4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.                             (* 0x809dc *)
Definition PE_MEMSET_SITE : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1e8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.                             (* 0x80a00 *)
(* The allocator calls the callees make on the body's behalf (absolute addresses: they are
   musl's, outside the listing): the malloc of fmemopen, under each pcap_source_open, and the
   free(NULL) and free of fclose, under pcap_source_close and the failure arms of
   pcap_source_open. *)
Definition PE_FMEMOPEN_MALLOC_RA : Z := Eval compute in (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z.  (* jal __wrap_malloc 0x8e7d4 (fmemopen 0x8e73c) *)
Definition PE_FCLOSE_FREE_RAS : list Z :=
  Eval compute in [(Symbols.AsanUbsan.s_fclose + 0xa4)%Z; (Symbols.AsanUbsan.s_fclose + 0xac)%Z].  (* jal __wrap_free 0x8e180, 0x8e188 (fclose 0x8e0e0) *)

(* The cut pcs and the return addresses, as addresses of the pin, and the call each slot holds
   in the listing: checked once here against PcapAddr.pcap_text and PcapList.pcap_listing. *)
Lemma PP_addrs :
  map (fun o => pcap_text + o)
    [PP_entry; PP_early; PP_K1; PP_dup0; PP_dupnull; PP_K2; PP_KM; PP_ref; PP_K3; PP_bufnull; PP_KD; PP_K4;
     PP_KR; PP_KRI; PP_KO; PP_KT1; PP_KT2; PP_KL2; PP_K5; PP_KW; PP_KWL; PP_K6; PP_K7; PP_K8; PP_K9; PP_K10;
     PP_K11; PP_K12; PP_K12r; PP_leave; PP_ret; PP_abort; PE_TRAP] =
    [(symaddr Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x128)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a4)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x224)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x268)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2ec)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x328)%Z);
     (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x378)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x390)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x3e4)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x544)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x568)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5a4)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5f4)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x798)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x7cc)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x620)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x650)%Z);
     (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x65c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x670)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x694)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x6ac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x78c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x81c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x824)%Z)] /\
  PP_entry = AF_LLVMFuzzerTestOneInput.
Proof. split; reflexivity. Qed.
Lemma PE_calls_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat ((o - 4) / 4)))
    (PE_SM_SITE :: PE_MEMCPY_SITE :: PE_MEMSET_SITE :: PE_SITES ++ PE_OPEN_SITES ++ PE_NEXT_SITES
       ++ PE_CLOSE_SITES ++ PE_BCMP_SITES ++ PE_RD32_SITES ++ PE_RDU32_SITES) =
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
   Some (PCall PS___interceptor_trampoline_bcmp (1%bv : bv 5));
   Some (PCall PS_rd32 (1%bv : bv 5)); Some (PCall PS_rd32 (1%bv : bv 5)); Some (PCall PS_rd32 (1%bv : bv 5));
   Some (PCall PS_rd32 (1%bv : bv 5)); Some (PCall PS_rd32 (1%bv : bv 5)); Some (PCall PS_rd32 (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5)); Some (PCall PS_rd_u32 (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5)); Some (PCall PS_rd_u32 (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.
(* The three NULL-test slots, verbatim words of the listing: beqz s6,+8 (0x809bc), beqz s2,+0x674
   to 0x81034 (0x809c0), beqz a0,+0x564 to 0x81034 (0x80ad0). *)
Lemma PE_null_tests_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat (o / 4))) [PP_dup0; PP_dupnull; PP_bufnull] =
  [Some (PW 0x000b0463); Some (PW 0x66090a63); Some (PW 0x56050263)].
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
   8 bytes: sd s6,0x498(s8) 0x809ac) and g_file (object 2, 8 bytes: sd s5,0(s3) 0x80990, sd s2,0(s3) 0x809dc). On the pin
   they are PcapEntry.G_HARNESS_U (pe_G_pin; the measurement and the neighbours are in lib/B/Prog/PcapEntry.v). *)
Definition pe_G : list (Z * Z) := [(pa_val (A_OBJ 4), 8); (pa_val (A_OBJ 2), 8)].

(* What the call may charge the allocator meter, at most, for an input of n bytes: the copy of
   the file (at most n bytes), two FILE blocks (one per pcap_source_open), the record buffer
   (at most 2040 bytes, 8 x one input byte, 0x80ab8) and six frees (each fclose frees twice,
   musl fclose 0x8e180 and 0x8e188, and the harness frees the buffer and the copy). *)
Definition pe_need (n : Z) : Z :=
  mo_malloc MT n + 2 * mo_malloc MT SRC_FILE_BLOCK + mo_malloc MT 2040 + 6 * mo_free MT.

(* What every phase may assume of the start: the pre-condition of the entry contract at the
   listing's image, the realigned stack pointer, the atoms of the entry registers, the
   meter and its budget (the bridge sets c_T := XM_LIB n and needs pe_need n <= XM_LIB n), the side
   condition of the journal's global ranges (gx_ok SEGS B pe_G: image bytes outside as_owned_static), that no byte of
   pe_G is a read-only byte, the AddrHashMap meta cell or errno (the callees' premises arodata_okP / asrc_meta_inv are
   stated at the harness's start memory, which the gx journal fixes only outside pe_G, and their kept clauses exclude
   errno; lib/A's conjunct, found by a Theorem Labs lane. On this pin G is .bss 0x5d3e40.. / 0x5d3e60.., the RELRO window
   0x99198..0x9a3f0, the meta cell InitializeCommonInterceptors::metadata_mem 0xa1008 (16 bytes; the asan pin's is
   0xa1108): disjoint; errno is B's TLS cell), and
   the call traces of the five calls of the wrappers for malloc and free, in the
   donor's form (cgif lib/A/ACf5.v:155-165): the malloc start only with the two malloc sites,
   the free start only with the three free sites. The asan image discharges both by
   ACejSites.llvmf_site_in (lib/A/Prog/PcapEntryDefs.v pe_traces_of_sites); this image has no trace universe yet: its
   allocator trace starts are pc_malloc_ra0 = 0x52ec4 (`jal GetCurrentPc` 0x52ec0 in __interceptor_malloc 0x52dfc)
   and pc_free_ra0 = 0x52d64 (0x52d60 in __interceptor_free 0x52c2c), BASE = 0x80788, and the spine of pch cx is
   [0x80684] when the frame lies below the stack top. *)
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
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8)) /\
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_MALLOC_SITES ->
     In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (pch cx)) (as_universe B)) /\
  (forall regsT : bvmap 5 word, In (raZ regsT - BASE) PE_FREE_SITES ->
     In (call_trace0 (pc_free_ra0 (as_code B)) regsT (pch cx)) (as_universe B)).

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

(* The frame's header as the prologue writes it (0x808e8..0x808f0): the magic, then the
   listing's objects 5 and 6 (PE_DESCR and PE_FNPC on the pin, PE_pin_values). *)
Definition pheader (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp) = Some PE_MAGIC /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + 8) = Some (pa_val (A_OBJ 5)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + 16) = Some (pa_val (A_OBJ 6)) /\
  (* the frame's last word holds its flag's address (aj_stack_malloc_atS's post at the call 0x80888); the epilogue
     loads it (ld a0,0x78(s7) 0x80f18) to give the frame back (sb zero,0(a0) 0x80f1c); lib/A's conjunct, found by
     a Theorem Labs lane *)
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (pF cx fp + PE_FLAGPTR) = Some (pFL cx fp).

(* A spill slot of the machine frame: the body reads these back after every call. *)
Definition pslot (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v.

(* The slots every phase from the first pcap_source_next on keeps (PP_KD; written at 0x808bc,
   0x8096c / 0x8097c, 0x80944, 0x80a20..0x80a28, 0x80abc and 0x80afc), for a frame taken on the
   side stack (PS_FK holds F itself then). The record buffer's slot PS_BUF holds an address the
   cut names, so each cut states it beside pslots. *)
Definition pslots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  pslot cx W3 ms3 PS_D (match c_pl cx with [] => 0 | d :: _ => bv_unsigned d end) /\
  pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_SH (pSH cx fp) /\
  pslot cx W3 ms3 PS_F (pF cx fp) /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\
  pslot cx W3 ms3 PS_TSP (pF cx fp + PO_TS) /\
  pslot cx W3 ms3 PS_CAP (8 * match c_pl cx with [] => 0 | d :: _ => bv_unsigned d end).

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the
   entry stack pointer in s0, gp and tp. (The asan build also keeps the shadow base in s11; this one
   keeps it in the slot PS_SHB, pslots.) *)
Definition pregs (cx : ecx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (c_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (c_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (c_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back
   (0x80820..0x80850, 0x80f6c..0x80f9c): ra at sp0 - 8, then s0, s1, s2..s11. *)
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

(* The post-condition of the whole call, in the shape the entry contract's post asks: the
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
   (OBLIGATIONS.md (sha256 781e8f81f164; internal record) row 11: the contract at ameter_triv (fun _ => 0) (fun _ => 0) ..., so c_T = 0):
   under cgif's trivial meter every charge is 0, so pe_need is 0 for every input length. *)
Lemma pe_need_triv : forall n, pe_need YCbp.ameter_triv n = 0.
Proof. intros n. reflexivity. Qed.
Lemma pe_need_triv_budget : forall n, pe_need YCbp.ameter_triv n <= (fun _ : Z => 0) n.
Proof. intros n. rewrite pe_need_triv. cbv beta. lia. Qed.

(* The harness's global ranges on the pin: the listing's objects 4 and 2 are g_file_len and g_file (PE_pin_values). *)
Lemma pe_G_pin : [(pcap_obj 4, 8); (pcap_obj 2, 8)] = G_HARNESS_U.
Proof. reflexivity. Qed.
