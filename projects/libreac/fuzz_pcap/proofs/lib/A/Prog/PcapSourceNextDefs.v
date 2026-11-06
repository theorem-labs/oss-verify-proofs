From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* pcap_source_next (0x8181c, listing offset AF_pcap_source_next = 0x10e4, 413 instructions) on the
   ASan build of libreac v1.9.0: the asan image's own data for the walk, and the data the walk's
   phases share. The contract itself (tpcap_source_next_specX / _post and everything it names), the
   lift of the model, the record loop's model clause and the constants both ASan builds share are
   the image-free lib/A/Prog/PcapSourceNextSpec.v, which this file Requires (porter 01:25Z: a lib/B
   closure may hold only image-free lib/A files). The walk itself is lib/A/Prog/PcapSourceNext.v.

   WHY THE CALLER-JOURNAL FORM. The call writes into memory the CALLER owns: the 24 bytes of the
   caller's `struct pcap_source` (the harness keeps it at F + 32 of its own class-1 side-stack
   frame), the caller's record buffer (a heap block the harness allocated) and the caller's
   `uint64_t ts` (F + 96 of the same frame). apost_base's footprint can only name heap blocks, so
   the contract is cgif's caller-journal form (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365,
   tlzw_kept / tlzw_pR_ok / tlzw_post / tlzw_spec; a Theorem Labs lane's shape in
   proofs/libreac/fuzz_grant/lib/A/Prog/CtrlFinish.v): the premise is the CALLER's journal, the
   right to write each of those bytes is a premise the caller supplies per byte (awr_byte), and the
   post extends the SAME journal.

   Every number below is read from the pinned
   fuzz_pcap.asan image (sha256 b7a91d9b1fb0017d...;
   symbols from its unstripped twin fuzz_pcap.asan (sha256 36da3052c383), capstone 5 disassembly).
   The comment beside a number names the instruction it comes from, by its address.

   THE SHAPE OF THE CODE.
   - a machine-stack frame of 224 bytes (`addi sp,sp,-0xe0` 0x8181c; `sd zero,0(sp)` 0x81820 probes
     its lowest word). ra and s0..s11 are saved at sp0-8 .. sp0-104 (0x81824..0x81854), s0 := sp0
     (`addi s0,sp,0xe0` 0x81858), the stack is realigned to 32 bytes (`andi sp,sp,-0x20` 0x8185c)
     and s1 := that stack pointer (`mv s1,sp` 0x81860). Every call of the body is made with
     sp = s1;
   - a frame on the side stack for frames, class 0 (64-byte slots), holding ONE 16-byte object at
     offset 32 (the record header the first fread reads; the frame's description string is object
     13, "1 32 16 5 ph:53"). When the use-after-return flag (the word at 0xa18c0, through its GOT
     word 0x99888: 0x81874, 0x81878, 0x81880) is not zero, `__asan_stack_malloc_0(0x40)` (a0 := 0x40
     at 0x81890, `jal` 0x81894, return address 0x81898) gives the frame F in a0. The flag is 1 on
     this image (the allocator invariant's AR_const_law, YG0d.v:465 `rd32 ... (as_uar_cell B) 1`),
     so the arm at 0x818a0..0x818c4 that builds the frame on the machine stack instead is NOT
     reached, and the walk closes it from that constant.

   THE CALL IT MAKES: three calls of the fread wrapper (0x819b8 nm = 16 into its own frame's object,
   0x81af0 and 0x81bd4 with nm from the record, into the caller's buffer) and one call of
   __asan_memmove (0x81cdc, overlapping ranges inside the caller's buffer). None of them allocates
   or frees, so the call costs no allocator event: EV_NEXT = 0.

   THE MODEL is Pau's own address-free model of this function, lib/Prog/pcap_source_struct_next.v,
   used unchanged (PSN below); the wrappers here only lift it from `list byte` to the `list Z` the
   read-stream predicate lib/A/Stdio/PSource.v states its content with. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
(* The image-free part (the contract, the model's lift, the shared constants), EXPORTED so that a file
   that Requires this one sees the same names as before the split. Pau's model is its module PSN. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the machine frame ---- *)

Definition NX_MFRAME : Z := 224.          (* addi sp,sp,-0xe0               0x8181c *)
(* The realigned stack pointer that s1 holds for the whole body. *)
Definition nx_sp1 (sp0 : Z) : Z := 32 * ((sp0 - NX_MFRAME) / 32).
                                          (* andi sp,sp,-0x20 0x8185c; mv s1,sp 0x81860 *)

(* ---- the constants of PcapSourceNextSpec.v on this image ----
   NX_CID = 0 / NX_FREQ = 64: `addi a0,zero,0x40` 0x81890, `jal __asan_stack_malloc_0` 0x81894.
   NX_NSH = 8: the shadow bytes 0(s3)..7(s3). NX_MAGIC: `lui a0,0x41b59` 0x818c8, `addiw a0,a0,-0x54d`
   0x818e0, `sd a0,0(s2)` 0x818ec. NX_RETIRED: `lui a0,0x45e03` 0x81d34, `addiw a0,a0,0x60e` 0x81d38,
   `sd a0,0(s2)` 0x81d3c. NX_FLAGPTR = 56: `ld a0,0x38(a5)` 0x81d68, `sb zero,0(a0)` 0x81d6c.
   NO_PH = 32: `addi s10,s2,0x20` 0x81944. NX_PH_LEN = 16: `addi a2,zero,0x10` 0x819b0.
   NSH_entry: a0 = 0xf1, a4 = 0xf8, a3 = 0xf3 from 0x818d8..0x818f8, stored 0x81900..0x81920.
   NSH_ph: `sb zero,4(s3)` / `5(s3)` 0x81998, 0x8199c. NSH_out: a0 = 0xf8 at 0x81b00..0x81b08 and
   0x81d24..0x81d2c. NSH_retired: a0 = -0xb 0x81d44, 0x81d48..0x81d64. NSH_machine: 0x81d74..0x81d90.
   PS_F_OFF: `ld a0,0(s5)` 0x81934, 0x819a8, 0x81ae0, 0x81bc4. PS_SW_OFF: `lw a0,0(a0)` 0x819e8 (through
   the ps+8 spill). PS_OL_OFF: `sw a3,0(t2)` 0x81ab8. PS_VT_OFF: `sw zero,0x10(s5)` 0x81bf4, `sw a3,0(a2)`
   0x81c6c. PS_VID_OFF: `sh zero,0(a0)` 0x81c14, `sh a2,0(a0)` 0x81ccc. *)

(* The frame's header words 2 and 3: the address of the frame's description string (object 13,
   "1 32 16 5 ph:53") and the function's own address (object 14). *)
Definition NX_DESCR : Z := Eval compute in (Symbols.Asan.Sec.s_rodata + 0x4c4a)%Z.  (* auipc a1,0xfff93 0x818cc; addi a1,a1,0x65e 0x818e4; sd a1,8(s2) 0x818f0 *)
Definition NX_FNPC : Z := Eval compute in Symbols.Asan.s_pcap_source_next.  (* auipc a2,0 0x818d0; addi a2,a2,-0xb4 0x818e8; sd a2,0x10(s2) 0x818f4 *)


(* ---- the spill slots, as offsets from s1 ---- *)

Definition NS_OFF12 : Z := 16.    (* (ps + 12) mod 8 + 3:    sd a3,0x10(s1) 0x81994 *)
Definition NS_OFF8 : Z := 24.     (* (ps + 8) mod 8 + 3:     sd a2,0x18(s1) 0x81980 *)
Definition NS_TS : Z := 32.       (* the caller's &ts (0 for none): sd s6,0x20(s1) 0x8193c;
                                     reloaded into s5 at 0x81c08 *)
Definition NS_SB : Z := 40.       (* the shadow base 0x7fff8000: sd s9,0x28(s1) 0x81984;
                                     reloaded at 0x81be4, 0x81c24, 0x81c48, 0x81c78, 0x81cec *)
Definition NS_PS12 : Z := 64.     (* ps + 12 (the orig_len field): sd a3,0x40(s1) 0x8196c *)
Definition NS_MASK : Z := 72.     (* 0xff00, the byte-swap mask: sd a0,0x48(s1) 0x81964 *)
Definition NS_SH8 : Z := 80.      (* the shadow byte of ps + 8:  sd a1,0x50(s1) 0x81978 *)
Definition NS_SH12 : Z := 56.     (* the shadow byte of ps + 12: sd a0,0x38(s1) 0x8198c *)
Definition NS_PS8 : Z := 88.      (* ps + 8 (the byte-swap flag): sd a2,0x58(s1) 0x81958 *)
Definition NS_FK : Z := 48.       (* __asan_stack_malloc_0's result (0 for a machine frame):
                                     sd a5,0x30(s1) 0x81940; reloaded 0x81d30 *)
Definition NS_F0 : Z := 112.      (* F: sd s2,0x70(s1) 0x8192c *)


(* ---- the stack this call needs ---- *)

(* Its own realigned frame is at most 240 bytes below the caller's sp (NX_MFRAME = 224 and
   spZ regs mod 16 = 0, then the realignment to 32 bytes takes 0 or 16 more), and the deepest
   callee is the fread wrapper, AFREAD_STK = 8192 (lib/A/Stdio/PFreadISpec.v, FROZEN), called with
   sp = sp1. __asan_memmove and __asan_stack_malloc_0 run in ESTACK = 4096 below the same sp. So
   the call uses at most 240 + AFREAD_STK bytes below the caller's sp. NX_STK is the figure the
   harness budgets for this call (PcapEntryDefs.v:249-250, 240 + 64 + AFREAD_STK = 8496); the 64
   extra bytes are slack (the machine-stack frame arm 0x818a0..0x818c4 that would use them is not
   reached: the use-after-return flag is 1, AR_const_law, and a Theorem Labs lane measured it 22:44Z).
   Depth: the caller's afn_pre gives astk_ok NX_STK ly sp0 with ly_bot = ly_top - 2 ^ 23
   (YG0f.v:36, :63) and ASTACK = 16384 (YG0d.v:18), so the astk_ok conjunct this call's own callees
   need is ly_top - sp1 < 2 ^ 23 + 16384 - AFREAD_STK, which follows from
   ly_top - spZ regs < 2 ^ 23 + 16384 - NX_STK and sp1 >= spZ regs - 240. *)
Definition NX_STK : Z := 304 + AFREAD_STK.


(* ---- the pcs of the phase cuts, as offsets in the listing (address - 0x80738) ---- *)

Definition NP_entry : Z := Eval compute in (Symbols.Asan.s_pcap_source_next - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x8181c, the first slot                                    *)
Definition NP_sm_ra : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x7c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x81898, __asan_stack_malloc_0 (0x81894) returned          *)
Definition NP_frame : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0xac) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x818c8, the frame is taken; both arms join here           *)
Definition NP_loop : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x17c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x81998, the head of the record loop (back edges 0x81b0c,
                                       0x81afc)                                                   *)
Definition NP_hd_ra : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x1a0) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x819bc, the fread of the 16-byte header (0x819b8) returned *)
Definition NP_sk1 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x2a4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81ac0, cap < incl: beqz s7, the `cap == 0` test          *)
Definition NP_sk0 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x2a8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81ac4, the head of the skip loop (back edge 0x81afc)     *)
Definition NP_sk_ra : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x2d8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x81af4, the fread of a skipped chunk (0x81af0) returned   *)
Definition NP_empty : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x2e4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x81b00, `ph` out of scope, then back to the loop head     *)
Definition NP_h0 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x310) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81b2c, the closed reader: s6 := -1, j 0x81d34            *)
Definition NP_eof : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x318) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81b34, the header read was short: bnez a0               *)
Definition NP_fit : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x324) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81b40, cap >= incl: the record is handed back            *)
Definition NP_fit_ra : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x3bc) - Symbols.Asan.s_libreac_fuzz_fopen)%Z. (* 0x81bd8, the fread of the record (0x81bd4) returned        *)
Definition NP_mm_ra : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x4c4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x81ce0, __asan_memmove (0x81cdc) returned                 *)
Definition NP_ts : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x4c8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81ce4, beqz s5: the caller asked for no timestamp        *)
Definition NP_exit : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x508) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.   (* 0x81d24, `ph` out of scope                                 *)
Definition NP_x0 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x518) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81d34, the frame is given back                           *)
Definition NP_epi : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x578) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81d94, a0 := s6, then the epilogue                       *)
Definition NP_ret : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x5b8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81dd4, the `ret`                                         *)
Definition NP_report : Z := Eval compute in ((Symbols.Asan.s_pcap_source_next + 0x5bc) - Symbols.Asan.s_libreac_fuzz_fopen)%Z. (* 0x81dd8, the first slot of the error path                  *)

(* The 24 run segments of our v1.9 re-walk (pcap-v190-next.md (sha256 b1d06d8683d6; internal record)), at these pcs:
     pro, pro_branch   NP_entry -> the use-after-return flag's test (0x8188c)
     ffr, ffr_flag     the flag is not 0 -> __asan_stack_malloc_0 0x81894
     sm_call           the call itself (NP_sm_ra)
     rfr, rfr_stk      the machine-stack arm 0x818a0..0x818c4 (NOT reached: the flag is 1)
     ent, ent_real,
     ent_real_go,
     entry             NP_frame -> NP_loop (the frame's header and shadow, the spill slots)
     hd                NP_loop -> the fread of the header 0x819b8
     hdr               NP_hd_ra -> NP_loop / NP_sk1 / NP_fit / NP_exit
     sk1               NP_sk1 -> NP_sk0 / NP_exit
     sk0               NP_sk0 -> the fread of a chunk 0x81af0
     sk2               NP_sk_ra -> NP_loop / NP_sk0 / NP_exit
     fit               NP_fit -> the fread of the record 0x81bd4
     fit2              NP_fit_ra -> __asan_memmove 0x81cdc / NP_ts / NP_exit
     mmr               NP_mm_ra -> NP_ts
     ts                NP_ts -> NP_exit
     ret, exit         NP_exit -> NP_x0
     x0                NP_h0 / NP_eof -> NP_x0
     epi               NP_x0 -> NP_ret
   Every shadow check that fails branches into the error path at NP_report (0x81dd8..0x81e8c,
   calls of __asan_report_{load,store}{1,2,4,8}); the walk proves each of those branches is not
   taken, from the addressability premises below, and no stack constant budgets them. *)

(* The cut pcs as addresses of the pin, and the four calls the listing holds: checked once here
   against PcapAddr.pcap_text and PcapList.pcap_listing. *)
Lemma NP_addrs :
  map (fun o => pcap_text + o)
    [NP_entry; NP_sm_ra; NP_frame; NP_loop; NP_hd_ra; NP_sk1; NP_sk0; NP_sk_ra; NP_empty; NP_h0;
     NP_eof; NP_fit; NP_fit_ra; NP_mm_ra; NP_ts; NP_exit; NP_x0; NP_epi; NP_ret; NP_report] =
    [(symaddr Symbols.Asan.s_pcap_source_next); (symaddr (Symbols.Asan.s_pcap_source_next + 0x7c)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0xac)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x17c)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x1a0)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x2a4)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x2a8)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x2d8)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x2e4)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x310)%Z);
     (symaddr (Symbols.Asan.s_pcap_source_next + 0x318)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x324)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x3bc)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x4c4)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x4c8)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x508)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x518)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x578)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x5b8)%Z); (symaddr (Symbols.Asan.s_pcap_source_next + 0x5bc)%Z)] /\
  NP_entry = AF_pcap_source_next.
Proof. split; reflexivity. Qed.

(* The call sites, as listing offsets of their return addresses. *)
Definition NX_SM_SITE : Z := NP_sm_ra.                       (* 0x81898 *)
Definition NX_FREAD_SITES : list Z := [NP_hd_ra; NP_sk_ra; NP_fit_ra].  (* 0x819bc, 0x81af4, 0x81bd8 *)
Definition NX_MM_SITE : Z := NP_mm_ra.                       (* 0x81ce0 *)
Lemma NX_calls_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat ((o - 4) / 4)))
    (NX_SM_SITE :: NX_MM_SITE :: NX_FREAD_SITES) =
  [Some (PCall PS___asan_stack_malloc_0 (1%bv : bv 5));
   Some (PCall PS___asan_memmove (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.
(* The frame's two pin objects, and the two GOT words the prologue reads. *)
Lemma NX_pin_values :
  pcap_obj 13 = NX_DESCR /\ pcap_obj 14 = NX_FNPC /\
  pcap_obj 0 = (symaddr (Symbols.Asan.Sec.s_got + 0xb8)%Z) /\ pcap_obj 1 = (symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z) /\
  pcap_obj 15 = (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address) /\ pcap_obj 16 = (symaddr Symbols.Asan.s___asan_option_detect_stack_use_after_return) /\
  pcap_sigma PS___asan_stack_malloc_0 = (symaddr Symbols.Asan.s___asan_stack_malloc_0) /\
  pcap_sigma PS___interceptor_trampoline_fread = (symaddr Symbols.Asan.s___wrap_fread) /\
  pcap_sigma PS___asan_memmove = (symaddr Symbols.Asan.s___asan_memmove).
Proof. repeat split; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* The phases of the walk (this build: segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi,       *)
(* nstk := NX_STK)                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* The call's context: everything the premises fix. One record, so that a phase lemma states one
   hypothesis instead of forty, and so that the phases can be split across files. *)
Record ncx := mkNCX {
  n_STK : Z; n_sp0 : Z; n_FP : list (Z * Z);
  n_ly : alayout; n_S : astate; n_W0 : world SEGS; n_mem0 : word -> option byte; n_md0 : Model;
  n_own : list (Z * Z);
  n_lyc : alayout; n_Sc : astate; n_W : world SEGS; n_memc : word -> option byte; n_mdc : Model;
  n_k : Z;
  n_regs : bvmap 5 word;
  n_ps : Z; n_buf : Z; n_cap : Z; n_ts : Z;
  n_h : Z; n_b : Z; n_p : Z; n_sw : Z;
  n_lol : Z; n_lvt : Z; n_lvid : Z; n_tsv : Z;
  n_M : Z;                         (* the stream's meta region *)
  n_cid : Z; n_pos : Z;            (* the caller's frame the struct lies in *)
  n_C : list Z; n_bj : list Z; n_pad : list Z;
  n_ch : list (Z * Z * Z);
  n_E0 : env                       (* the atoms of the entry registers *)
}.

(* The realigned stack pointer this call runs on, and the two addresses of its own frame. *)
Definition n_sp1 (cx : ncx) : Z := nx_sp1 (spZ (n_regs cx)).
Definition nF (cx : ncx) (fp : Z) : Z := frame_addr (n_lyc cx) NX_CID fp.
Definition nFL (cx : ncx) (fp : Z) : Z := flag_addr (n_lyc cx) NX_CID fp.
Definition nSH (cx : ncx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (nF cx fp).

(* The chain this call hands to the fread wrapper: its own frame is on the chain when it fits under
   the layout's top (cgif lib/A/ACf5.v:128-131, PcapEntryDefs.pch). *)
Definition nx_ch (cx : ncx) : list (Z * Z * Z) :=
  if spZ (n_regs cx) + 16 <? ly_top (n_lyc cx)
  then (spZ (n_regs cx), raZ (n_regs cx), s0Z (n_regs cx)) :: n_ch cx else [].

(* What every phase may assume of the start: exactly the premises of tpcap_source_next_specX at
   segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi, nstk := NX_STK, in the same order, plus the
   atoms of the entry registers. *)
Definition nx_base (cx : ncx) : Prop :=
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (n_W cx)) (n_memc cx)) /\
  YK0s.ret_ok (getr (n_regs cx) 1) /\ 4096 <= raZ (n_regs cx) /\
  getr (n_regs cx) 3 = w64 (as_gp B) /\ getr (n_regs cx) 4 = w64 (as_tp B) /\
  getr (n_regs cx) 10 = w64 (n_ps cx) /\ getr (n_regs cx) 11 = w64 (n_buf cx) /\
  getr (n_regs cx) 12 = w64 (n_cap cx) /\ getr (n_regs cx) 13 = w64 (n_ts cx) /\
  spZ (n_regs cx) mod 16 = 0 /\ n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK /\
  spZ (n_regs cx) <= n_sp0 cx /\
  achain (n_lyc cx) (aview SEGS (w_H (n_W cx)) (n_memc cx)) (spZ (n_regs cx)) (s0Z (n_regs cx)) (n_ch cx) /\
  count_cid NX_CID (frames (n_Sc cx)) < fs_frames NX_CID /\
  val_mem SEGS (rdW (n_W cx) (n_memc cx)) (n_ps cx + PS_F_OFF) 8 (n_h cx) /\ 0 <= n_h cx < 2 ^ 64 /\
  n_ps cx mod 8 = 0 /\ 4096 <= n_ps cx /\ n_ps cx + PS_LEN <= 2 ^ 47 /\ amem_range (n_ps cx) PS_LEN /\
  In (n_cid cx, n_pos cx) (n_own cx) /\ frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) /\
  range_addressable (aview SEGS (w_H (n_W cx)) (n_memc cx)) SHADOW_OFF (n_ps cx) PS_LEN /\
  (n_h cx <> 0 ->
     nx_ps_at SEGS (rdW (n_W cx) (n_memc cx)) (n_ps cx) (n_h cx) (n_sw cx) (n_lol cx) (n_lvt cx) (n_lvid cx)
       (n_pad cx)) /\
  (n_h cx <> 0 -> n_sw cx = 0 \/ n_sw cx = 1) /\
  (n_h cx <> 0 -> 0 <= n_lol cx < 2 ^ 32 /\ 0 <= n_lvt cx < 2 ^ 32 /\ 0 <= n_lvid cx < 2 ^ 16) /\
  (n_h cx <> 0 ->
     nx_wr_ok NX_STK B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
       (spZ (n_regs cx)) (n_ps cx) PS_LEN) /\
  (n_h cx <> 0 ->
     In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B (n_lyc cx) (n_Sc cx)) /\
     4096 <= n_buf cx /\ n_buf cx + nx_bufn (n_cap cx) < 2 ^ 63 /\
     garr8 SEGS (rdW (n_W cx) (n_memc cx)) (n_buf cx) (n_bj cx) /\
     Z.of_nat (length (n_bj cx)) = nx_bufn (n_cap cx) /\
     0 <= n_cap cx <= NX_CAP_MAX /\
     nx_wr_ok NX_STK B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
       (spZ (n_regs cx)) (n_buf cx) (nx_bufn (n_cap cx)) /\
     (n_buf cx + nx_bufn (n_cap cx) <= n_ps cx \/ n_ps cx + PS_LEN <= n_buf cx)) /\
  (n_h cx <> 0 -> n_ts cx <> 0 ->
     val_mem SEGS (rdW (n_W cx) (n_memc cx)) (n_ts cx) 8 (n_tsv cx) /\ n_ts cx mod 8 = 0 /\
     4096 <= n_ts cx /\ n_ts cx + 8 <= 2 ^ 47 /\ amem_range (n_ts cx) 8 /\
     (exists tcid tpos, In (tcid, tpos) (n_own cx) /\ frame_addr (n_lyc cx) tcid tpos <= n_ts cx /\
        n_ts cx + 8 <= frame_addr (n_lyc cx) tcid tpos + fs_frame_bytes tcid) /\
     nx_wr_ok NX_STK B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
       (spZ (n_regs cx)) (n_ts cx) 8 /\
     range_addressable (aview SEGS (w_H (n_W cx)) (n_memc cx)) SHADOW_OFF (n_ts cx) 8 /\
     (n_ts cx + 8 <= n_ps cx \/ n_ps cx + PS_LEN <= n_ts cx) /\
     (n_buf cx + nx_bufn (n_cap cx) <= n_ts cx \/ n_ts cx + 8 <= n_buf cx)) /\
  (n_h cx <> 0 ->
     In (n_h cx, SRC_FILE_BLOCK) (ablocks B (n_lyc cx) (n_Sc cx)) /\
     In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B (n_lyc cx) (n_Sc cx)) /\
     asource_at SEGS KS (rdW (n_W cx) (n_memc cx)) (n_h cx) (n_b cx) (n_C cx) (n_p cx) /\
     Z.of_nat (length (n_C cx)) < 2 ^ 26 /\ 0 <= n_p cx <= Z.of_nat (length (n_C cx)) /\
     (n_buf cx + nx_bufn (n_cap cx) <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_buf cx) /\
     (n_buf cx + nx_bufn (n_cap cx) <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_buf cx) /\
     (n_ps cx + PS_LEN <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_ps cx) /\
     (n_ps cx + PS_LEN <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_ps cx) /\
     (n_ts cx <> 0 ->
        (n_ts cx + 8 <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_ts cx) /\
        (n_ts cx + 8 <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_ts cx)) /\
     (forall x, inFP (asource_fp (n_h cx)) x ->
        inFP (n_FP cx) x \/ in_tmp_block (ablocks B (n_ly cx) (n_S cx)) (ablocks B (n_lyc cx) (n_Sc cx)) x)) /\
  (n_h cx <> 0 -> asrc_meta_inv SEGS KS (n_lyc cx) (rdW (n_W cx) (n_memc cx)) (n_M cx)) /\
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (n_E0 cx) n = getr (n_regs cx) r) /\
  bv_unsigned (ew (n_E0 cx) 2) = spZ (n_regs cx).

(* The post of the whole call, in the shape tpcap_source_next_post asks. *)
Definition nx_post (cx : ncx) : world SEGS -> config -> Prop :=
  tpcap_source_next_post SK SEGS NX_STK B MT KS
    (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx)
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx).

(* ---- the memory of a phase ---- *)

(* The shadow bytes of this call's own frame. *)
Definition nshadow (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* The frame's header as the prologue writes it (0x818ec..0x818f4): the magic, then the listing's
   objects 13 and 14 (NX_DESCR and NX_FNPC on the pin, NX_pin_values). *)
Definition nheader (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp) = Some NX_MAGIC /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + 8) = Some (pa_val (A_OBJ 13)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + 16) = Some (pa_val (A_OBJ 14)).

(* A spill slot of the machine frame: the body reads these back after every call. *)
Definition nslot (cx : ncx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx + off) = Some v.

(* The slots every phase from the loop head on keeps (written at 0x8192c..0x81994, for a frame taken
   on the side stack, where NS_FK holds F itself). *)
Definition nslots (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nslot cx W3 ms3 NS_F0 (nF cx fp) /\
  nslot cx W3 ms3 NS_FK (nF cx fp) /\
  nslot cx W3 ms3 NS_TS (n_ts cx) /\
  nslot cx W3 ms3 NS_SB SHADOW_OFF /\
  nslot cx W3 ms3 NS_PS8 (n_ps cx + PS_SW_OFF) /\
  nslot cx W3 ms3 NS_PS12 (n_ps cx + PS_OL_OFF) /\
  nslot cx W3 ms3 NS_SH8 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\
  nslot cx W3 ms3 NS_SH12 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_OL_OFF)) /\
  nslot cx W3 ms3 NS_OFF8 ((n_ps cx + PS_SW_OFF) mod 8 + 3) /\
  nslot cx W3 ms3 NS_OFF12 ((n_ps cx + PS_OL_OFF) mod 8 + 3) /\
  nslot cx W3 ms3 NS_MASK 0xff00.

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the entry
   stack pointer in s0, gp and tp. (s11 is NOT the shadow base in this function: the base lives in
   the NS_SB slot from 0x81984 on, and s9 is reused for the record's incl_len.) *)
Definition nregs (cx : ncx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (n_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (n_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (n_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back (0x81824..0x81854,
   0x81d9c..0x81dcc): ra at sp0 - 8, then s0, s1, s2..s11. *)
Definition nsaved (cx : ncx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 8) = Some (raZ (n_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (n_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* The slot's last word: __asan_stack_malloc_0 leaves the address of the slot's flag byte there
   (StackMalloc0.v:44, fframe_region PcapFrame.v:66); the epilogue stores 0 through it
   (`ld a0,0x38(a5); sb zero,0(a0)` 0x81d68, 0x81d6c). Nothing in the body writes it. *)
Definition nflagw (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + NX_FLAGPTR) = Some (nFL cx fp).

(* What every state from the frame's header on carries (0x818c8 on): the pc (a listing offset),
   the machine state's fixed fields (YK11.mkst: the floating-point state is the context's, which the
   code never touches), the registers, the saved registers, the frame's header, flag word and
   shadow, s2 = F and s3 = the frame's shadow address (neither is written after 0x818d4 / 0x818fc),
   and the slot NS_F0 (written at 0x8192c, before the closed reader's `beqz` 0x81938). *)
Definition nx_body0 (cx : ncx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  nregs cx ms3 /\ nsaved cx W3 ms3 /\ nheader cx fp W3 ms3 /\ nflagw cx fp W3 ms3 /\
  nshadow cx fp W3 ms3 sh /\ length sh = NX_NSH /\
  getr (ms_regs ms3) 18 = w64 (nF cx fp) /\ getr (ms_regs ms3) 19 = w64 (nSH cx fp) /\
  nslot cx W3 ms3 NS_F0 (nF cx fp).

(* ... and, from the spills 0x8193c..0x81994 on (the open reader), every spill slot. *)
Definition nx_body (cx : ncx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  nx_body0 cx fp pc W3 ms3 sh /\ nslots cx fp W3 ms3.

(* ---- a phase ---- *)

(* `nx_from POST GI` says: from any machine state that `GI` describes, with the class-0 frame taken
   at slot fp, the run reaches POST. A phase lemma has the shape
   `nx_from POST GI_next -> nx_from POST GI_self`; the record loop and the skip loop are proved by
   induction on the number of turns left. *)
Definition nx_from (POST : ncx -> world SEGS -> config -> Prop)
  (GI : ncx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ncx) (fp k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  nx_base cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  GI cx fp k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under `nx_base` to the same post-condition. The
   entry phase proves it from the phases that follow it. *)
Definition nx_start (POST : ncx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : ncx, nx_base cx ->
  SRr SEGS (n_W cx)
    (mkCfg (mkst (n_regs cx) (w64 (BASE + NP_entry)) (n_memc cx) (seg_rom SEGS)) (n_mdc cx))
    (POST cx).

(* ---- the shared middle state ---- *)

(* The journal's bookkeeping at every cut after the frame is taken: no allocator event
   (EV_NEXT = 0), the caller's blocks, the meter, and no descriptor or file-system change. *)
Definition nx_jbk (cx : ncx) (k2 : Z) (ly3 : alayout) (S3 : astate) (md3 : Model) : Prop :=
  k2 = n_k cx + EV_NEXT /\
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) /\
  mo_le MT (n_Sc cx) S3 0 /\
  m_fds md3 = m_fds (n_mdc cx) /\ m_fs md3 = m_fs (n_mdc cx).

(* The caller's bytes the call may write (the post's set). *)
Definition nx_E (cx : ncx) : Z -> Prop := nx_wrset (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx).

(* The struct's orig field for the last non-empty header lh (0x81ab8 writes it; an empty record
   leaves it alone). *)
Definition nx_ol (cx : ncx) (lh : option Z) : Z :=
  match lh with Some q0 => PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q0 | None => n_lol cx end.

(* nx_mid: the facts every cut of the open reader after the spills shares (NP_loop .. NP_exit).
   Parameters: pc and sh (the cut's pc and the frame's shadow); E (the caller's bytes written so far,
   inside nx_E); q (the stream's position); ol vt vid (the struct's orig / vtag / vid fields now);
   tv (the timestamp cell's value now, when ts <> 0); then the state as nx_from takes it.
   Registers: s8 = the shadow address of ps (0x81924; never written after). The others differ per
   cut (s4 = buf until 0x81cb4, s5 = ps until 0x81c08, s7 = cap until 0x81b68, s10 = F + 32 until
   0x81b6c, s9 / s11 / s6 per record): each phase states its own. *)
Definition nx_mid (cx : ncx) (fp pc : Z) (sh : list Z) (E : Z -> Prop) (q ol vt vid tv : Z)
  (k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body cx fp pc W3 ms3 sh /\
  getr (ms_regs ms3) 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) /\
  nx_jbk cx k2 ly3 S3 md3 /\
  (* the caller's memory: kept outside the stack window and E *)
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx)) E /\
  (forall a, E a -> nx_E cx a) /\
  (* the open reader: the struct, its shadow, the stream at q, the buffer, the timestamp cell *)
  n_h cx <> 0 /\
  nx_ps_at SEGS (rdW W3 (ms_mem ms3)) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ps cx) PS_LEN /\
  asource_at SEGS KS (rdW W3 (ms_mem ms3)) (n_h cx) (n_b cx) (n_C cx) q /\
  n_p cx <= q <= Z.of_nat (length (n_C cx)) /\
  (exists bj', garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) /\
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ts cx) 8 tv /\
     range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ts cx) 8).

(* The loop invariant of the record loop (NP_loop, 0x81998). `q` is the position in the file this
   turn starts at and `lh` the last non-empty record header seen so far (the model's `lh`). The
   shadow is NSH_entry: 0x81998 / 0x8199c themselves put `ph` in scope, and both edges into the
   head (the prologue, and NP_empty 0x81b00..0x81b0c) have it out of scope (PcapSourceNextHdrB.v, PcapSourceNextSkip.v,
   PcapSourceNextEntry.v). The struct's orig field is the one lh gives, vtag / vid / ts are the caller's.
   Registers: s4 = buf, s5 = ps, s7 = cap, s10 = F + 32 (s9 is dead here: written at 0x81a00 before
   any read). The chain clause is nx_chain_inv. *)
Definition nx_loop_inv (cx : ncx) (fp q : Z) (lh : option Z)
  (k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_mid cx fp NP_loop NSH_entry (nx_E cx) q (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 20 = w64 (n_buf cx) /\ getr (ms_regs ms3) 21 = w64 (n_ps cx) /\
  getr (ms_regs ms3) 23 = w64 (n_cap cx) /\ getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH) /\
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh.

(* The record loop by well-founded induction (the top, PcapSourceNext.v). A turn started at q that
   goes back to the head does so at some q' with q < q' <= |C| (KEmpty: q + 16; KBig: q + 16 + incl).
   So every phase inside a turn takes the loop head as `nx_from POST (nx_loop_at R)` for an R the
   top chooses, and carries `nx_next_ok R cx q0` for the turn's start q0. *)
Definition nx_next_ok (R : ncx -> Z -> Prop) (cx : ncx) (q : Z) : Prop :=
  forall q', q < q' <= Z.of_nat (length (n_C cx)) -> R cx q'.
Definition nx_loop_at (R : ncx -> Z -> Prop) :
  ncx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k2 ly3 S3 W3 ms3 md3 => exists q lh, R cx q /\ nx_loop_inv cx fp q lh k2 ly3 S3 W3 ms3 md3.

(* ---- the end of the body ---- *)

(* The post's final memory and a0, for this call's context. *)
Definition nx_fin_at (cx : ncx) (W3 : world SEGS) (mem3 : word -> option byte) (r : word) : Prop :=
  nx_fin SEGS NX_STK B KS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (spZ (n_regs cx))
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx) W3 mem3 r.

(* NP_exit (0x81d24, `ph` still in scope): every path of the open reader that ends the call
   (NP_eof, NP_sk1 with cap = 0, a short chunk at NP_sk_ra, a short record at NP_fit_ra, NP_ts)
   arrives here with the result in s6 and the caller's memory final. *)
Definition nx_exit_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body cx fp NP_exit W3 ms3 NSH_ph /\
  nx_jbk cx k2 ly3 S3 md3 /\
  nx_fin_at cx W3 (ms_mem ms3) (getr (ms_regs ms3) 22).

(* NP_x0 (0x81d34, `ph` out of scope, shadow NSH_entry): both readers. The closed reader comes from
   NP_h0 (0x81b2c, s6 := -1) right after the `beqz` 0x81938, before the spills, so only NS_F0 is
   written (nx_body0); a5 = F there (0x81898, not written after). The open reader comes from NP_exit,
   which reloads a5 from NS_FK (0x81d30). *)
Definition nx_x0_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body0 cx fp NP_x0 W3 ms3 NSH_entry /\
  getr (ms_regs ms3) 15 = w64 (nF cx fp) /\
  nx_jbk cx k2 ly3 S3 md3 /\
  nx_fin_at cx W3 (ms_mem ms3) (getr (ms_regs ms3) 22).

End c.
End b.
End a.

(* SK is explicit at every use: the closure's only global sink_head instance is the PLAIN build's
   (lib/Reusable/YI5b.v:12), so an inferred SK would make the stream facts vacuous (a Theorem Labs lane 21:57Z). *)
Arguments nx_base {rc} SK {PI}.
Arguments nx_post {fx rc} SK {PI}.
Arguments nx_from {rc} SK {PI}.
Arguments nx_start {fx rc} SK {PI}.

