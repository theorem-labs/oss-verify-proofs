From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30, 416 instructions) on
   the ASan+UBSan build of libreac v1.9.0: the data the phases of the lib/B walk share. The walk's top is
   lib/B/Prog/PcapSourceNext.v.

   THE CONTRACT IS LIB/A'S. The statement tpcap_source_next_specX (with tpcap_source_next_post, nx_ps_at, nx_wr_ok,
   nx_kept, nx_wrset, nx_fin and Pau's model wrappers nx_q .. nx_tsv, nx_chain_inv) is the image-generic text of
   lib/A/Prog/PcapSourceNextSpec.v; it is never copied here. This file EXPORTS that file (and only that one of
   lib/A's next files: lib/A's PcapSourceNextDefs Requires the asan image's listing and instance, and a lib/B file's
   Require closure may hold only lib/B, the core and image-free lib/A modules, porter 01:25Z). A lib/B phase file
   imports this file and gets the shared names plus the lib/B phase layer below (ncx, nx_base, nx_body, nx_mid,
   nx_loop_inv, nx_exit_inv, nx_x0_inv, NP_*, NS_*, ...: lib/A's names, lib/B's meanings). This build's stack is
   NX_STK_B.

   The constants of the class-0 frame and the struct are shared by the two images and are the Spec's (NX_CID,
   NX_FREQ, NX_FRAME, NX_NSH, NX_MAGIC, NX_RETIRED, NX_FLAGPTR, NO_PH, NX_PH_LEN, NSH_*, PS_*_OFF, PS_LEN, EV_NEXT,
   NX_CAP_MAX, nx_bufn); the comment below names the lib/B instruction each comes from. The image's own data
   (NX_DESCR, NX_FNPC, the pcs, the slots) are defined here and checked by NX_pin_values / NP_addrs.

   Every number below is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols from its unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59), capstone
   5). The slot-by-slot table: nxb-handoff.md (sha256 c02dc85fade1; internal record); the annotated disassembly:
   nxb-next.dis (sha256 7213b94e2690; internal record).

   THE SHAPE OF THE CODE, where it differs from lib/A's.
   - a machine-stack frame of 256 bytes (`addi sp,sp,-0x100` 0x815b8; `sd zero,0(sp)` 0x815bc). ra and s0..s11 are
     saved at sp0-8 .. sp0-104 (0x815c0..0x815f0, the same places as lib/A's), s0 := sp0 (0x815f4), the stack is
     realigned to 32 bytes (0x815f8) and s1 := sp (0x815fc). Every call is made with sp = s1.
   - the record buffer is spilled at once (`sd a1,0x60(s1)` 0x81608), before the frame is taken.
   - the class-0 frame F is held in s3 (0x81644) and its shadow address in s9 (0x81678, 0x8169c; never written
     again). From 0x816f4 s3 is ph = F + 32; every exit reloads s3 := F from NS_F0 and a6 := F from NS_FK.
   - UBSan: ONE `unimp` (0x81b64), reached by 12 guard branches (null / misaligned ps 0x816c4 0x816cc; ph + 4, 8, 12
     wraps 0x81794 0x817b4 0x817d8; null buf 0x819fc and buf + 12 .. 16 wraps 0x81a04 0x81a30 0x81a74 0x81a7c 0x81ad8;
     misaligned ts 0x81b24). Each is closed from the statement's premises (the table, section 6).
   - the header's four 32-bit words are read through rd_u32 (0x81c38; lib/B/Prog/RdU32.v), four calls 0x81788,
     0x817a8, 0x817c8, 0x817f0 with a0 = ph + 0, 4, 8, 12 and a1 = ps->swapped.
   - the code that hands a fitting record back (NP_fit .. NP_ts) lies after the epilogue; every exit of the open
     reader joins at NP_exit (0x818b4) with the result in a1, and the closed reader at NP_h0 (0x818c4). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
(* The shared statement, the model wrappers and the shared constants (see the header). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the machine frame ---- *)

Definition NX_MFRAME : Z := 256.          (* addi sp,sp,-0x100               0x815b8 *)
(* The realigned stack pointer that s1 holds for the whole body. *)
Definition nx_sp1 (sp0 : Z) : Z := 32 * ((sp0 - NX_MFRAME) / 32).
                                          (* andi sp,sp,-0x20 0x815f8; mv s1,sp 0x815fc *)
(* The frame header's second and third words: the address of the frame's description string "1 32 16 5 ph:53"
   (object 13 of this listing) and the function's own address (object 14). *)
Definition NX_DESCR : Z := Eval compute in (Symbols.AsanUbsan.Sec.s_rodata + 0x4c4a)%Z.  (* auipc a1,0xfff94 0x81670; addi a1,a1,-0x746 0x81684; sd a1,8(s3) 0x81690 *)
Definition NX_FNPC : Z := Eval compute in Symbols.AsanUbsan.s_pcap_source_next.  (* auipc a2,0 0x81674; addi a2,a2,-0xbc 0x81688; sd a2,0x10(s3) 0x81694 *)

(* The class-0 frame's data, all lib/A's values, at these lib/B instructions:
     NX_FREQ 64       addi a0,zero,0x40 0x8162c; jal __asan_stack_malloc_0 0x81634 (NX_CID 0)
     NX_MAGIC         lui a4,0x41b59 0x8166c; addiw a4,a4,-0x54d 0x81680; sd a4,0(s3) 0x8168c
     NX_RETIRED       lui a0,0x45e03 0x818cc; addiw a0,a0,0x60e 0x818d0; sd a0,0(s3) 0x818d4
     NX_FLAGPTR 56    ld a0,0x38(a6) 0x81900; sb zero,0(a0) 0x81904
     NO_PH 32         addi s3,s3,0x20 0x816f4
     NX_PH_LEN 16     addi a2,zero,0x10 0x81764
     NSH_entry        a1 = -8 0x81698 -> 4(s9), 5(s9) 0x816a0/0x816a4; a3 = -13 0x8167c -> 6(s9), 7(s9)
                      0x816a8/0x816ac; a1 = -15 0x816b0 -> 0(s9)..3(s9) 0x816b4..0x816c0
     NSH_ph           sb zero,4(s9) / 5(s9) 0x8174c, 0x81750 (the loop head)
     NSH_out          a0 = -8: 0x81858..0x81860 (NP_empty), 0x818b4..0x818bc (NP_exit)
     NSH_retired      a0 = -0xb 0x818dc; 0x818e0..0x818fc
     NSH_machine      0x8190c..0x81928 (not reached)
   The struct's offsets PS_*_OFF are lib/A's, at these lib/B accesses: f `ld a0,0(s5)` 0x816e4, 0x8175c, 0x81838,
   0x81994; swapped `lw a1,0(s11)` (s11 = ps + 8, 0x816f8) 0x81780, 0x817a0, 0x817c0, 0x817e8; orig `sw a0,0(a1)`
   0x8180c (a1 = ps + 12 from NS_PS12); vtag `sw zero,0x10(s5)` 0x819d0, `sw a3,0(a2)` 0x81a70 (a2 = ps + 16);
   vid `sh zero,0(a0)` 0x819f4, `sh a2,0(a0)` 0x81ad4 (a0 = ps + 20). *)

(* ---- the spill slots, as offsets from s1 ---- *)

Definition NS_OFF12 : Z := 24.    (* (ps + 12) mod 8 + 3:  sd a2,0x18(s1) 0x81748; read 0x81898 *)
Definition NS_OFF8 : Z := 32.     (* (ps + 8) mod 8 + 3:   sd a0,0x20(s1) 0x81734; read 0x81868..0x8188c *)
Definition NS_SB : Z := 40.       (* the shadow base:      sd a5,0x28(s1) 0x81738; read 0x819c0, 0x81a10, 0x81a3c,
                                     0x81a88, 0x81b08 *)
Definition NS_TS : Z := 48.       (* the caller's &ts:     sd s2,0x30(s1) 0x816ec; read 0x819ac, 0x81a58, 0x81b04,
                                     0x81b18 *)
Definition NS_SEC : Z := 56.      (* the record's ts_sec (rd_u32 of ph + 0), per record: sd s2,0x38(s1) 0x817e4;
                                     read 0x819e8. NOT in nslots. *)
Definition NS_F0 : Z := 64.       (* F:                    sd s3,0x40(s1) 0x816f0; read 0x818ac, 0x81974, 0x8198c,
                                     0x81a54, 0x81b00, 0x81b14 *)
Definition NS_SH12 : Z := 72.     (* shadow of ps + 12:    sd a1,0x48(s1) 0x81740; read 0x817f4 *)
Definition NS_PH12 : Z := 80.     (* ph + 12 = F + 44:     sd a0,0x50(s1) 0x81714; read 0x817ec *)
Definition NS_PS12 : Z := 88.     (* ps + 12:              sd a2,0x58(s1) 0x81724; read 0x81808, 0x818a0 *)
Definition NS_BUF : Z := 96.      (* buf:                  sd a1,0x60(s1) 0x81608 (prologue); read 0x81814,
                                     0x8199c, 0x819e4 *)
Definition NS_FK : Z := 104.      (* __asan_stack_malloc_0's result (F here): sd a0,0x68(s1) 0x816d0, before the
                                     closed reader's beqz 0x816e8; read 0x818a8, 0x818c8, 0x81970, 0x819a8,
                                     0x81a50, 0x81afc, 0x81b10 *)
Definition NS_PH8 : Z := 112.     (* ph + 8 = F + 40:      sd a0,0x70(s1) 0x8170c; read 0x817c4 *)
Definition NS_PH4 : Z := 120.     (* ph + 4 = F + 36:      sd a0,0x78(s1) 0x81704; read 0x817a4 *)
Definition NS_F1 : Z := 144.      (* F:                    sd s3,0x90(s1) 0x81668 (the frame join); never read,
                                     so no invariant carries it *)

(* ---- the stack this call needs ---- *)

(* Its own realigned frame is at most 272 bytes below the caller's sp (NX_MFRAME = 256, spZ regs mod 16 = 0, then
   the realignment to 32 bytes takes 0 or 16 more), and the deepest callee is the fread wrapper, AFREAD_STK = 8192
   (lib/A/Stdio/PFreadISpec.v, FROZEN), called with sp = sp1. rd_u32 takes RDU32_FRAME = 16 (lib/B/Prog/RdU32.v);
   __asan_memmove and __asan_stack_malloc_0 run in ESTACK = 4096 below the same sp. So the call uses at most
   272 + AFREAD_STK bytes below the caller's sp (the machine-stack frame arm 0x8164c..0x81664, which would use more,
   is not reached: the use-after-return flag is 1, AR_const_law).
   Depth: the caller's afn_pre gives astk_ok NX_STK_B ly sp0 with ly_bot = ly_top - 2 ^ 23 (YG0f.v:36, :63) and
   ASTACK = 16384 (YG0d.v:18), so the astk_ok conjunct this call's callees need is
   ly_top - sp1 < 2 ^ 23 + 16384 - AFREAD_STK, which follows from ly_top - spZ regs < 2 ^ 23 + 16384 - NX_STK_B and
   sp1 >= spZ regs - 272. *)
Definition NX_STK_B : Z := 272 + AFREAD_STK.

Lemma NX_STK_B_frame : forall sp0, sp0 mod 16 = 0 -> sp0 - 272 <= nx_sp1 sp0 <= sp0 - NX_MFRAME /\
  nx_sp1 sp0 mod 32 = 0.
Proof.
intros sp0 H. unfold nx_sp1, NX_MFRAME.
pose proof (Z.mul_div_le (sp0 - 256) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 256) 32 ltac:(lia)).
pose proof (Z.div_mod (sp0 - 256) 32 ltac:(lia)).
split; [split|]; [| lia | rewrite Z.mul_comm; apply Z.mod_mul; lia].
assert ((sp0 - 256) mod 32 = 0 \/ (sp0 - 256) mod 32 = 16) as [E|E].
{ assert (sp0 - 256 = 16 * ((sp0 - 256) / 16)) as E1.
  { pose proof (Z.div_mod (sp0 - 256) 16 ltac:(lia)).
    assert ((sp0 - 256) mod 16 = 0) by (rewrite Zminus_mod, H; reflexivity). lia. }
  rewrite E1. set (n := (sp0 - 256) / 16).
  pose proof (Z.mod_pos_bound n 2 ltac:(lia)). pose proof (Z.div_mod n 2 ltac:(lia)).
  replace (16 * n) with ((n / 2) * 32 + 16 * (n mod 2)) by lia.
  rewrite Z.add_comm, Z.mod_add by lia.
  assert (n mod 2 = 0 \/ n mod 2 = 1) as [M|M] by lia; rewrite M; [left | right]; reflexivity. }
all: lia.
Qed.

(* ---- the pcs of the phase cuts, as offsets in the lib/B listing (address - 0x80788) ---- *)

Definition NP_entry : Z := Eval compute in (Symbols.AsanUbsan.s_pcap_source_next - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x815b8, the first slot                                              *)
Definition NP_sm_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x80) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81638, __asan_stack_malloc_0 (0x81634) returned                     *)
Definition NP_frame : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0xb0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81668, the frame is taken (`sd s3,0x90(s1)`); both arms join here   *)
Definition NP_loop : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x194) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x8174c, the head of the record loop (back edge `j` 0x81864)          *)
Definition NP_hd_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x1b8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81770, the fread of the 16-byte header (0x8176c) returned           *)
Definition NP_rd0_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x1d4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x8178c, rd_u32 (ph + 0) (0x81788) returned: ts_sec                   *)
Definition NP_rd1_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x1f4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x817ac, rd_u32 (ph + 4) (0x817a8) returned: ts_usec                  *)
Definition NP_rd2_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x214) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x817cc, rd_u32 (ph + 8) (0x817c8) returned: incl; beqz -> NP_empty   *)
Definition NP_rd3_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x23c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x817f4, rd_u32 (ph + 12) (0x817f0) returned: orig                    *)
Definition NP_sk1 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x25c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x81814, cap < incl (the fall-through of bgeu 0x81810): s2 := buf,
                                       then beqz s7 0x81818, the `cap == 0` test                             *)
Definition NP_sk0 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x264) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x8181c, the head of the skip loop (back edge bnez 0x81854)           *)
Definition NP_sk_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x294) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.  (* 0x8184c, the fread of a skipped chunk (0x81848) returned              *)
Definition NP_empty : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x2a0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.  (* 0x81858, `ph` out of scope, then j NP_loop                            *)
Definition NP_slow : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x2b0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81868, the first slot of the slow-path block 0x81868..0x818a4      *)
Definition NP_xm1 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x2f0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x818a8, the -1 exit: a6 := FK, s3 := F, a1 := -1, into NP_exit       *)
Definition NP_exit : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x2fc) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x818b4, every exit of the open reader: a1 = the result, `ph` out     *)
Definition NP_h0 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x30c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x818c4, the closed reader: a1 := -1, a6 := FK, into NP_x0            *)
Definition NP_x0 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x314) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x818cc, the frame is given back                                      *)
Definition NP_epi : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x374) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x8192c, a0 := a1, then the epilogue                                  *)
Definition NP_ret : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x3b4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x8196c, the `ret`                                                    *)
Definition NP_eof : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x3b8) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x81970, the header read was short: a6, s3 reloaded, bnez a0          *)
Definition NP_fit : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x3d0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.    (* 0x81988, cap >= incl: the record is handed back                       *)
Definition NP_fit_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x3f0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x819a8, the fread of the record (0x819a4) returned                   *)
Definition NP_mm_ra : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.  (* 0x81af8, __asan_memmove (0x81af4) returned                            *)
Definition NP_ts : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x564) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x81b1c, beqz a7: the caller asked for no timestamp                   *)
Definition NP_trap : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x5ac) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81b64, the UBSan `unimp`, the target of every guard branch           *)
Definition NP_report : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x5b0) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z. (* 0x81b68, the first slot of the tail error region 0x81b68..0x81c34     *)

(* The cut pcs as addresses of the pin, and the calls the listing holds: checked once here against lib/B's
   PcapAddr.pcap_text and PcapList.pcap_listing. *)
Lemma NP_addrs :
  map (fun o => pcap_text + o)
    [NP_entry; NP_sm_ra; NP_frame; NP_loop; NP_hd_ra; NP_rd0_ra; NP_rd1_ra; NP_rd2_ra; NP_rd3_ra;
     NP_sk1; NP_sk0; NP_sk_ra; NP_empty; NP_slow; NP_xm1; NP_exit; NP_h0; NP_x0; NP_epi; NP_ret;
     NP_eof; NP_fit; NP_fit_ra; NP_mm_ra; NP_ts; NP_trap; NP_report] =
    [(symaddr Symbols.AsanUbsan.s_pcap_source_next); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x80)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0xb0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x194)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x1b8)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x1d4)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x1f4)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x214)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x23c)%Z);
     (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x25c)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x264)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x294)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x2a0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x2b0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x2f0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x2fc)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x30c)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x314)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x374)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x3b4)%Z);
     (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x3b8)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x3d0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x3f0)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x540)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x564)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x5ac)%Z); (symaddr (Symbols.AsanUbsan.s_pcap_source_next + 0x5b0)%Z)] /\
  NP_entry = AF_pcap_source_next /\ NP_entry + 0x680 = AF_rd_u32.
Proof. split; [reflexivity | split; reflexivity]. Qed.

(* The call sites, as listing offsets of their return addresses. *)
Definition NX_SM_SITE : Z := NP_sm_ra.                                  (* 0x81638 *)
Definition NX_FREAD_SITES : list Z := [NP_hd_ra; NP_sk_ra; NP_fit_ra].  (* 0x81770, 0x8184c, 0x819a8 *)
Definition NX_RD_SITES : list Z := [NP_rd0_ra; NP_rd1_ra; NP_rd2_ra; NP_rd3_ra].
                                                                        (* 0x8178c, 0x817ac, 0x817cc, 0x817f4 *)
Definition NX_MM_SITE : Z := NP_mm_ra.                                  (* 0x81af8 *)
Lemma NX_calls_listed :
  map (fun o => nth_error pcap_listing (Z.to_nat ((o - 4) / 4)))
    (NX_SM_SITE :: NX_MM_SITE :: NX_FREAD_SITES ++ NX_RD_SITES) =
  [Some (PCall PS___asan_stack_malloc_0 (1%bv : bv 5));
   Some (PCall PS___asan_memmove (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5));
   Some (PCall PS___interceptor_trampoline_fread (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5));
   Some (PCall PS_rd_u32 (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.
(* The UBSan trap is the listing's word 0xc0001073 (`unimp`). *)
Lemma NX_trap_listed : nth_error pcap_listing (Z.to_nat (NP_trap / 4)) = Some (PW 0xc0001073).
Proof. vm_compute. reflexivity. Qed.
(* The frame's two pin objects, the two GOT words and cells the prologue reads, and the callees. *)
Lemma NX_pin_values :
  pcap_obj 13 = NX_DESCR /\ pcap_obj 14 = NX_FNPC /\
  pcap_obj 0 = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xb8)%Z) /\ pcap_obj 1 = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z) /\
  pcap_obj 15 = (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address) /\ pcap_obj 16 = (symaddr Symbols.AsanUbsan.s___asan_option_detect_stack_use_after_return) /\
  pcap_sigma PS___asan_stack_malloc_0 = (symaddr Symbols.AsanUbsan.s___asan_stack_malloc_0) /\
  pcap_sigma PS___interceptor_trampoline_fread = (symaddr Symbols.AsanUbsan.s___wrap_fread) /\
  pcap_sigma PS___asan_memmove = (symaddr Symbols.AsanUbsan.s___asan_memmove) /\
  pcap_sigma PS_rd_u32 = (symaddr Symbols.AsanUbsan.s_rd_u32) /\ pcap_sigma PS_rd_u32 = pcap_text + AF_rd_u32.
Proof. repeat split; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* The phases of the walk (this build: segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi,       *)
(* nstk := NX_STK_B, of lib/B's PAImg)                                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* The call's context: everything the premises fix (lib/A's record, field for field). *)
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

(* The realigned stack pointer this call runs on, and the addresses of its own frame. *)
Definition n_sp1 (cx : ncx) : Z := nx_sp1 (spZ (n_regs cx)).
Definition nF (cx : ncx) (fp : Z) : Z := frame_addr (n_lyc cx) NX_CID fp.
Definition nFL (cx : ncx) (fp : Z) : Z := flag_addr (n_lyc cx) NX_CID fp.
Definition nSH (cx : ncx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (nF cx fp).

(* The chain this call hands to its callees (cgif lib/A/ACf5.v:128-131, PcapEntryDefs.pch). *)
Definition nx_ch (cx : ncx) : list (Z * Z * Z) :=
  if spZ (n_regs cx) + 16 <? ly_top (n_lyc cx)
  then (spZ (n_regs cx), raZ (n_regs cx), s0Z (n_regs cx)) :: n_ch cx else [].

(* What every phase may assume of the start: exactly the premises of tpcap_source_next_specX at segs := SEGS,
   rlo := pa_relro_lo, rhi := pa_relro_hi, nstk := NX_STK_B, in the same order, plus the atoms of the entry
   registers. *)
Definition nx_base (cx : ncx) : Prop :=
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (n_W cx)) (n_memc cx)) /\
  YK0s.ret_ok (getr (n_regs cx) 1) /\ 4096 <= raZ (n_regs cx) /\
  getr (n_regs cx) 3 = w64 (as_gp B) /\ getr (n_regs cx) 4 = w64 (as_tp B) /\
  getr (n_regs cx) 10 = w64 (n_ps cx) /\ getr (n_regs cx) 11 = w64 (n_buf cx) /\
  getr (n_regs cx) 12 = w64 (n_cap cx) /\ getr (n_regs cx) 13 = w64 (n_ts cx) /\
  spZ (n_regs cx) mod 16 = 0 /\ n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK_B /\
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
     nx_wr_ok NX_STK_B B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
       (spZ (n_regs cx)) (n_ps cx) PS_LEN) /\
  (n_h cx <> 0 ->
     In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B (n_lyc cx) (n_Sc cx)) /\
     4096 <= n_buf cx /\ n_buf cx + nx_bufn (n_cap cx) < 2 ^ 63 /\
     garr8 SEGS (rdW (n_W cx) (n_memc cx)) (n_buf cx) (n_bj cx) /\
     Z.of_nat (length (n_bj cx)) = nx_bufn (n_cap cx) /\
     0 <= n_cap cx <= NX_CAP_MAX /\
     nx_wr_ok NX_STK_B B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
       (spZ (n_regs cx)) (n_buf cx) (nx_bufn (n_cap cx)) /\
     (n_buf cx + nx_bufn (n_cap cx) <= n_ps cx \/ n_ps cx + PS_LEN <= n_buf cx)) /\
  (n_h cx <> 0 -> n_ts cx <> 0 ->
     val_mem SEGS (rdW (n_W cx) (n_memc cx)) (n_ts cx) 8 (n_tsv cx) /\ n_ts cx mod 8 = 0 /\
     4096 <= n_ts cx /\ n_ts cx + 8 <= 2 ^ 47 /\ amem_range (n_ts cx) 8 /\
     (exists tcid tpos, In (tcid, tpos) (n_own cx) /\ frame_addr (n_lyc cx) tcid tpos <= n_ts cx /\
        n_ts cx + 8 <= frame_addr (n_lyc cx) tcid tpos + fs_frame_bytes tcid) /\
     nx_wr_ok NX_STK_B B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_lyc cx) (n_Sc cx) (n_own cx)
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

(* The post of the whole call, in the shape tpcap_source_next_post asks, at nstk := NX_STK_B. *)
Definition nx_post (cx : ncx) : world SEGS -> config -> Prop :=
  tpcap_source_next_post SK SEGS NX_STK_B B MT KS
    (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx)
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx).

(* ---- the memory of a phase ---- *)

(* The shadow bytes of this call's own frame (s9 + 0 .. s9 + 7). *)
Definition nshadow (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + Z.of_nat i) = Some (nth i sh 0).

(* The frame's header as the prologue writes it (0x8168c..0x81694): the magic, then the listing's objects 13 and
   14 (NX_DESCR and NX_FNPC on the pin, NX_pin_values). *)
Definition nheader (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp) = Some NX_MAGIC /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + 8) = Some (pa_val (A_OBJ 13)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + 16) = Some (pa_val (A_OBJ 14)).

(* A spill slot of the machine frame. *)
Definition nslot (cx : ncx) (W3 : world SEGS) (ms3 : machine_state) (off v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx + off) = Some v.

(* The slots every phase of the open reader from the loop head on keeps (written at 0x81608 and 0x816d0 on every
   path, and at 0x816ec..0x81748 on the open reader's). NS_SEC is per record (each phase that needs it states it);
   NS_F1 is never read. *)
Definition nslots (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nslot cx W3 ms3 NS_FK (nF cx fp) /\
  nslot cx W3 ms3 NS_F0 (nF cx fp) /\
  nslot cx W3 ms3 NS_BUF (n_buf cx) /\
  nslot cx W3 ms3 NS_TS (n_ts cx) /\
  nslot cx W3 ms3 NS_SB SHADOW_OFF /\
  nslot cx W3 ms3 NS_PS12 (n_ps cx + PS_OL_OFF) /\
  nslot cx W3 ms3 NS_SH12 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_OL_OFF)) /\
  nslot cx W3 ms3 NS_OFF8 ((n_ps cx + PS_SW_OFF) mod 8 + 3) /\
  nslot cx W3 ms3 NS_OFF12 ((n_ps cx + PS_OL_OFF) mod 8 + 3) /\
  nslot cx W3 ms3 NS_PH4 (nF cx fp + NO_PH + 4) /\
  nslot cx W3 ms3 NS_PH8 (nF cx fp + NO_PH + 8) /\
  nslot cx W3 ms3 NS_PH12 (nF cx fp + NO_PH + 12).

(* The registers every phase of the body keeps: the realigned stack pointer in sp and s1, the entry stack pointer
   in s0, gp and tp. *)
Definition nregs (cx : ncx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (spZ (n_regs cx)) /\
  getr (ms_regs ms3) 9 = w64 (n_sp1 cx) /\
  getr (ms_regs ms3) 3 = getr (n_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (n_regs cx) 4.

(* The saved registers of the machine frame, which the epilogue reads back (0x815c0..0x815f0, 0x81934..0x81964):
   ra at sp0 - 8, then s0, s1, s2..s11 (the same places as lib/A's). *)
Definition nsaved (cx : ncx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 8) = Some (raZ (n_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (n_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* The slot's last word: __asan_stack_malloc_0 leaves the address of the slot's flag byte there (StackMalloc0.v:44,
   fframe_region PcapFrame.v); the epilogue stores 0 through it (`ld a0,0x38(a6); sb zero,0(a0)` 0x81900, 0x81904).
   Nothing in the body writes it. *)
Definition nflagw (cx : ncx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + NX_FLAGPTR) = Some (nFL cx fp).

(* What every state from the FK spill on carries (0x816d0 on, both readers): the pc (a listing offset), the machine
   state's fixed fields, the registers, the saved registers, the frame's header, flag word and shadow, s9 = the
   frame's shadow address (written 0x8169c, never after), and the slot NS_FK (0x816d0, before the closed reader's
   `beqz` 0x816e8; NP_h0 reads it). *)
Definition nx_body0 (cx : ncx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  nregs cx ms3 /\ nsaved cx W3 ms3 /\ nheader cx fp W3 ms3 /\ nflagw cx fp W3 ms3 /\
  nshadow cx fp W3 ms3 sh /\ length sh = NX_NSH /\
  getr (ms_regs ms3) 25 = w64 (nSH cx fp) /\
  nslot cx W3 ms3 NS_FK (nF cx fp).

(* ... and, from the spills 0x816ec..0x81748 on (the open reader), every slot of nslots. *)
Definition nx_body (cx : ncx) (fp : Z) (pc : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  nx_body0 cx fp pc W3 ms3 sh /\ nslots cx fp W3 ms3.

(* ---- a phase ---- *)

(* `nx_from POST GI`: from any machine state that `GI` describes, with the class-0 frame taken at slot fp, the run
   reaches POST. A phase lemma has the shape `nx_from POST GI_next -> nx_from POST GI_self`. *)
Definition nx_from (POST : ncx -> world SEGS -> config -> Prop)
  (GI : ncx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ncx) (fp k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  nx_base cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  GI cx fp k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* The whole call: from the function's first slot under `nx_base` to the same post-condition. *)
Definition nx_start (POST : ncx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : ncx, nx_base cx ->
  SRr SEGS (n_W cx)
    (mkCfg (mkst (n_regs cx) (w64 (BASE + NP_entry)) (n_memc cx) (seg_rom SEGS)) (n_mdc cx))
    (POST cx).

(* ---- the shared middle state ---- *)

(* The journal's bookkeeping at every cut after the frame is taken. *)
Definition nx_jbk (cx : ncx) (k2 : Z) (ly3 : alayout) (S3 : astate) (md3 : Model) : Prop :=
  k2 = n_k cx + EV_NEXT /\
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) /\
  mo_le MT (n_Sc cx) S3 0 /\
  m_fds md3 = m_fds (n_mdc cx) /\ m_fs md3 = m_fs (n_mdc cx).

(* The caller's bytes the call may write (the post's set). *)
Definition nx_E (cx : ncx) : Z -> Prop := nx_wrset (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx).

(* The struct's orig field for the last non-empty header lh (0x8180c writes it; an empty record leaves it). *)
Definition nx_ol (cx : ncx) (lh : option Z) : Z :=
  match lh with Some q0 => PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q0 | None => n_lol cx end.

(* nx_mid: the facts every cut of the open reader after the spills shares (NP_loop .. NP_ts). Parameters as
   lib/A's: pc and sh (the cut's pc and the frame's shadow); E (the caller's bytes written so far, inside nx_E);
   q (the stream's position); ol vt vid (the struct's orig / vtag / vid fields now); tv (the timestamp cell's value
   now, when ts <> 0); then the state as nx_from takes it.
   Registers: the four that no instruction after the spills writes: s5 = ps (0x81624), s7 = cap (0x81604),
   s10 = the shadow address of ps (0x816d8), s11 = ps + 8 (0x816f8). The others differ per cut (s3 = F + 32 until
   the exits reload F; s4 = the shadow address of ps + 8 until 0x819e4; s2 / s6 / s8 per record): each phase states
   its own. *)
Definition nx_mid (cx : ncx) (fp pc : Z) (sh : list Z) (E : Z -> Prop) (q ol vt vid tv : Z)
  (k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body cx fp pc W3 ms3 sh /\
  getr (ms_regs ms3) 21 = w64 (n_ps cx) /\ getr (ms_regs ms3) 23 = w64 (n_cap cx) /\
  getr (ms_regs ms3) 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) /\
  getr (ms_regs ms3) 27 = w64 (n_ps cx + PS_SW_OFF) /\
  nx_jbk cx k2 ly3 S3 md3 /\
  (* the caller's memory: kept outside the stack window and E *)
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx)) E /\
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

(* The loop invariant of the record loop (NP_loop, 0x8174c). `q` is the position in the file this turn starts at
   and `lh` the last non-empty record header seen so far (the model's `lh`). The shadow is NSH_entry: 0x8174c /
   0x81750 themselves put `ph` in scope, and both edges into the head (the prologue, and NP_empty 0x81858..0x81864)
   have it out of scope. Registers: s3 = ph = F + 32 (0x816f4), s4 = the shadow address of ps + 8 (0x8172c); s2, s6,
   s8 are dead here (each written before any read in the turn). The chain clause is nx_chain_inv. *)
Definition nx_loop_inv (cx : ncx) (fp q : Z) (lh : option Z)
  (k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_mid cx fp NP_loop NSH_entry (nx_E cx) q (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) /\
  getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh.

(* The record loop by well-founded induction (the top, PcapSourceNext.v), as lib/A's. *)
Definition nx_next_ok (R : ncx -> Z -> Prop) (cx : ncx) (q : Z) : Prop :=
  forall q', q < q' <= Z.of_nat (length (n_C cx)) -> R cx q'.
Definition nx_loop_at (R : ncx -> Z -> Prop) :
  ncx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k2 ly3 S3 W3 ms3 md3 => exists q lh, R cx q /\ nx_loop_inv cx fp q lh k2 ly3 S3 W3 ms3 md3.

(* ---- the end of the body ---- *)

(* The post's final memory and a0, for this call's context. *)
Definition nx_fin_at (cx : ncx) (W3 : world SEGS) (mem3 : word -> option byte) (r : word) : Prop :=
  nx_fin SEGS NX_STK_B B KS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (spZ (n_regs cx))
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx) W3 mem3 r.

(* NP_exit (0x818b4, `ph` still in scope): every path of the open reader that ends the call (NP_eof, NP_sk1 with
   cap = 0 and a short chunk through NP_xm1, a short record from NP_fit_ra, NP_ts) arrives here with the result in
   a1, s3 = F and a6 = F reloaded from NS_F0 / NS_FK, and the caller's memory final. *)
Definition nx_exit_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body cx fp NP_exit W3 ms3 NSH_ph /\
  getr (ms_regs ms3) 19 = w64 (nF cx fp) /\ getr (ms_regs ms3) 16 = w64 (nF cx fp) /\
  nx_jbk cx k2 ly3 S3 md3 /\
  nx_fin_at cx W3 (ms_mem ms3) (getr (ms_regs ms3) 11).

(* NP_x0 (0x818cc, `ph` out of scope, shadow NSH_entry): both readers. The closed reader comes from NP_h0 (0x818c4,
   a1 := -1, a6 := NS_FK) right after the `beqz` 0x816e8, before the spills, with s3 = F (0x81644, not written on
   that path); the open reader from NP_exit. *)
Definition nx_x0_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  nx_body0 cx fp NP_x0 W3 ms3 NSH_entry /\
  getr (ms_regs ms3) 19 = w64 (nF cx fp) /\ getr (ms_regs ms3) 16 = w64 (nF cx fp) /\
  nx_jbk cx k2 ly3 S3 md3 /\
  nx_fin_at cx W3 (ms_mem ms3) (getr (ms_regs ms3) 11).

End c.
End b.
End a.

(* SK is explicit at every use: the closure's only global sink_head instance is the PLAIN build's
   (lib/Reusable/YI5b.v:12), so an inferred SK would make the stream facts vacuous (a Theorem Labs lane 21:57Z). *)
Arguments nx_base {rc} SK {PI}.
Arguments nx_post {fx rc} SK {PI}.
Arguments nx_from {rc} SK {PI}.
Arguments nx_start {fx rc} SK {PI}.

(* GUARD: SK is passed by position; were it implicit again, these lines would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
  (B : asyms) (MT : ameter_ops) (KS : asource_syms) =>
  (@nx_start fx rc SK PI B KS (@nx_post fx rc SK PI B MT KS) : Prop)).
