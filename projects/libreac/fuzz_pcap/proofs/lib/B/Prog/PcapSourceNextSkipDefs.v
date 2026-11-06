(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 101 of its 135 lines of code are new or changed and 546 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNext.v, with its module paths and module names changed; 37 of its 72 lines of code are new or changed and 100 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the entry predicates
   of the skip phase (lib/B/Prog/PcapSourceNextSkip.v), over lib/B's shared middle state nx_mid
   (lib/B/Prog/PcapSourceNextDefs.v).

   NP_sk1 (0x81814, listing offset 0x108c) is reached from the header phase (a Theorem Labs lane) when the record at q is longer
   than the caller's buffer: the header fread returned 16 (`bne a0,a1` 0x81774 not taken, so q + 16 <= |C| and the
   stream is at q + 16), the four rd_u32 calls returned the header's words, incl (the third, 0x817c8) is not 0
   (`beqz a0` 0x817cc not taken), s6 := incl (`mv s6,a0` 0x817d0), ps->orig := orig (`sw a0,0(a1)` 0x8180c), and
   cap < incl (`bgeu s7,s2` 0x81810 not taken, s2 = incl zero-extended, 0x81800 / 0x81804). The model's kind of the
   record is then KBig0 (cap = 0), KBig or KCutBig.

   NP_sk0 (0x8181c, listing offset 0x1094) is the head of the skip loop: r bytes of the record are still to read, the
   stream is at q + 16 + incl - r, s2 = buf (`ld s2,0x60(s1)` 0x81814) and s6's low word is r (`subw s6,s6,s8`
   0x81850 keeps it).

   Registers at both cuts besides nx_mid's (s5 = ps, s7 = cap, s10 = the shadow address of ps, s11 = ps + 8):
   s3 = ph = F + 32 (0x816f4; the loop head NP_loop needs it back), s4 = the shadow address of ps + 8 (0x8172c; the
   loop head needs it back), and s6, whose low 32 bits are the bytes still to read. s6 may carry a sign extension
   above them (rd_u32's 32-bit result in a0, `mv s6,a0` 0x817d0; `subw` 0x81850); every use reads the low word
   (`slli a0,s6,0x20; srli a0,a0,0x20` 0x8181c / 0x81820, and `bnez s6` 0x81854 right after the `subw`).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image (sha256
   9e66f771f22af67a...; capstone 5 disassembly of the unstripped twin:
   nxb-next.dis (sha256 7213b94e2690; internal record), table nxb-handoff.md (sha256 c02dc85fade1; internal record)). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* The model's incl of the record at q, for this call's stream and byte order. *)
Definition nx_incl (cx : ncx) (q : Z) : Z := PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q.

(* What both cuts of the skip phase share, for the record at q with r bytes still to read: the turn's start q is
   one the record loop may go on from (nx_next_ok R), the model's chain clause at q, the header facts
   (q + 16 <= |C|, incl <> 0, cap < incl), the middle state at pc with `ph` in scope, the stream at
   q + 16 + incl - r, ps->orig = orig q (nx_ol (Some q)), vtag / vid / ts the caller's, and the registers s3, s4, s6
   (the header). *)
Definition nx_skip_at (R : ncx -> Z -> Prop) (pc r : Z)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  exists q lh,
    nx_next_ok R cx q /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh /\
    q + 16 <= Z.of_nat (length (n_C cx)) /\
    nx_incl cx q <> 0 /\ n_cap cx < nx_incl cx q /\
    0 < r <= nx_incl cx q /\
    nx_mid B MT KS cx fp pc NSH_ph (nx_E cx) (q + 16 + nx_incl cx q - r) (nx_ol cx (Some q))
      (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) /\
    getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\
    bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = r.

(* NP_sk1 (0x81814, the fall-through of `bgeu s7,s2` 0x81810): the whole record is still to read (r = incl), the
   stream is at q + 16. *)
Definition nx_sk1_inv (R : ncx -> Z -> Prop)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  exists q lh,
    nx_next_ok R cx q /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh /\
    q + 16 <= Z.of_nat (length (n_C cx)) /\
    nx_incl cx q <> 0 /\ n_cap cx < nx_incl cx q /\
    nx_mid B MT KS cx fp NP_sk1 NSH_ph (nx_E cx) (q + 16) (nx_ol cx (Some q))
      (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) /\
    getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\
    bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = nx_incl cx q.

(* NP_sk0 (0x8181c), the skip loop's invariant: r bytes still to read, 0 < cap (the `beqz s7` at 0x81818 was not
   taken), s2 = buf (0x81814). The loop is proved by induction on r. *)
Definition nx_sk0_inv (R : ncx -> Z -> Prop) (r : Z)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  n_cap cx <> 0 /\ getr (ms_regs ms3) 18 = w64 (n_buf cx) /\
  nx_skip_at R NP_sk0 r cx fp k2 ly3 S3 W3 ms3 md3.

End c.
End b.
End a.

(* The skip predicates name no sink head (nx_mid takes none), so SK is not among their binders. GUARD: their
   arguments are {fx} {rc} {PI} B MT KS, the loop measure R (and r), and the eight of a phase predicate. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) (R : ncx -> Z -> Prop) =>
  (@nx_sk1_inv fx rc PI B MT KS R, @nx_sk0_inv fx rc PI B MT KS R 1)).
