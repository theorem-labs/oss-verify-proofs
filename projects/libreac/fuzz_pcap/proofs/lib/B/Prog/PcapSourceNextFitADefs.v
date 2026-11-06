(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 23 of its 54 lines of code are new or changed and 3526 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the ASan+UBSan
   build of libreac v1.9.0: the entry predicate of the fit phase at NP_fit (listing offset 0x1200, address 0x81988),
   where the header of a record that the buffer can hold (0 < incl <= cap) has been read. The phase itself
   (0x81988 .. NP_ts 0x81b1c / NP_exit 0x818b4; on this image the path lies after the epilogue) is walked in
   lib/B/Prog/PcapSourceNextFitA.v. lib/A's twin of this predicate is lib/A/Prog/PcapSourceNextFitADefs.v.

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols from its unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59),
   capstone 5; slot table nxb-handoff.md (sha256 c02dc85fade1; internal record)).

   WHAT THE HEADER PHASE LEAVES AT 0x81988 (`bgeu s7,s2` 0x81810 taken: cap >= incl):
     s2           incl, zero-extended          `slli a1,s6,0x20; srli s2,a1,0x20` 0x81800, 0x81804
     s6           incl as rd_u32 returned it   `mv s6,a0` 0x817d0 (sign-extended 32 bits; incl <= cap <= 2040)
     s8           the record's ts_usec         `mv s8,a0` 0x817ac (rd_u32 of ph + 4; its low word is read)
     NS_SEC       the record's ts_sec          `sd s2,0x38(s1)` 0x817e4 (rd_u32 of ph + 0; its low word is read)
     ps->orig     the record's orig_len        `sw a0,0(a1)` 0x8180c (rd_u32 of ph + 12, through NS_PS12)
   and nx_mid's registers s5 = ps, s7 = cap, s10 = the shadow address of ps, s11 = ps + 8. The stream stands after
   the 16-byte header (q + 16); `ph` is in scope (NSH_ph). s3 (ph), s4 and the a / t registers are not read before
   they are written on the fit path (s3 := F at 0x8198c, s4 := buf at 0x819e4). *)
(* Modified by Theorem Labs, 2026-10: the lib/B twin of lib/A/Prog/PcapSourceNextFitADefs.v (a working branch
   b5b98d94ebb): the cut, the registers and the slot are lib/B's (NP_fit 0x1200; s2 / s6 / s8 and NS_SEC instead of
   lib/A's header bytes in a2 .. a5 and s9 / s11), over lib/B's nx_mid. *)
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
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* THE ENTRY PREDICATE AT NP_fit (0x81988). q is the position of the record in the file: the model's final position
   (nx_q), with the record's header the last non-empty one (nx_lh = Some q). Its header has been read, so the stream
   stands at q + 16; its incl is not 0 and the buffer can hold it (incl <= cap). ps->orig holds the record's
   orig_len; ps->vtag, ps->vid and ts are the caller's. The middle state is lib/B's nx_mid at NP_fit with `ph` in
   scope. The two halves of the timestamp are stated by their low words: the code reads only those (`slli a1,s2,0x20`
   0x81b3c after `ld s2,0x38(s1)` 0x819e8, `slli s8,s8,0x20` 0x81b40). *)
Definition nx_fit_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  let sw := (n_sw cx =? 1) in
  let F := nxF (n_C cx) in
  let R := ms_regs ms3 in
  exists q : Z,
  nx_mid B MT KS cx fp NP_fit NSH_ph (nx_E cx) (q + 16) (PSN.orig sw F q) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
  (* the model: the record q *)
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q /\
  nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q /\
  n_p cx <= q /\
  0 < PSN.incl sw F q <= n_cap cx /\
  (* the registers and the slot (s5, s7, s10, s11 are nx_mid's) *)
  getr R 18 = w64 (PSN.incl sw F q) /\                                  (* s2: incl, zero-extended *)
  getr R 22 = w64 (PSN.incl sw F q) /\                                  (* s6: incl (< 2 ^ 31) *)
  bv_unsigned (getr R 24) mod 2 ^ 32 = PSN.hw sw F q 4 /\               (* s8: ts_usec *)
  (exists v, nslot cx W3 ms3 NS_SEC v /\ v mod 2 ^ 32 = PSN.hw sw F q 0). (* NS_SEC: ts_sec *)

End c.
End b.
End a.

(* nx_fit_inv names no sink head (asource_at takes none), so SK is not among its binders: its arguments are
   {fx rc} {PI} B MT KS and the eight of a phase predicate (fx: nx_body0 states the floating-point state). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) => @nx_fit_inv fx rc PI B MT KS).
