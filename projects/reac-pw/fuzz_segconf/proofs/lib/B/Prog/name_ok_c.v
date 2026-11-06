(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 25 of its 45 lines of code are new or changed and 147 lines of the source are left out. *)
(* name_ok (reac_declared_vlan.c:20-30, static; fuzz_segconf.asan 0x89d58, 244 bytes, 61 instructions; frame 64
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/name_ok_c.v:10-49 (name_ok_pre :33-35, the return value
   :43, the write list :45), restated over the ASan reader. The post is the plain one: a0 = b2z (SegModel.name_ok
   nm) for the C string nm at s.
   What the code does (objdump of fuzz_segconf.asan, 0x89d58-0x89e48): the C test of a NULL s is gone, as in the
   plain build (the premise is s <> 0); lbu of s[0] at 0x89d94 and 0 for the empty string; the loop (0x89dbc ..
   bnez 0x89df8) calls musl's isalnum on the byte (zext.b, jal 0x901a0 at 0x89dc0) and, when it answers 0, accepts
   only the bytes 0x2d 0x2e 0x3a 0x5f (s3 = 50 and the bit test of s4 = 2^50 + 2^13 + 3, 0x89dc8-0x89dd8), else
   returns 0; at the NUL it returns 1.
   What it reads: the shadow base through the GOT word as_got_shadow B (image A 0xa2a50, which holds 0xabff8, the
   cell as_shadow_cell B; AR's const law gives both, so the contract names neither); the bytes of s up to its NUL,
   one at a time (lbu, no slack). What it writes: its own frame only, so its footprint is [] (the plain write list
   :45 is its frame). No abort site (segA/evidence/program.asan.tsv line 32).
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load1 of s[0] at 0x89d94 (shadow test 0x89d84-0x89d90, slow path 0x89e40, error arm
     __asan_report_load1 at 0x89e48), and inline check 2, load1 of s[k], k >= 1, at 0x89dec (shadow test
     0x89ddc-0x89de8, slow path 0x89e00, error arm __asan_report_load1 at 0x89e0c): both killed by name_ok_pre's
     sa_addr rd s (length nm + 1).
   - where s lies: sa_dst, the place form of reac_declared_vlan_split's parent buffer, which split has just
     written (memcpy and the NUL store) and hands over: a side-stack frame or a heap block, each addressable, or a
     slot of the caller's real stack above this sp. Every arm keeps the string outside this call's stack window,
     which is the plain apart premise (:34); the plain stack_ok and mem_inv are afn_pre's.
   - arodata_okP over the read-only window RLO RHI: NOT needed by row 9 - its accepted text,
     RtSeg.aisalnum_realizes (commit 80d098bd1905, lib/A/Rt/RtSeg.v:140), asks no read-only
     view, since musl's isalnum reads no memory (the interceptor lane's review, O2). It stays in the statement
     because the one caller carries the same premise, so it costs no caller anything; dropping it would be a
     statement change.
   - sa_kept segs W mem W' mem' regs STK_name_ok (fun _ => False) in the post: every byte outside the stack window
     reads as at the entry, the shadow of an image object included, which the journal alone does not keep
     (SegABase.v's sa_kept, found by the G4 / G5 walks). True of the code: it
     takes no side-stack frame and calls no set_shadow entry (segA/evidence/program.asan.tsv line 32,
     callsites.asan.tsv lines 382-384); its only stores are the saved registers in its frame (0x89d5c-0x89d74);
     musl's isalnum (0x901a0-0x901b8) is seven register instructions, no load, no store, no stack.
   - no side-stack frame and no printf: apost_base, EV_name_ok = 0, post tail sa_noalloc.
   Call site (segA/evidence/callsites.asan.tsv line 378): reac_declared_vlan_split 0x89d08 with a0 = parent, which
   then holds firstn plen segment and its NUL (plen <= 15).
   image A: A_name_ok = 0x89d58; STK_name_ok = 64 + ESTACK (row 9's window; musl's isalnum at 0x901a0 is a 28-byte
   leaf that uses no stack).
   IMAGE-INDEPENDENT: no image module is Required; A_name_ok, STK_name_ok, RLO, RHI and every image cell are
   parameters (or fields of B).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); row 9 accepted at 80d098bd1905):
     RtSeg.aisalnum_realizes (pc) (row 9, lib/A/Rt/RtSeg.v:140), at musl's isalnum (image A 0x901a0; a direct
       call, not intercepted).
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/name_ok_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What name_ok asks of its caller (the plain name_ok_pre, lib/Prog/name_ok_c.v:33-35, over the reader
   rd = aview segs (w_H W) mem): s is the C string nm with its NUL (sa_strz: the loop reads byte by byte, no slack),
   its bytes and NUL addressable, in the place split's parent buffer has (sa_dst; regs are this call's entry
   registers). Outside the sections: name_ok_pre segs B ly S W mem regs s nm. *)
Definition name_ok_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (s : Z) (nm : list Z) : Prop :=
s <> 0 /\ sa_strz (aview segs (w_H W) mem) s nm /\
sa_addr (aview segs (w_H W) mem) s (Z.of_nat (length nm) + 1) /\
sa_dst segs B ly S W mem regs s (Z.of_nat (length nm) + 1).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_name_ok : Z := 0.
Definition name_ok_contract (A_name_ok STK_name_ok RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s : Z) (nm : list Z),
afn_pre segs B STK_name_ok ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 s -> 0 <= s < 2 ^ 64 ->
name_ok_pre ly S W mem regs s nm ->
st_nev S + EV_name_ok <= EV_MAX ->
SRr segs W (cfg_at segs A_name_ok regs mem md)
(apost_base segs B STK_name_ok [] regs ly S W mem md EV_name_ok
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.b2z (SegModel.name_ok nm)) /\
 sa_kept segs W mem W' mem' regs STK_name_ok (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
