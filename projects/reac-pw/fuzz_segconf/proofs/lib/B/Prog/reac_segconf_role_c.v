(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 35 of its 56 lines of code are new or changed and 146 lines of the source are left out. *)
(* reac_segconf_role (reac_segconf.c:533-541; fuzz_segconf.asan 0x895f0, 200 bytes, 50 instructions; frame 32
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_role_c.v:11-53, restated over the ASan
   reader; its role_pre (:27-29) and its write list role_W (:31-36) keep their names here.
   What the code does (objdump of fuzz_segconf.asan, 0x895f0-0x896b4): s0 = out (0x89600); s =
   reac_segconf_find(c, name) (jal 0x89610); 0 when s is 0 or s->role_set = 0 (lw of s + 0x14 at 0x89630); else
   1, and when out <> 0 it loads s->role (lw of s + 0x10 at 0x89660) and stores it at out (sw at 0x89668). The
   post is the plain one: a0 = 1 and the 4 bytes at out hold r when r_role rcs nm = Some r (out <> 0); a0 = 0
   when it is None.
   What it reads: the shadow base (the GOT word as_got_shadow B, image A 0xa2a50, loaded at 0x89604-0x8960c before
   the call; AR_const_law), what find reads, and the role_set and role words of the entry found. What it
   writes: its own frame and find's, inside its stack window, and the 4 bytes at out exactly when it returns 1
   with out <> 0, so its footprint is role_W out (r_role rcs nm), the plain write list without its stack
   interval, in the same order. No abort site (segA/evidence/program.asan.tsv line 26).
   Premise: role_pre, which is query_pre of lib/A/Prog/reac_segconf_find_c.v (the one find asks) and the out
   cell. NAME PREMISE: sa_str, not sa_strz: the only reader of the name is find, which hands it to strcmp, and
   row 17's RtString.astrcmp_realizes asks the slack after the NUL (atail_vis; see reac_segconf_find_c.v).
   ASAN FACTS ADDED over the plain contract (s = c + 356 i with i < length (rc_seg rcs) <= 32, by find's post
   seg_spec.find_ptr and seg_spec.rconf_enc, so every field of s lies in the block):
   - inline check 1, load4 of s->role_set at s + 0x14 (shadow test 0x8961c-0x89688, error arm
     __asan_report_load4 at 0x8968c): killed by query_pre's sa_addr rd c SEG_C_SIZE.
   - inline check 2, load4 of s->role at s + 0x10 (shadow test 0x89640-0x89698, error arm __asan_report_load4
     at 0x896a0): killed by the same sa_addr.
   - inline check 3, store4 at out (shadow test 0x89654-0x896ac, error arm __asan_report_store4 at 0x896b4):
     killed by role_pre's sa_dst segs B ly S W mem regs out 4, in its side-stack-frame and heap arms by their
     range_addressable, in its real-stack arm by AR's zshadow_ok over [ly_stk_lo, ly_stk_hi) (lib/Reusable/YG0n.v
     :188-191), as fuzz_command's number_c.v states its out. The plain wr_at / apart conjuncts become sa_dst.
   - find's facts (its load4 of c->n, strcmp's two ranges, rt_rom_view from arodata_okP segs RLO RHI B rd):
     query_pre and arodata_okP, handed to find unchanged, with the same RLO RHI.
   - no side-stack frame and no printf: apost_base, EV_reac_segconf_role = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK (fun a => out <> 0 /\ out <= a < out + 4) in the post (SegABase.v's
     sa_kept, found by the G4 / G5 walk of check_absent: the journal keeps no shadow of an image object). True of
     the code: its stores are ra, s0, s1 into its frame (0x895f4-0x895fc) and the sw at out (0x89668, only when
     out <> 0, so the set is exactly role_W's cell); it takes no side-stack frame and calls no set_shadow entry;
     find's post gives the same clause over find's window, which lies in this one when
     STK >= 32 + STK_reac_segconf_find. The `out <> 0` guard (CONTRACT STOP #4, the G4 / G5 walk of check_absent,
     accepted by the image-A owner 2026-10-30): without it, at out = 0 - check_absent's call 0x87614, `li a2,0` at
     0x87610 - the excepted set was [0, 4) and the post said nothing of bytes 0..3, which check_absent's own
     keep clause (fun _ => False) could then not cover.
   The stored value: the plain post's bytes_at m' out (le4 (Z_to_bv 64 v)) is stated as sa_val rd' out 4 v
   (SegABase's form of a 4-byte cell; the same bytes, since 0 <= v < 2 ^ 31 by seg_spec.role_enc).
   Call sites (segA/evidence/callsites.asan.tsv lines 21, 208): LLVMFuzzerTestOneInput 0x85508 (c, g->name,
   a2 = ld 96(s1), the word main stored at 0x84fbc: s3 + 176 with s3 = a7, main's ASan frame base, its class-3
   side-stack frame or the real-stack fallback, mv s3,a7 at 0x84efc); check_absent 0x87614 (c, the probe, out = 0:
   li a2,0 at 0x87610); no constant argument in the tsv's a0 / a1 columns at either.
   image A: A_reac_segconf_role = 0x895f0; STK_reac_segconf_role = 32 + STK_reac_segconf_find =
   32 + 32 + 2 * ESTACK (INFERENCE: its frame above find's window); RLO = 0xa14a0 (.data.rel.ro start),
   RHI = 0xa3748 (.got end), the one pair this unit uses, as SegGlob.SEG_RLO / SEG_RHI has it (the listing lane,
   2026-10-30; the earlier 0xa1468 / 0xa4000 here was the whole PT_GNU_RELRO and was wrong).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_role, STK_reac_segconf_role, RLO, RHI and every
   image cell are parameters (or fields of B).
   The WALK takes as Section hypotheses: reac_segconf_find_contract (lib/A/Prog/reac_segconf_find_c.v) at find's
   entry and stack. It calls no runtime entry itself (find's walk takes RtString.astrcmp_realizes, row 17 of
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626), accepted v1 5e0b8a44fdc;
   at e45889d6935a strcmp is that file's DECISION 2, option (b)). They are NOT premises of this contract: the
   statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/reac_segconf_role_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the plain role_pre over the reader: find's query_pre, and out is 0 or a 4-aligned cell the call may write
   (sa_dst: a side-stack frame or a heap block with its shadow addressable, or a slot of the caller's real stack
   above the entry sp). Outside the sections: role_pre segs B ly S W mem regs c name out rcs nm.
   This call is why sa_dst's real-stack arm carries astack_pres (lib/A/Prog/SegABase.v, the comment on sa_dst;
   found by the G4 / G5 walk of reac_segconf_role, 2026-10-30): the code keeps out in s0 (0x89600 `mv s0,a2`) across
   `jal reac_segconf_find` (0x89610), and find's afn_pre asks `achain ly rd (sp - 32) s0 ch`
   (lib/Reusable/YCbq.v:264), which for a real-stack out needs the words at out - 8 and out - 16 readable,
   where sa_dst's arm had made only [out, out + 4) present. The fix is in the base, not here, so the premise
   has one source; this text is unchanged. *)
Definition role_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word)
(c name out : Z) (rcs : rconf) (nm : list Z) : Prop :=
query_pre segs B ly S (aview segs (w_H W) mem) c name rcs nm /\
(out = 0 \/ (out mod 4 = 0 /\ sa_dst segs B ly S W mem regs out 4)).
(* the plain role_W without its stack interval [sp - ROLE_STACK, sp), which apost_base's window covers: the out
   cell when the call stores, else nothing *)
Definition role_W (out : Z) (o : option Z) : list (Z * Z) :=
match o with
| Some _ => if out =? 0 then [] else [(out, out + 4)]
| None => []
end.
(* the events this call spends: 0, it reaches no allocator entry (nor does find) *)
Definition EV_reac_segconf_role : Z := 0.
Definition reac_segconf_role_contract (A_reac_segconf_role STK_reac_segconf_role RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name out : Z) (rcs : rconf) (nm : list Z),
afn_pre segs B STK_reac_segconf_role ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
getr regs 12 = w64 out -> 0 <= out < 2 ^ 64 ->
role_pre ly S W mem regs c name out rcs nm ->
st_nev S + EV_reac_segconf_role <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_role regs mem md)
(apost_base segs B STK_reac_segconf_role (role_W out (r_role rcs nm)) regs ly S W mem md
EV_reac_segconf_role
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (match r_role rcs nm with Some _ => 1 | None => 0 end) /\
 (match r_role rcs nm with
  | Some v => out <> 0 -> sa_val (aview segs (w_H W') mem') out 4%nat v
  | None => True
  end) /\
 sa_kept segs W mem W' mem' regs STK_reac_segconf_role (fun a => out <> 0 /\ out <= a < out + 4) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
