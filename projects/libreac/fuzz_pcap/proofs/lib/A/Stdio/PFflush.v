(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fflush on libreac/fuzz_pcap's fmemopen READ stream.

   STATEMENT ONLY: the definitions compile, there is no lemma yet.

   Donor: cgif_file_fuzzer lib/A/AE29.v:616 fflush_real (donor sha c8557374ad2e), which walks the SAME
   interceptor and musl code -- masked-equal on pcap (icpt_fflush 67/67 insns, musl fflush 92/92,
   a Theorem Labs lane's runtime-donors.md (sha256 77e6fad19fb7; internal record) rows 5-6) -- but only for a WRITE stream over __stdio_write. The
   read-stream branch is not covered there, and that branch is this file.

   IMAGE ROOT: the ORIGINAL v1.9.0 set, which is what the statements target --
   the pinned fuzz_pcap images, unstripped twins fuzz_pcap.asan (sha256 36da3052c383) and
   fuzz_pcap.asan-ubsan (sha256 c969d83cdd59), statements ed6b6b7b0ab. NOT the toolchain-N images: a runtime premise
   true on one can be false on the other (another proof's
   malloc_context_size = 1 is exactly such a premise, true on N and false here).

   musl fflush(f), 0x8e43c, 92 instructions, READ OFF pcap's v1.9.0 ASan image:
     0x8e450  f = 0 selects the all-streams path (0x8e470); not this spec
     0x8e458  a0 = f->lock        -- lw from +140
     0x8e45c  lock < 0 -> s2 = 1, NO __lockfile call; else __lockfile(f)
     0x8e490  wpos = f->wpos (+40), wbase = f->wbase (+56)
     0x8e498  wpos = wbase -> skip the write flush entirely
              else f->write(f, 0, 0) through +72, and f->wpos = 0 afterwards means error
     0x8e4b8  rpos = f->rpos (+8), rend = f->rend (+16)
     0x8e4c0  rpos = rend -> skip the seek
              else f->seek(f, rpos - rend, SEEK_CUR) through +80          <-- the read branch
     0x8e4d8  s0 = 0
     0x8e4dc  f->wbase = 0 ; f->rpos = 0 ; f->rend = 0 ; f->wend = 0 ; f->wpos = 0
     0x8e4f0  unlock if it locked; return 0

   TWO FACTS FROM PSource.v MAKE THIS BRANCH DETERMINISTIC, which is why those fields are in the
   predicate rather than at the call site:
     - source_static pins the lock word at +140 to -1 (U32M1), so the `bltz` at 0x8e45c is TAKEN and
       the __lockfile / __unlockfile calls do not happen;
     - source_static pins wpos (+40) and wbase (+56) both to 0, so the test at 0x8e498 is equal and the
       write branch -- the whole of cgif's fflush_real -- is skipped. A read stream never calls
       f->write, which is why mwrite is only stored, never invoked.

   The seek offset is `rpos - rend`, i.e. -(rend - rpos) = -(cpos - p). That is exactly the argument
   PFmopsM.v's amseek_rewind_spec takes, so the two compose with no arithmetic in between. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04.
(* The relocated cgif core; PFclose.v's Section C cites each name's home. YK11 supplies getr / mkst /
   seg_rom, whose mkst carries the FP state fx exactly as cfg_at's does. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK04 YA0n YG00 YG0f YG0n YG0d YCbq YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmopsM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* NO image pcs here: musl fflush's entry and the interceptor trampoline live in the per-image
   numerals files, lib/A/Stdio/PStdioImgA.v (PFFLUSH_MUSL, PFFLUSH_ICPT) and lib/B/Stdio/PStdioImgB.v
   (PFFLUSH_MUSL_U, PFFLUSH_ICPT_U) (a Theorem Labs lane 02:31Z / 03:54Z). The statement is image-generic:
   the entry pc is a parameter and pfflush_entry_ok tests it. PFFLUSH_OWN_STK needs no twin:
   a Theorem Labs lane measured 1840 as identical in both images. *)

Section F.
(* SK is EXPLICIT (a Theorem Labs lane, 21:58Z): see PFclose.v's Section C. *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.

(* The cgif-core vocabulary is the REAL relocated core (afn_pre / ajournal from YCbq.v, NOT YCe5.v;
   cfg_at / spZ / aregs_preserved from YG0d.v; SRr / world / w_H from YA0n.v). rd is the donor's own
   abbreviation (YE01.v:47). *)
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The WHOLE-REACH stack of a call to fflush on this stream, covering BOTH entries the statement
   admits (pfflush_entry_ok: the ASan interceptor and musl's own entry).

   1840 is MEASURED by a Theorem Labs lane (22:25Z appendix TAG pcapquar of
   pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record)), by the method agreed for all three stdio
   chains: maximum LIVE depth, never the sum; tail calls pop the caller first; every indirect
   edge resolved and named; recursion checked and cited. IDENTICAL in both images.

   The figure is set by the INTERCEPTOR entry, not by musl:
     ___interceptor_fflush 0x46694 (frame 80)
       -> AddrHashMap::acquire 0x47b2c (frame 176) -> InternalAlloc -> ... -> AppendNumber 336
       -> release 0x4834c (32)
       -> jalr REAL fflush 0x8e43c (32, non-tail) -> jalr f->seek = mseek 0x8ec28 (48)
   musl's own entry reaches only 32 + 48 = 80.

   TWO EARLIER VALUES WERE BOTH UNSOUND, which is why this one is measured and cited rather than
   inherited: this file carried 32, which is only fflush's OWN frame (addi sp,sp,-32 at 0x8e43c)
   and sits BELOW mseek's 48; and the donor's FFL_STK 144 is below even the musl-entry 160 that
   the interceptor path needs. A too-SMALL stack constant is the unsound direction (a Theorem Labs lane,
   21:19Z: a constant moves only when a measurement shows it unsound).

   Sound tighter variants exist and are NOT taken, because each rests on a further premise:
   1312 with decorate_proc_maps off, 368 if the secondary cache is already populated. *)
Definition PFFLUSH_OWN_STK : Z := 1840.

(* ---------------------------------------------------------------------------------------------- *)
(* fflush on the read stream: give the read-ahead bytes back and empty the window.                   *)
(*                                                                                                   *)
(* Covers both cases in one statement, because the post is the same either way:                      *)
(*   window non-empty (cpos > p): f->seek(f, -(cpos - p), SEEK_CUR) runs, the cookie rewinds to p;    *)
(*   window empty (cpos = p): the seek is skipped, and the cookie is already at p.                   *)
(* In both the five window fields are zeroed and 0 is returned, so the post is                        *)
(* asource_unbuffered ... p -- the state fmemopen left and the state a later fread re-fills.          *)
(*                                                                                                   *)
(* The caller-consumed count p does NOT change: fflush gives back only what the FILE read ahead of    *)
(* the caller, which is precisely the two-counter distinction this predicate carries.                 *)
(* ---------------------------------------------------------------------------------------------- *)
Definition afflush_source_spec (pc rlo rhi : Z) : Prop :=
  forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
         (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
         (f b M : Z) (C : list Z) (p : Z),
    afn_pre segs B PFFLUSH_OWN_STK ly S W regs mem md ch ->
    getr regs 10 = Z_to_bv 64 f ->
    (* The read-only data the INTERCEPTOR entry reads is pinned. A sixth gap found while proving
       (a Theorem Labs lane, 23:09Z): after REAL fflush returns, the interceptor loads the .rodata word
       0x103d0 at 0x466cc (`ld a1,-760(a0)`), which seeds the AddrHashMap Handle's fields, and
       acquire loads 0x103d8 at 0x47bb4 (`ld a2,-1956(a2)`), the MULTIPLIER of the bucket-index
       hash at 0x47be8 (`mulhu`), and 0x103a0 at AddrHashMap::acquire+0x6c (the auditor found this
       third word, 23:40Z; it is the donor's icell 0xafffff00000fffff). arodata_okS covers ONLY the
       first two: 0x103d0 and 0x103d8 lie in the unowned read-only chunk 0x103b8..0x10420. 0x103a0 is
       NOT covered, because it is an OWNED-STATIC row (AF0m.Tfib_owned_static (0x103a0, 8)) and
       arodata_okS excludes owned-static bytes; the walk gets it from AR's const cells instead
       (AF0m.Tfib_const_abs: z8 (ANum 0x103a0) 0xafffff00000fffff, tied to as_const by
       PcapSyms.ts_const). An earlier version of this comment said arodata_okS covered all three;
       a Theorem Labs lane corrected it at 00:07Z. The memory model gives image bytes no value --
       arbitrary there and AR pins only as_const cells -- so without this the bucket index came
       from an arbitrary multiplier, the bucket address was garbage, and the meta premise below
       could not be used. Form as PFclose.v:134, which already holds this premise at its fflush
       call; the donor discharges the same fact the same way (cgif AE24 ffc_ro_img_of_arodata,
       AE2f.v:221 iflush_tail's ro_img). *)
    arodata_okS segs B rlo rhi (aview segs (w_H W) mem) ->
    (* The ASan meta region is pinned. Needed ONLY by the INTERCEPTOR entry, and the statement
       admits it (pfflush_entry_ok), so the spec must carry it. Found while proving (a Theorem Labs lane,
       22:34Z): after REAL fflush returns, ___interceptor_fflush builds an AddrHashMap Handle
       (map_ = *0xa1100 at 0x466d4, remove = create = 0) and calls acquire 0x47b2c / release
       0x4834c; acquire hashes f into the bucket at M + 120*idx(f) (0x47bd8-0x47c04,
       M = *as_meta_mem), takes that bucket's spin lock and scans its cells. The outcome decides
       0x46704 / 0x4670c / 0x46718: a found cell whose created/refcount is not 1 goes to
       CheckFailed 0x6b918 and the process DIES, and a held lock spins forever. Nothing else in
       this spec pinned M or the bucket bytes. PFclose.v:133 already carries exactly this premise,
       and the donor's interceptor tail consumes the same zero-bucket fact (cgif A/AE2f.v:208-222
       meta_pre / iflush_tail). asrc_meta_inv_kept (PSourceMeta.v) carries it across the call. *)
    asrc_meta_inv segs K ly (rd W mem) M ->
    asource_at segs K (rd W mem) f b C p ->
    (* The FILE block is LIVE in the allocator state -- the same premise mseek needs, and for the
       same reason (a Theorem Labs lane, 22:29Z, found while proving, not in review): fflush's own window
       stores at 0x8e4dc-0x8e4ec write into the FILE block, and ajournal keeps every byte at or
       above alloc_ceiling outside [sp0 - STK, sp0) unchanged (YCbq.v:355), so without this the
       post demands those cells be both unchanged and zeroed. Form as PFreadISpec.v:63; PFclose
       passes it down from its Permutation premise. *)
    In (f, SRC_FILE_BLOCK) (ablocks B ly S) ->
    (* The data buffer is DISJOINT FROM THE FRAME this call may use -- the same gap a Theorem Labs lane
       found in mseek (22:32Z), and it reaches here because the post concludes
       asource_unbuffered, which carries `garr8 b C`. Nothing otherwise keeps b out of
       [spZ regs - PFFLUSH_OWN_STK, spZ regs), which this call's reach may write. The window is
       measured against the whole reach, not fflush's own 32-byte frame: mseek's frame sits at
       [sp0 - 80, sp0 - 32), and YCbq.v:355 keeps unchanged only what lies outside the stated
       window -- which is why PFFLUSH_OWN_STK is the measured 1840 and not 32. Form as
       PFreadISpec.v:67. *)
    (b + Z.of_nat (length C) <= spZ regs - PFFLUSH_OWN_STK \/ spZ regs <= b) ->
    (* NO premise pins the FILE's ops to an image's addresses. An earlier `pmops_ok K`
       (as_seek K = PMSEEK /\ as_close K = PMCLOSE) named asan constants INSIDE this statement,
       which binds it to the asan image even though the hex sat in a Definition: on asan-ubsan,
       0x8ec28 lies inside fopen, at fopen+0x90 (fopen = 0x8eb98, size 0xdc there; measured with
       symbol SIZES, since a nearest-preceding-symbol lookup that drops weak symbols misplaces it;
       the auditor, on a Theorem Labs lane's asan-ubsan close, 23:06Z / 23:40Z). It was also
       unnecessary: the walk reaches the seek callback through f->seek, which source_static pins
       to `as_seek K`, and takes mseek's contract AT `as_seek K` -- an address the image's own
       KS supplies. Dropping it makes the statement strictly STRONGER (one premise fewer). *)
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         (* no allocation: fflush on a read stream only moves the cookie and zeroes the window *)
         ajournal segs B PFFLUSH_OWN_STK (spZ regs) (asource_fp f) ly S W mem md
                  [] ly S W' mem' md' 0 /\
         aregs_preserved regs regs' /\
         getr regs' 10 = Z_to_bv 64 0 /\
         (* the window is empty and the cookie is back at the caller's position *)
         asource_unbuffered segs K (rd W' mem') f b C p /\
         val_mem segs (rd W' mem') (f + SRC_COOKIE_OFF) 8 p /\
         (* no descriptor and no file-system change: see afclose_source_spec's post (PFclose.v).
            The read branch calls only f->seek = mseek, and makes no syscall itself. *)
         m_fds md' = m_fds md /\ m_fs md' = m_fs md).

(* fclose reaches fflush through the interceptor trampoline at 0x415c8 (measured: the call at
   0x8e230 inside musl fclose). PFclose.v's proof consumes afflush_source_spec at that pc. *)
(* The two entries, as PARAMETERS rather than this image's constants, so the predicate is the same
   text on both images: the asan instance passes (PFFLUSH_ICPT, PFFLUSH_MUSL), the asan-ubsan one
   (PFFLUSH_ICPT_U, PFFLUSH_MUSL_U). Naming the constants here bound it to asan (a Theorem Labs lane 23:06Z). *)
Definition pfflush_entry_ok (icpt musl pc : Z) : Prop := pc = icpt \/ pc = musl.

End F.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the
   positional SK would land on the segs argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  afflush_source_spec (fx:=fx) (rc:=rc) SK).
