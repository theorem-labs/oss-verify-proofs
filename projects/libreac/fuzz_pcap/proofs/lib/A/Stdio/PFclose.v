(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fclose on libreac/fuzz_pcap's fmemopen READ stream, ported from
   cgif_file_fuzzer's write-sink fclose (donor lib/YE01.v:193 afclose_spec, with the walks at
   lib/A/AE24.v:75 and lib/A/AE28.v:238/:651/:690; donor sha c8557374ad2e).

   STATEMENT ONLY, as a Theorem Labs lane asked: the definitions compile, there is no lemma yet.
   The proof composes cgif's relocated interceptor and musl fclose walks (the code is masked-equal:
   icpt_fclose 107/107 insns, musl fclose 51/51) with the read-stream FILE ops; it does not re-walk
   cgif's code.

   WHAT DIFFERS FROM THE DONOR, and why this is a new statement rather than a relocation:
     - the FILE is an fmemopen read stream, so f->close = mclose (0x8ecc4), not __stdio_close, and
       f->seek = mseek (0x8ec28);
     - the stream predicate is a SOURCE (PSource.v asource_at), not cgif's asink_at: a memory stream
       has no fd and no path, so the donor's Fs.fs_lookup / fd_lookup FdFileW conjuncts have no
       counterpart, and the post says asource_none instead of asink_none + fs_lookup;
     - the data buffer b is the harness's g_file (0x5d3f60) and is NOT freed: only the 1304-byte FILE
       block leaves ablocks.

   IMAGE ROOT: the ORIGINAL v1.9.0 set, which is what the statements target --
   the pinned fuzz_pcap images and their unstripped twins,
   statements ed6b6b7b0ab. NOT the toolchain-N images: a runtime premise
   true on one can be false on the other (another proof's
   malloc_context_size = 1 is exactly such a premise, true on N and false here).

   MEASURED on pcap's own v1.9.0 ASan image (fuzz_pcap.asan (sha256 36da3052c383), the unstripped twin
   of the pin, and on its dumps):
     musl fclose 0x8e214, 51 insns. Its calls: fflush trampoline 0x8e230 -> 0x415c8, __ofl_lock 0x8f1dc
     (0x8e240, 0x8e278), __unlist_locked_file 0x8e210 (0x8e270), __ofl_unlock 0x8f20c (0x8e2ac), and
     TWO free trampoline calls at 0x8e2b4 and 0x8e2bc (0x52bd4). f->close is an indirect jalr.
     mclose 0x8ecc4 is 2 instructions (li a0,0; ret): a no-op returning 0.
   So the event count is 2, matching the donor's two free return addresses and a Theorem Labs lane's reading.

   Call sites (a Theorem Labs lane, same image): pcap_source_open 0x81674 and 0x816b8 (error paths),
   pcap_source_close 0x81ec8. The spec is parametric in the entry pc and the two free return
   addresses, so one definition serves all three. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04.
(* The relocated cgif core this statement is written over; Section C cites each name's home. YK11
   also supplies getr / mkst / seg_rom, and its mkst carries the FP state fx: the post's configuration
   must be built with the same mkst as cfg_at's, not lib/Lib's FP-empty one. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK04 YA0n YG00 YG01 YG0f YG0n YG0d YCbq YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The stack budget this statement grants musl fclose's whole reach.

   MEASURED: addi sp,sp,-48 at 0x8e214 (fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record)), so musl fclose's own frame is
   48 bytes; the whole reach is the chain below it.

   PFCLOSE_STK = 16528, the donor's constant (YE01.v AFCLOSE_STK), KEPT by a Theorem Labs lane's 21:13Z
   ruling -- and now SHOWN SOUND, with 10,768 B of headroom.

   MEASURED by a Theorem Labs lane (22:25Z, appendix TAG pcapquar of
   pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record)), by the method agreed for all
   three stdio chains: maximum LIVE depth, never the sum; tail calls pop the caller first; every
   indirect edge resolved; recursion checked and cited. IDENTICAL in both images.

     upper bound      5760 B  =  96 (fclose interceptor) + 48 (musl fclose)
                                 + 5616 (the free interceptor, measured to its leaves)
     tight-reachable  4928 B
     against          16528   -> sound, no constant rises

   THE EARLIER FLOOR IS RETIRED, and two of its figures were wrong: the quarantine path past
   Quarantine::Put (0x352b4) is now fully expanded with every jalr resolved -- it is NOT a stop --
   and the "208 B unwinder spine" was understated, because GetPageSize (0x6533c) tail-jumps into
   musl sysconf, which pushes 544 B, making the spine 688 B. Neither changes soundness here.

   16528 IS EXACTLY TIGHT AT THE INTERCEPTOR ENTRY, AND IT IS THE MINIMUM THERE -- DO NOT TIGHTEN IT.
   The free calls (0x8e2b4, 0x8e2bc) sit 48 below musl fclose's entry (its frame; no pop before
   them), and musl runs 96 below the interceptor entry (the interceptor's frame, 0x467a0). So
   relative to the INTERCEPTOR entry sp0 they are at sp0 - 144, and the free rule's allocator-window
   side condition, aj_free_at_io's `ASTACK - o <= STK`, reads 16384 + 144 = 16528 <= PFCLOSE_STK.
   (An earlier version of this note said "sp0 - 144" without naming the entry; that figure is the
   INTERCEPTOR-relative one. Found by a Theorem Labs lane 23:33Z; the frame of reference corrected by
   a Theorem Labs lane 23:52Z.) So the binding constraint is the MODEL's allocator window (ASTACK =
   16384, YG0d.v:18: the stack ASan's free may clobber), not the machine depth: the measured 5760
   upper bound is NOT a candidate replacement. A constant may only be lowered to a proved upper
   bound AND never below what the model's own side conditions demand. *)
Definition PFCLOSE_STK : Z := 16528.

(* The budget at MUSL fclose's own entry 0x8e214. Relative to it the free calls are at sp - 48, so
   the same side condition reads 16384 + 48 = 16432: EXACTLY tight here too. It is also exactly what
   the interceptor entry can grant across its 96-byte frame (aj_call_tok: 16432 + 96 <= 16528), so
   the two constants compose with no slack and neither can move without the other. Musl fflush,
   called from inside musl fclose at sp - 48, needs 1840 + 48 = 1888 <= 16432. *)
Definition PFCLOSE_MUSL_STK : Z := PFCLOSE_STK - 96.
Lemma PFCLOSE_MUSL_STK_val : PFCLOSE_MUSL_STK = 16432. Proof. reflexivity. Qed.
(* musl fclose's entry (frame 48) is PFCLOSE_MUSL / PFCLOSE_MUSL_U in PStdioImgA.v / PStdioImgB.v. *)

Section C.
(* SK is EXPLICIT (a Theorem Labs lane, 21:58Z), unlike the donor's {SK}. It fixes the open-file
   list head AOFL_HEAD that ajournal spares, and lib/Reusable/YI5b.v:12 declares a #[global] instance
   for the PLAIN image's head: with an implicit SK, a consumer whose closure reaches YI5b would get
   that head silently, and the ASan statement would still build. The caller names the head. *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis ASIL : asource_img_laws SK segs B K.

(* ---------------------------------------------------------------------------------------------- *)
(* The cgif-core vocabulary this statement is written over: the REAL relocated definitions, with    *)
(* their homes on a working branch ae00077a82d.                                                      *)
(*   afn_pre, ajournal         lib/Reusable/YCbq.v:333, :347. YCbq, NOT YCe5: both define these     *)
(*                             names, and YCbq is the superset pcap consumes.                        *)
(*   ablocks, aregs_preserved, spZ, cfg_at                                                           *)
(*                             lib/Reusable/YG0d.v:421, :22, :24, :213                               *)
(*   arodata_okS               lib/Reusable/YE01.v:186                                               *)
(*   asrc_meta_inv, asource_img_laws                                                                 *)
(*                             lib/A/Stdio/PSourceMeta.v: the source analogues of the core's        *)
(*                             ameta_inv (YE01.v:137) and asink_img_laws (YE01.v:25), over K         *)
(*   aview                     lib/Reusable/YG0n.v:18                                                *)
(*   SRr, world, w_H           lib/Reusable/YA0n.v:35, :18                                           *)
(*   astate, st_nev, EV_MAX    lib/Reusable/YG00.v:155, :168, :39;  frames  lib/Reusable/YG01.v:214  *)
(*   alayout, asyms, as_universe, pc_free_ra0   lib/Reusable/YG0f.v                                  *)
(*   rd W mem                  the donor's own abbreviation for mrestrict (w_H W) mem (YE01.v:47;    *)
(*                             mrestrict is lib/Reusable/YK04.v:17)                                  *)
(*                                                                                                   *)
(* ONE SYMBOL RECORD. K : asource_syms (PSource.v) is this file's READ stream, and every stream fact  *)
(* -- asource_at, asource_none, the meta invariant, as_close / as_seek -- is stated over it. The core *)
(* states ameta_inv over cgif's SINK record asink_syms, which would make every caller discharge sink *)
(* image laws (path, trailer) for a program with no sink; asrc_meta_inv is the same body over K.     *)
(* ASIL is the donor's AIL (YE01.v:45) for the source record. Like AIL it enters no Definition here  *)
(* (Coq drops a section hypothesis that no definition uses): it is there for the proofs stated in   *)
(* this Section. The donor's lemmas over the meta invariant, ameta_ptr_of_AR (YE01.v:139) and        *)
(* ameta_inv_kept (YE01.v:151), are ported as asrc_meta_ptr_of_AR / asrc_meta_inv_kept in           *)
(* PSourceMeta.v, under the same ASIL.                                                               *)
(* ---------------------------------------------------------------------------------------------- *)
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* afclose_source_spec: fclose on the fmemopen read stream.                                          *)
(*                                                                                                   *)
(* Premises, in the donor's order (YE01.v:193), with asink_at replaced by asource_at:                 *)
(*   the function precondition; a0 = f; the FILE block is one of the live blocks; the stream is open  *)
(*   at ANY consumed position p (every call site needs this, including the error paths, where p       *)
(*   may be 0 or len C); the meta invariant; the rodata window; room for 2 events; and the two free   *)
(*   return addresses in the trace universe, one per measured free call.                               *)
(*                                                                                                   *)
(* Post: a0 = 0; the FILE block leaves ablocks and NOTHING ELSE does -- in particular the data buffer  *)
(*   b stays, because it is the harness's and fclose never frees it; the stream is closed             *)
(*   (asource_none: musl's open-file list head is 0 again); the frame count is unchanged; the journal  *)
(*   records exactly 2 events over the FILE block's footprint; C's bytes at b are still there, which  *)
(*   is what lets a second pcap_source_open reuse the same buffer; and m_fds / m_fs are unchanged.     *)
(* ---------------------------------------------------------------------------------------------- *)
(* The STACK BUDGET IS A PARAMETER here, because one constant cannot serve both entries (a Theorem Labs lane,
   23:52Z, by arithmetic). The interceptor's `jalr a1` at 0x46834 runs musl fclose at sp1 = sp0 - 96
   (its frame is 96, 0x467a0). So a caller at the interceptor entry with budget STK can grant the
   musl body at most STK - 96, and aj_call_tok's side condition `STK1 - o <= STK` (o = -96) says the
   same. At ONE shared constant the interceptor theorem is NOT derivable from the musl one, although
   both are true. afclose_source_spec below is this definition at PFCLOSE_STK, unchanged for every
   consumer; the musl body is proved at PFCLOSE_MUSL_STK. *)
Definition afclose_source_spec_stk (STK pc ra1 ra2 rlo rhi : Z) : Prop :=
  forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
         (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
         (f b M : Z) (C : list Z) (p : Z) (rest : list (Z * Z)),
    afn_pre segs B STK ly S W regs mem md ch ->
    getr regs 10 = Z_to_bv 64 f ->
    Permutation (ablocks B ly S) ((f, SRC_FILE_BLOCK) :: rest) ->
    asource_at segs K (rd W mem) f b C p ->
    (* The DATA BUFFER is a live block too. Without this the post is not merely unprovable but
       FALSE, with two counterexamples from the prover (a Theorem Labs lane, 22:45Z):
       (a) b = sp0 - 96 with C 96 zero bytes -- the fclose interceptor's `sd ra,88(sp)` at
           0x467a4 leaves ra (>= 4096) in C's last 8 bytes, so the post's `garr8 b C` fails;
       (b) b = as_ofl_head K (0x5f4f88) with C the 8 LE bytes of f -- every premise holds
           (garr8 holds precisely because the head IS f), yet the post needs asource_none, i.e.
           head = 0, while garr8 needs head = f <> 0. The post contradicts itself.
       Note (b) is NOT fixed by the frame-disjointness premise mseek and fflush took: b is in
       .bss there, not on the stack. Membership in ablocks rules out both, since a live heap
       block overlaps neither the frame nor an owned static. The consumer discharges it: b is the
       harness's malloc'd copy, and PcapSourceClose.v:249 already carries exactly this fact. *)
    In (b, Z.of_nat (length C)) (ablocks B ly S) ->
    asrc_meta_inv segs K ly (rd W mem) M ->
    arodata_okS segs B rlo rhi (aview segs (w_H W) mem) ->
    st_nev S + 2 <= EV_MAX ->
    In [pc_free_ra0 (as_code B); ra1] (as_universe B) ->
    In [pc_free_ra0 (as_code B); ra2] (as_universe B) ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => exists (ly' : alayout) (S' : astate) (regs' : bvmap 5 word)
                           (mem' : word -> option byte) (md' : Model),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ajournal segs B STK (spZ regs) (asource_fp f) ly S W mem md
                  [] ly' S' W' mem' md' 2 /\
         aregs_preserved regs regs' /\
         getr regs' 10 = Z_to_bv 64 0 /\
         Permutation (ablocks B ly' S') rest /\
         frames S' = frames S /\
         asource_none segs K (rd W' mem') /\
         (* the harness's buffer survives the close, bytes and all *)
         garr8 segs (rd W' mem') b C /\
         (* no descriptor and no file-system change (donor form YE01.v:222; a Theorem Labs lane 22:06Z). A caller
            cannot derive it: asource_fp carries YI16.sink_token, so ajournal's aos_step lets m_fds
            and m_fs change. It is true of the code: fclose's callees (fflush -> mseek, __ofl_lock,
            mclose, __unlist_locked_file, __ofl_unlock, free x2) make no descriptor or file-system
            syscall -- mclose is li a0,0; ret, mseek writes one cookie cell, and free touches the
            allocator's state, not m_fds / m_fs. *)
         m_fds md' = m_fds md /\ m_fs md' = m_fs md).

(* The statement of record: the budget at the INTERCEPTOR entry (IC_ENTRY, the fclose trampoline),
   which is where the harness calls fclose. Identical text to before the parameter was introduced. *)
Definition afclose_source_spec (pc ra1 ra2 rlo rhi : Z) : Prop :=
  afclose_source_spec_stk PFCLOSE_STK pc ra1 ra2 rlo rhi.

(* The two FILE ops this stream closes through: f->close = mclose (2 instructions, returns 0 and
   touches nothing the predicate names) and f->seek = mseek, which fclose reaches only through its
   fflush call. Their contracts live in PFmopsM.v; their addresses are PMCLOSE / PMSEEK
   (PStdioImgA.v) and PMCLOSE_U / PMSEEK_U (PStdioImgB.v), the pointers source_static pins at
   +24 and +80. The earlier duplicate names PCLOSE_OP / PSEEK_OP (and their _U twins) are retired:
   they were the same two pcs.
   As PARAMETERS, so the predicate is image-generic text (a Theorem Labs lane 23:06Z): each image passes
   its own pair. It is not a premise of afclose_source_spec; the walk reaches both callbacks
   through `as_close K` / `as_seek K`. *)
Definition pclose_ops_ok (cl sk : Z) : Prop :=
  as_close K = cl /\ as_seek K = sk.

End C.

(* GUARD (a Theorem Labs lane, 21:58Z): SK must stay an EXPLICIT argument. SK is passed by position;
   if it ever went back to implicit ({SK}), Coq would fill it by instance search and the positional SK
   would land on the segs argument, so this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  afclose_source_spec (fx:=fx) (rc:=rc) SK).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  afclose_source_spec_stk (fx:=fx) (rc:=rc) SK).
