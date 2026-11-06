(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the two fmemopen FILE ops that libreac/fuzz_pcap's read stream closes and
   flushes through: musl mseek (0x8ec28) and mclose (0x8ecc4).

   STATEMENT ONLY: the definitions compile, there is no lemma yet.

   At ossv/recipes 25e3d17bdb50 (2026-10-29), there was NO DONOR for these. cgif_file_fuzzer's stream is a real file, so its FILE ops are
   __stdio_seek / __stdio_close; at ossv/recipes 25e3d17bdb50 (2026-10-29), the cookie ops of a memory stream appeared in no released proof outside
   libpcap / libreac (a Theorem Labs lane's runtime-donors.md (sha256 77e6fad19fb7; internal record) section 6 item 3), and libpcap/fuzz_pcap is ruled
   out as a donor (different program, different lineage; section 5). pcap's own plain proofs
   lib/Prog/mseek.v / mseek_ro.v / mclose.v are STEP TEMPLATES only: they state over the mallocng plain
   model, not over the ASan journal.

   IMAGE ROOT: the ORIGINAL v1.9.0 set, which is what the statements target --
   the pinned fuzz_pcap images and their unstripped twins,
   statements ed6b6b7b0ab. NOT the toolchain-N images: a runtime premise
   true on one can be false on the other (another proof's
   malloc_context_size = 1 is exactly such a premise, true on N and false here).

   Both bodies are READ OFF pcap's v1.9.0 ASan image (fuzz_pcap.asan (sha256 36da3052c383), the
   unstripped twin of the pin), not inherited:

   mseek(f = a0, off = a1, whence = a2), 39 instructions at 0x8ec28:
     0x8ec34-0x8ec3c  s0 = &__stack_chk_guard, the GLOBAL guard (0x5f48d0, .bss), read through the .got
                      slot 0x9a4b8 -- NOT tp-relative; its value is saved at 24(sp) and re-checked at
                      0x8ec98, with __stack_chk_fail (0x88620) only on mismatch
     0x8ec48  if whence >= 3 -> error
     0x8ec4c  a3 = f->cookie            -- a load from +152, which is why source_static pins it
     0x8ec50  a0 = c->pos               -- cookie +0   (= FILE +232)
     0x8ec54  a4 = c->len               -- cookie +8   (= FILE +240)
     0x8ec5c-0x8ec70  base = [0; pos; len][whence]     -- SEEK_SET / SEEK_CUR / SEEK_END
     0x8ec78  if off < -base -> error
     0x8ec7c  a2 = c->size              -- cookie +16  (= FILE +248)
     0x8ec84  if off > size - base -> error
     0x8ecb4-0x8ecb8  c->pos = base + off; return base + off. On this success path that store and
                      mseek's own frame (0x8ec2c-0x8ec64) are its ONLY stores: rpos (+8) / rend (+16)
                      are not touched (the EINVAL path below also stores errno, at 0x8ec90)
     error (0x8ec88): errno = 22 (EINVAL); return -1

   So mseek's own loads confirm the cookie's field roles independently of pcap's plain model:
   +232 pos, +240 len, +248 size. For an fmemopen read stream musl sets len = size = length C, which
   is why PSource.v pins the same n at both +240 and +248.

   mclose(f), 2 instructions at 0x8ecc4:  li a0,0 ; ret.
   It touches nothing at all and always returns 0. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04.
(* The relocated cgif core; PFclose.v's Section C cites each name's home. YK11 supplies getr / mkst /
   seg_rom, whose mkst carries the FP state fx exactly as cfg_at's does. YP09 supplies mbyte. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YP09 YK11 YK04 YA0n YG00 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* NO image pcs here: mseek's and mclose's entries live in the per-image numerals files,
   lib/A/Stdio/PStdioImgA.v (PMSEEK, PMCLOSE) and lib/B/Stdio/PStdioImgB.v (PMSEEK_U, PMCLOSE_U),
   each derived by symbol + offset from its pin (a Theorem Labs lane 02:31Z / 03:54Z). The statements below
   take the entry pc as a parameter, so this file is image-free and serves both images. *)

(* The three whence values, as mseek's base table indexes them. *)
Definition SEEK_SET : Z := 0.
Definition SEEK_CUR : Z := 1.
Definition SEEK_END : Z := 2.

Section M.
(* SK is EXPLICIT (a Theorem Labs lane, 21:58Z): see PFclose.v's Section C. *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.

(* The cgif-core vocabulary is the REAL relocated core (afn_pre / ajournal from YCbq.v, NOT YCe5.v;
   cfg_at / spZ / aregs_preserved from YG0d.v; SRr / world / w_H from YA0n.v). rd is the donor's own
   abbreviation (YE01.v:47). *)
Local Notation rd W mem := (mrestrict (w_H W) mem).

Definition PMSEEK_STK  : Z := 48.   (* MEASURED: addi sp,sp,-48 at 0x8ec28 *)
Definition PMCLOSE_STK : Z := 0.    (* MEASURED: no frame; two instructions *)

(* ---------------------------------------------------------------------------------------------- *)
(* mseek's REWIND case: the only call fflush makes on a read stream.                                  *)
(*                                                                                                   *)
(* fflush(f) on a read stream calls f->seek(f, -(rend - rpos), SEEK_CUR) to give back the bytes it     *)
(* read ahead of the caller. With whence = SEEK_CUR the base is c->pos = cpos, so the new position is  *)
(*     cpos + (-(rend - rpos)) = cpos - (cpos - p) = p,                                               *)
(* i.e. exactly the caller-consumed count. mseek does NOT empty the window: its only heap store is    *)
(* c->pos (0x8ecb8), so rpos / rend still delimit C[p .. cpos) when it returns, and it is fflush that *)
(* zeroes them afterwards (0x8e4dc-0x8e4ec). The post therefore states the cookie cell and a frame    *)
(* over everything else asource_at reads, NOT asource_unbuffered.                                     *)
(*                                                                                                   *)
(* BOTH of mseek's guards hold for this call, so the rewind CANNOT fail:                              *)
(*   whence = 1 < 3;                                                                                  *)
(*   off >= -base, because off = -(cpos - p) and base = cpos, and p >= 0;                             *)
(*   off <= size - base, because off <= 0 <= length C - cpos = size - base.                           *)
(* That is why the post below has no error disjunct: the EINVAL path at 0x8ec88 is unreachable here.   *)
(* ---------------------------------------------------------------------------------------------- *)
Definition amseek_rewind_spec (pc : Z) : Prop :=
  forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
         (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
         (f b : Z) (C : list Z) (p cpos : Z),
    afn_pre segs B PMSEEK_STK ly S W regs mem md ch ->
    (* the stream, with the window holding C[p .. cpos) *)
    asource_at segs K (rd W mem) f b C p ->
    (* The FILE block is LIVE in the allocator state. Without this the spec is UNPROVABLE, and the
       gap was found by the prover, not by review (a Theorem Labs lane, 22:29Z): mseek's store at 0x8ecb8
       writes f+232..f+239, but ajournal keeps every byte at or above alloc_ceiling outside
       [sp0 - STK, sp0) unchanged (YCbq.v:355) and every image byte but owned-static, errno and
       the ofl head unchanged (YCbq.v:359). Nothing in afn_pre or asource_at kept f out of the
       caller's stack or .bss, so for such an f with p < cpos the post demanded that the cookie
       cell be both unchanged and equal to p. The write lemmas need it too: awr_byte's FP case
       wants f+232 inside a block of ablocks. Stated in the form PFreadISpec.v:63 already uses;
       PFclose carries the same fact through its Permutation premise and passes it down. *)
    In (f, SRC_FILE_BLOCK) (ablocks B ly S) ->
    (* The data buffer is DISJOINT FROM MSEEK'S OWN FRAME. A second unprovability, again found by
       the prover with a counterexample (a Theorem Labs lane, 22:32Z): the post keeps `garr8 b C`, but
       nothing kept b out of [spZ regs - PMSEEK_STK, spZ regs), where mseek stores ra, s0, the
       canary, 0, cpos and n (0x8ec2c, 0x8ec30, 0x8ec44, 0x8ec5c-0x8ec64). Take b = sp0 - 48 with
       C 48 zero bytes: every premise holds -- source_static separates b only from f, and afn_pre
       only says the frame bytes are PRESENT -- yet after the store at 0x8ec2c the last 8 bytes of
       C read back as ra (>= 4096), so garr8 fails and the post is false. Stated in the form
       PFreadISpec.v:67 already uses for its destination buffer. *)
    (b + Z.of_nat (length C) <= spZ regs - PMSEEK_STK \/ spZ regs <= b) ->
    val_mem segs (rd W mem) (f + SRC_COOKIE_OFF) 8 cpos ->
    p <= cpos ->
    (* fflush's arguments *)
    getr regs 10 = Z_to_bv 64 f ->
    getr regs 11 = Z_to_bv 64 (- (cpos - p)) ->
    getr regs 12 = Z_to_bv 64 SEEK_CUR ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         (* no allocation event: mseek only writes the cookie's position cell *)
         ajournal segs B PMSEEK_STK (spZ regs) (asource_fp f) ly S W mem md
                  [] ly S W' mem' md' 0 /\
         aregs_preserved regs regs' /\
         (* the new position is the caller's, and it is what mseek returns *)
         getr regs' 10 = Z_to_bv 64 p /\
         val_mem segs (rd W' mem') (f + SRC_COOKIE_OFF) 8 p /\
         (* every other byte of the FILE block is unchanged -- rpos / rend included, so the window
            still holds C[p .. cpos) until fflush zeroes it *)
         (forall k, 0 <= k < SRC_FILE_BLOCK -> ~ (SRC_COOKIE_OFF <= k < SRC_COOKIE_OFF + 8) ->
                    mbyte segs (rd W' mem') (f + k) = mbyte segs (rd W mem) (f + k)) /\
         (* the buffer, the stdio environment and the open-file-list head are untouched. The head is
            stated here because ajournal does not keep it: asource_fp's sink token unspares
            [AOFL_HEAD, AOFL_HEAD + 8), and fflush's proof needs it to rebuild asource_at. *)
         garr8 segs (rd W' mem') b C /\
         asrc_stdio_env segs K (rd W' mem') /\
         val_mem segs (rd W' mem') (as_ofl_head K) 8 f /\
         (* no descriptor and no file-system change: see afclose_source_spec's post (PFclose.v).
            mseek's only heap store is the cookie cell, and it makes no syscall. *)
         m_fds md' = m_fds md /\ m_fs md' = m_fs md).

(* ---------------------------------------------------------------------------------------------- *)
(* mclose: two instructions, li a0,0 ; ret. It reads and writes nothing.                              *)
(* fclose reaches it through f->close, which source_static pins at +24.                               *)
(* ---------------------------------------------------------------------------------------------- *)
Definition amclose_spec (pc : Z) : Prop :=
  forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
         (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (f : Z),
    afn_pre segs B PMCLOSE_STK ly S W regs mem md ch ->
    getr regs 10 = Z_to_bv 64 f ->
    SRr segs W (cfg_at segs pc regs mem md)
      (fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ajournal segs B PMCLOSE_STK (spZ regs) [] ly S W mem md [] ly S W' mem' md' 0 /\
         aregs_preserved regs regs' /\
         getr regs' 10 = Z_to_bv 64 0 /\
         (* no descriptor and no file-system change: see afclose_source_spec's post (PFclose.v).
            With FP = [] it also follows from ajournal (aos_step_closed, YCbq.v:77); it is stated
            so that the four stdio contracts carry the same fact in the same form. *)
         m_fds md' = m_fds md /\ m_fs md' = m_fs md).

(* The callback addresses the FILE carries, as PARAMETERS: each image's instance passes its own
   (PMSEEK / PMCLOSE on asan, PMSEEK_U / PMCLOSE_U on asan-ubsan). It is no longer a premise of any
   statement -- afflush_source_spec reaches mseek through `as_seek K` directly (a Theorem Labs lane 23:06Z). *)
Definition pmops_ok (sk cl : Z) : Prop := as_seek K = sk /\ as_close K = cl.

End M.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the
   positional SK would land on the segs argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  amseek_rewind_spec (fx:=fx) (rc:=rc) SK).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  amclose_spec (fx:=fx) (rc:=rc) SK).
