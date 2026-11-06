(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the statement of the memory-checking runtime's fmemopen wrapper as fuzz_pcap's
   program code calls it, for libreac/fuzz_pcap on libreac v1.9.0 (ASan build). The shape is cgif_file_fuzzer's
   lib/YE01.v afopen_spec (origin/ossv/recipes c8557374ad2e): the same premise order, an SRr post over ajournal with
   an exact event count, and the success / failure split; the stream is a Theorem Labs lane's read-stream predicate
   lib/A/Stdio/PSource.v (asource_none / asource_at) instead of cgif's write sink. Statement only; the proof is
   another owner's (a Theorem Labs lane assigns it). It does not mention the C library's own contract: that enters only in the
   proof, as a Section hypothesis.

   Measured on the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...): the one caller is
   libreac_fuzz_fopen, which tail-jumps to the wrapper's 4-byte jump at 0x807ac (`j 0x415c4`) after popping its own
   32-byte frame, so the wrapper returns to libreac_fuzz_fopen's caller; a0 = the data buffer (ld 0x7d0 from the
   g_file global), a1 = its length (g_file_len), a2 = the "rb" mode literal 0x20d40 (asource_syms' as_mode).
   The wrapper is reached only with a length of at least 1: libreac_fuzz_fopen tests g_file_len itself (0x80788 load,
   0x8078c `beqz a1,0x807b0`, returning 0 at 0x807b0 without calling fmemopen and without writing errno), so the
  empty stream is the caller's case, not this statement's. With a non-null buffer and a length >= 1 musl's fmemopen
  (0x8e870) does not reject: its only length test is a sign test (0x8e8c0 `bgez s2`, reached only when buf = 0,
  0x8e8bc) and its EINVAL arm is the mode test (strchr over "rwa" at 0x8e8b4, never taken for "rb"). It requests one
  1304-byte block (the FILE and its cookie, PSource.v SRC_FILE_BLOCK) with one call of the wrapped malloc
  (jal 0x8e908). In the code that call may return 0 (allocator_may_return_null = 1 on every pcap image): then
  0x8e90c `bnez a0` falls to 0x8e910 `j 0x8e8dc`, which returns 0 having written nothing. That arm is DEAD under this
  statement's premises: the call goes through the core's malloc rule amalloc04_rule, whose post gives 4096 <= res
  (YC5d.v:72) whenever its room premises hold, and those are exactly the premises below (st_nev S + 1 <= EV_MAX,
  blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX, mo_ok MT S (mo_malloc MT SRC_FILE_BLOCK), the call-trace premises);
  the same fact kills the harness's own `if (!buf) abort()` (a Theorem Labs lane, alloc-null.md (sha256 678cc2328725; internal record)). So the post is the success
  arm only, the shape cgif's amalloc04_rule itself has; the proof of this statement refutes musl's NULL arm from that
  rule. The malloc room is counted by the donor's meter (YC5d.v ameter_ops: mo_ok in the pre, mo_le in the post).
  (History: an earlier version had an unconditional res = 0 arm; a caller can never refute such an arm, so with it a
  well-formed input could reach the harness's abort at 0x81340 and the entry contract was unprovable (found by
  a Theorem Labs lane). The audit row 5 premise that forces success is amalloc04_rule's post.)

  No AddrHashMap meta premise (statement class R2 does not apply): ___interceptor_fmemopen (0x46644) is 20
  instructions, TryAsanInitFromRtl then a tail jump through 0x9b5e8, with no AddrHashMap / FileMetadata access and no
  path to CheckFailed (a Theorem Labs lane).

  AFMEMOPEN_STK = 18624 (cgif's AFOPEN_STK value) is an upper bound on the call's stack use, justified by
  a Theorem Labs lane's whole-reach table pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record) (one method for
  fmemopen / fread / fclose, on the original v1.9.0 pins; maximum live depth, allocator path included): the normal
  path's maximum is 4368 bytes (the index interceptor 2144 -> strchr -> strchrnul -> the strlen interceptor 2144),
  below 18624 (a Theorem Labs lane ruling: the donor value is kept; the slack is deliberate). The interceptors' ERROR paths
  are NOT budgeted: their measured depth is only a floor (>= 5360 bytes), so no bound covers them; a walk of this
  call must prove every report path unreachable from its premises, never rely on AFMEMOPEN_STK for it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK18 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition AFMEMOPEN_STK : Z := 18624.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ajournal (YCbq.v) is stated under cgif's sink-head class; it is a parameter here as in cgif's YE01.v. *)
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The footprint, as cgif's afopen_spec (YE01.v) writes it: the sink token alone. ajournal (YCbq.v) keeps every image
   byte outside owned-static / errno / fp_spares FP, and fp_spares FP spares exactly the open-file-list head
   [AOFL_HEAD, AOFL_HEAD + 8), and only when FP holds the token (YI16.sink_open_fp FP = in_fp FP 0, YCbq.v:87).
   fmemopen links the new FILE there (head 0 -> res); the lock word returns to 0, so it is kept; the new FILE block is
   fresh, so no live byte constrains it; errno is outside every footprint by ajournal's own clause. An earlier
   version had [(ofl_lock, ofl_lock + 16)], under which the journal kept the head and the post contradicted it
   (found by two Theorem Labs lanes). *)
Definition afmemopen_fp : list (Z * Z) := [YI16.sink_token].

(* pc: the wrapper's entry (its 4-byte jump, 0x415c4 on the pin); ra: the return address of the malloc call inside the
   C library's fmemopen. CTX: the caller's possible return-address spines (YCbq.spine of afn_pre's chain). At that
   malloc call s0 is still the caller's frame pointer (the wrapper, the interceptor and libreac_fuzz_fopen restore s0
   before their tail jumps), so the allocator records ra followed by the CALLER's spine, never [pc_malloc_ra0; ra]
   alone: the universe premise is the donor's callee form (cgif lib/A/ACeb.v:29-39), per context (found by
   a Theorem Labs lane, pcaptr-asks.md (sha256 436176c63147; internal record) 4.1). *)
Definition afmemopen_spec (CTX : list (list Z)) (pc ra mc_lo mc_hi : Z) : Prop :=
  forall W ly S regs mem md ch (b n : Z) (C : list Z),
  (* PSource's head is the head ajournal spares (cgif's asink_img_laws ail_head) *)
  as_ofl_head K = AOFL_HEAD ->
  afn_pre segs B AFMEMOPEN_STK ly S W regs mem md ch ->
  In (spine ch) CTX ->
  getr regs 10 = w64 b -> getr regs 11 = w64 n -> getr regs 12 = w64 (as_mode K) ->
  asource_none segs K (rd W mem) ->
  n = Z.of_nat (length C) -> 1 <= n < 2 ^ 26 ->
  In (b, n) (ablocks B ly S) -> garr8 segs (rd W mem) b C -> bytes_ok C ->
  (* the word constants musl fmemopen's strchr calls read (__strchrnul, [mc_lo, mc_hi) = 0x10350 / 0x10370 on the
     pin), as the image has them: AR does not pin them (YG0n.v:490). The donor's NARROW form, cgif A/AE39.v:28
     mconsts_view over segs, derived at the program site from its image-region fact (cgif A/AD1k.v:266) and moved across
     calls by mconsts_view_keep (cgif A/AE39.v:42); mirrors a Theorem Labs lane's rfmemopen_pre (a working branch c53fee70393; a Theorem Labs lane 00:23Z).
     It replaces an earlier full rom_view premise, which no caller could derive. *)
  (forall a, mc_lo <= a < mc_hi ->
     aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
  st_nev S + 1 <= EV_MAX -> blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX ->
  mo_ok MT S (mo_malloc MT SRC_FILE_BLOCK) ->
  In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (ra :: c))) (as_universe B)) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (res : Z),
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
       ajournal AFMEMOPEN_STK (spZ regs) afmemopen_fp ly S W mem md [] ly' S' W' mem' md' 1 /\
       aregs_preserved regs regs' /\ getr regs' 10 = w64 res /\ frames S' = frames S /\
       mo_le MT S S' (mo_malloc MT SRC_FILE_BLOCK) /\
       (* no descriptor and no file-system change: fmemopen makes no file-system call (its only callee with an
          effect on the model is the allocator, whose mappings touch neither); ajournal alone would allow them,
          because the footprint carries the sink token (aos_step's fds / fs relation; found by a Theorem Labs lane) *)
       m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
       (* the FILE and its cookie, linked as the open stream *)
       4096 <= res /\ res mod 16 = 0 /\
       ablocks B ly' S' = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] /\
       asource_unbuffered segs K (rd W' mem') res b C 0).

End a.

(* SK is EXPLICIT for every caller (a Theorem Labs lane ruling 21:57Z): the only global sink_head instance loaded with the
   unit is the PLAIN build's (lib/Reusable/YI5b.v:12, ofl head 0x4f3b0); inferring it here would make
   as_ofl_head K = AOFL_HEAD false on the ASan image. Callers pass the core's ASan head. *)
Arguments afmemopen_spec {fx rc} SK.
(* Guard (a Theorem Labs lane's form): if SK ever becomes implicit again, the positional SK lands on segs and this fails. *)
Check (fun fx rc (SK : YI16.sink_head) => afmemopen_spec (fx:=fx) (rc:=rc) SK).
