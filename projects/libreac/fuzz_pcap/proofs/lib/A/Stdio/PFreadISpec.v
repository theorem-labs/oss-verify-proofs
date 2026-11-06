(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the statement of the memory-checking runtime's fread WRAPPER as fuzz_pcap's
   program code calls it, for libreac/fuzz_pcap on libreac v1.9.0 (ASan build), in the DONOR'S CALLER-JOURNAL form
   (cgif_file_fuzzer lib/YC20.v:311-365 tlzw_kept / tlzw_pR_ok / tlzw_post / tlzw_spec, origin/ossv/recipes
   c8557374ad2e). Statement only; the proof is another owner's. It does not mention the C library's own contract:
   that enters only in the proof, as a Section hypothesis.

   WHY THE FORM CHANGED (a Theorem Labs lane). The earlier statement took afn_pre and gave apost_base.
   apost_base starts a FRESH journal at the call, and that journal keeps every byte at or above alloc_ceiling
   outside the callee's own window (YCbq.v:355-356) whatever the footprint. Two of pcap's four fread sites write a
   destination in the CALLER's frame or on the real stack, so the old post asked one cell to be both kept and
   written: no walk could use it. The form here takes the CALLER's journal and EXTENDS it, and the right to write
   each destination byte is a premise the caller supplies (awr_byte, YCbq.v:459-461).

   ONE SOURCE with a Theorem Labs lane's musl-level statement where the two levels coincide: this file Requires its
   lib/A/Stdio/PFreadM.v (a working branch, merged into this branch) and uses the shared predicates
   rread_k / rread_wrset / rread_wr_ok / rread_at / rread_dest / rread_call / rread_kept / rread_post_base DIRECTLY
   (a Theorem Labs lane ruling; earlier versions of this file restated them under afread_ names). A change to them is
   a Theorem Labs lane's, and composes here unchanged.

   WHERE THIS LEVEL DIFFERS FROM musl's, and what that changes here:
     - THE WRAPPER'S OWN FRAME. The call enters the 4-byte jump 0x41580 -> ___interceptor_fread, whose frame
       (2128 bytes) sits above musl fread's. The window is therefore AFREAD_STK = 8192, not RFREAD_STK = 4224:
       a Theorem Labs lane checked the composition 2128 + 4224 = 6352 <= 8192 (its pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record) measures the
       same reach at 4416 from the interceptor's entry). The donor value 8192 is kept (a Theorem Labs lane ruling); the
       slack is deliberate. Every premise that names the callee's window therefore names AFREAD_STK: the
       destination's and the FILE block's rread_wr_ok, the data buffer's disjunct, and rread_call's placement.
    - THE INTERCEPTOR'S SHADOW CHECKS. After the real fread returns (the jalr at 0x43558) the wrapper reads the
      shadow of the destination (0x43568-0x435bc, region_is_poisoned 0x436a8); musl's own path checks it only
      through mread's __wrap_memcpy (an auditor). That is why the
       destination keeps the shadow premises range_addressable and shadow_hull_vis (aintrin_realizes' own,
       YG0d.v:318-336) and why the post keeps the shadow band [kLowMemEnd, kHighShadowEnd) unchanged.
     - NO META REGION. The fread wrapper never reaches the AddrHashMap acquire / release that the fclose and
       fflush wrappers use (and libunwind's path to __wrap_fflush is dead, because __wrap_getenv is the NULL
       stub), so this statement carries no meta premise and no meta conjunct, unlike PFclose's (auditor's
       measurement, a Theorem Labs lane).
     - THE ERROR PATHS ARE NOT BUDGETED. Their measured depth is only a floor (>= 5360 bytes, ReportGenericError
       3232), so no constant covers them: a walk of this call must prove every report path unreachable from its
       premises (as a Theorem Labs lane's strcmp walk does), never lean on AFREAD_STK for it.

   THE CALL SITES, measured on the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...; the unstripped twin
   fuzz_pcap.asan (sha256 36da3052c383) carries the symbols). Four, all with item size 1 (`li a1,1` at 0x815e8,
   0x819ac, 0x81ae4, 0x81bc8), a3 the stream loaded from the source object:
     pcap_source_open 0x815f8, nm = 24, destination in the caller's side-stack frame or on the real stack;
     pcap_source_next 0x819b8, nm = 16, likewise;
     pcap_source_next 0x81af0, nm = s11 with 0 < s11 < incl_len, destination the harness's heap buffer;
     pcap_source_next 0x81bd4, nm = incl_len (possibly 0), destination the same heap buffer.
   EACH ARM OF afread_at IS REACHED (a Theorem Labs lane's pcap-fread-dest.md (sha256 dc57856b06db; internal record), both images). The frame arm and the
   stack arm are the SAME two sites, 0x815f8 and 0x819b8: the local lies in __asan_stack_malloc_1's 96-byte (open)
   or __asan_stack_malloc_0's 64-byte (next) side-stack frame when __asan_option_detect_stack_use_after_return
   (cell 0xa18c0 through the GOT word 0x99888) is non-zero (`beqz` at 0x814bc / 0x8188c), and on the real stack
   when it is zero (0x814dc-0x814f4 / 0x818ac-0x818c4); the flag is a run-time cell, so both are live code. The
   live-block arm is 0x81af0 and 0x81bd4, where the destination is the buffer LLVMFuzzerTestOneInput allocates at
   0x80ab8. No arm can be dropped without dropping a site.

   nm = 0 IS REACHABLE and covered (k = 0): at 0x81bd4 nm is the record's incl_len, and the branch that reaches it
   (0x81abc `bgeu s7,s11` -> 0x81b40) tests no incl_len >= 1. It is not a no-op on the FILE: musl's fread stores
   the orientation word (+136) at 0x8eeac-0x8eec0 before it tests the total, which asource_at allows (PSource
   source_mode: 0 or U32M1) and which afread_wrset covers.

   WITH SIZE 1 musl's fread returns the byte count, min(nm, what is left), so the post gives that count exactly;
   a read at the end of the stream returns 0 and keeps asource_at valid there (PSource asource_rest_eof). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK18 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The wrapper's window: its own frame above musl fread's whole reach (header, THE WRAPPER'S OWN FRAME). *)
Definition AFREAD_STK : Z := 8192.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ajournal (YCbq.v) is stated under cgif's sink-head class; it is a parameter here as in cgif's YE01.v. *)
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* fread(d, 1, nm, f) through the wrapper                                                           *)
(* ---------------------------------------------------------------------------------------------- *)
(* a Theorem Labs lane's rfread_pre at the wrapper's window. No meta premise: the fread wrapper reaches no AddrHashMap
   operation (header, NO META REGION). *)
Definition afread_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (k : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z))
    (d nm f b p : Z) (C : list Z) : Prop :=
  rread_call segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k AFREAD_STK regs ch /\
  getr regs 10 = w64 d /\ getr regs 11 = w64 1 /\ getr regs 12 = w64 nm /\ getr regs 13 = w64 f /\
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
  (b + Z.of_nat (length C) <= spZ regs - AFREAD_STK \/ spZ regs <= b) /\
  asource_at segs K (rd W memc) f b C p /\
  (* fread and mread write the FILE block, and the caller's journal keeps a block that was live at its start
     unless the byte is in the caller's footprint (YCbq.v:357-358), so the FILE needs the same per-byte right as
     the destination *)
  rread_wr_ok B STK sp0 FP ly S lyc Sc own AFREAD_STK (spZ regs) f SRC_FILE_BLOCK /\
  0 <= nm <= 2 ^ 26 /\
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc AFREAD_STK (spZ regs) d nm f b
    (Z.of_nat (length C)).

(* a Theorem Labs lane's rfread_post. The layout and the allocation state are as they were, the count is the byte count,
   the destination holds the bytes read, the stream has moved, and the wrapper changed no descriptor, no file
   system entry and no shadow outside what it wrote. *)
Definition afread_post (d nm f b p : Z) (C : list Z) (lyc : alayout) (Sc : astate)
    (W : world segs) (memc : word -> option byte) (mdc : Model)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  let j := rread_k nm (Z.of_nat (length C)) p in
  ly' = lyc /\ S' = Sc /\
  getr regs' 10 = w64 j /\
  garr8 segs (rd W' mem') d (firstn (Z.to_nat j) (skipn (Z.to_nat p) C)) /\
  asource_at segs K (rd W' mem') f b C (p + j) /\
  (* musl's fread always stores mode |= mode - 1 (0x8eeac-0x8eec0) *)
  source_mode segs (rd W' mem') f U32M1 /\
  (* nm = 0: the FILE is as it was, except that orientation word *)
  (nm = 0 -> forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) memc a) /\
  (* the wrapper and musl's read path reach no ecall. The journal above is the CALLER's, and its aos_step
     (YCbq.v:34-39) permits a descriptor or file-system change when the caller's footprint holds the sink token,
     so the equalities have to be stated here or no caller can have them (as afmemopen_spec does). *)
  m_fds md' = m_fds mdc /\ m_fs md' = m_fs mdc /\
  (* the shadow band is as it was: the wrapper reads the shadow of (d, j) after the real fread returns
     (0x43568-0x435bc, 0x436a8), and below alloc_ceiling afread_kept pins only the frames' shadow *)
  (forall s, kLowMemEnd <= s < kHighShadowEnd ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s).

(* pc: the wrapper's entry (its 4-byte jump, 0x41580 on the pin). a Theorem Labs lane's rfread_contract. *)
Definition afread_spec (pc : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (d nm f b p : Z) (C : list Z),
  afread_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C ->
  SRr segs W (cfg_at segs pc regs memc mdc)
    (rread_post_base segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k AFREAD_STK regs
       (rread_wrset f d nm) (afread_post d nm f b p C lyc Sc W memc mdc)).

End a.

(* SK is EXPLICIT for every caller (a Theorem Labs lane ruling 21:57Z): the only global sink_head instance loaded with
   the unit is the PLAIN build's (lib/Reusable/YI5b.v:12, ofl head 0x4f3b0); inferring it here would make
   as_ofl_head K = AOFL_HEAD false on the ASan image. Callers pass the core's ASan head. *)
Arguments afread_pre {rc} SK segs.
Arguments afread_spec {fx rc} SK segs.
(* Guard (a Theorem Labs lane's form): if SK ever becomes implicit again, the positional SK lands on segs and this fails. *)
Check (fun fx rc (SK : YI16.sink_head) (segs : list Segment) (B : asyms) (K : asource_syms) (pc : Z) =>
         afread_spec (fx:=fx) (rc:=rc) SK segs B K pc).
(* Guard (a Theorem Labs lane's form): if SK ever becomes implicit again, the positional SK lands on segs and this fails. *)
