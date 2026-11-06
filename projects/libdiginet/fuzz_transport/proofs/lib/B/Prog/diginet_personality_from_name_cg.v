(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of the ASan strcmp interceptor (and of the one-`j` trampoline
   __interceptor_trampoline_strcmp = __wrap_strcmp that enters it), in the form of abcmp_realizes
   (projects/cgif/cgif_file_fuzzer/proofs/lib/YG0d.v) over the asan-state definitions of that proof as libreac/fuzz_grant holds
   them. The interceptor compares byte by byte up to the first index k where the bytes differ or s1's byte is 0, checks
   [s1, s1 + k + 1) and [s2, s2 + k + 1) with the READ_RANGE checks (QuickCheck below 64 bytes, else
   __asan_region_is_poisoned), calls the empty weak hook, and returns CharCmpX (-1, 0 or 1). Target-independent: every
   address comes from the layout or the registers. R1: the strings are disjoint from the callee's stack window
   [sp - 2 ESTACK, sp). R2: not stated, because this interceptor does not touch the AddrHashMap metadata (no FILE
   object). It subsumes the literal instance of libreac/fuzz_pcap lib/A/Rt/StrcmpDef.v (x = y, k = the literal's
   length, c1 = c2 = 0, result 0). *)
(* Modified by Theorem Labs, 2026-10-29: taken by path from libreac/fuzz_grant lib/Reusable/AStrcmpDef.v
   (a working branch 97c611eec86, owner a Theorem Labs lane, the text of record for the strcmp trampoline contract in
   a Theorem Labs lane's registry). Only the module paths change (fuzz_grant -> fuzz_identity); the statement is identical. The
   walk is a Theorem Labs lane's lib/A/Rt/Strcmp.v, relocated to identity's addresses separately. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/AStrcmpDef.v (donor image sha256 c954b804786c), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Reusable/AStrcmpDef.v, with its module paths and module names changed; 74 of its 111 lines of code are new or changed and 16 lines of the source are left out. *)
(* diginet_personality_from_name_cg: the ASan walk contract of diginet_personality_from_name (src/diginet_codec.c:17-25;
   plain contract lib/Prog/diginet_personality_from_name_c.v, result codec_cells.v from_name_res) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x8c050 = transportb_sigma TB_diginet_personality_from_name, size 172,
   as STATEMENTS only (no proof). It stores into no harness global and calls the strcmp wrapper, so it takes decode's
   caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the caller's donor journal ajournal); a
   G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = x, not 0, with the bytes tb at x, a 0 among them (a C string: codec_cells.v cstr), placed by
   trans_src_ok and outside this call's stack window (decode_off_win); the read-only bytes it reads (personalities[]
   and the two announce names its entries point to) read as the image's (trans_rom_view_rd). The function returns to
   ra with a0 = trans_pfrom_res tb (personalities + 0 for "CNTRL|24", personalities + 24 for "MAINUNIT", else 0;
   image B's personalities[] is at 0xa3b00 = TRANS_PERS = TImgB.v ti_personalities timg_B), the callee-saved
   registers kept, no allocator event, no meter charge, and every byte outside its stack window kept (it stores
   nothing outside its own frame: E is empty). This is what the plain contract says: a0 = from_name_res tb (the same
   cases at the plain image's PERS); munch of the frame only. Its cstr / off-window premises become garr8 + the 0 in tb
   + trans_src_ok + decode_off_win, relro_img becomes trans_rom_view_rd, and mem_inv, stk and the RELRO / stack
   disjointness are dropped (the journal's window premises). No world: the function reads no
   harness global.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 172 code bytes of this function are equal in both files),
   43 words:
     0x8c050          sp = sp - 48; ra, s0 .. s4 at sp + 40 .. sp + 0 (0x8c054 - 0x8c068), loaded back at 0x8c0d8 -
                      0x8c0ec; no side-stack frame, no frame pointer.
     0x8c06c          x = 0 returns a0 = 0 (kept unreached: x <> 0).
     0x8c070 - 0x8c088  s0 = x, s2 = k = 0; s1 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it
                      holds: the shadow base 0x7fff8000 (transport_cells rows 1-2); s3 = personalities (0xa3b00).
     0x8c08c - 0x8c0cc  for k = 0, 1: s4 = personalities + 24 k; the instrumented check of the 8-byte load at s4 + 8
                      (the shadow byte at ((s4 + 8) >> 3) + 0x7fff8000 must be 0, else the error path), then
                      personalities[k].announce_name (0x211a0 "CNTRL|24" for k = 0, 0x211c0 "MAINUNIT" for k = 1:
                      TRANS_PNAME0 / TRANS_PNAME1, measured: the 8-byte words at 0xa3b08 and 0xa3b20); strcmp (0x42d28 =
                      transportb_sigma TB___interceptor_trampoline_strcmp) at 0x8c0b8 with (x, that name); a result 0,
                      or k = 1, ends the loop.
     0x8c0d0 - 0x8c0d4  a0 = s4 when the last result was 0, else 0; the return at 0x8c0f4.
   Against image A's code (lib/A/Prog/diginet_personality_from_name_cg.v, 43 words): the same 43 instructions with
   image B's auipc / ld / jal immediates. Image B's code has no UBSan check here: no trap word, no abort.
   No trap path. Error path (1 call) and the fact that rules it out: errpath_load8 0x8c0f8 (the call of
   __asan_report_load8, 0x596e4 = TB___asan_report_load8; personalities + 8 + 24 k, 8-aligned): personalities' 48 bytes
   have shadow 0 (transport_cells: decode_zshadow_at TRANS_PERS), and strcmp keeps every byte outside its stack
   window.
   The result: strcmp's result is 0 exactly when the C string at x equals the name (the bytes before tb's first 0 are
   codec_cells.v cstring (zb tb), the names are NAME_C24 / NAME_PC, read through trans_rom_view_rd).
   Callee texts assumed, as a NAMED HYPOTHESIS of this statement: the strcmp wrapper as astrcmp_realizes (defined below,
   the text of lib/A/Prog/diginet_personality_from_name_cg.v Section strcmp word for word: the registry text of record
   for the strcmp trampoline contract, libreac/fuzz_identity lib/Reusable/AStrcmpDef.v at origin/ossv/recipes, from
   libreac/fuzz_grant lib/Reusable/AStrcmpDef.v (file sha256 403db67e9c50; donor not released); this unit's
   lib/Reusable has no copy) at transportb_sigma TB___interceptor_trampoline_strcmp = 0x42d28, whose word is the
   4-byte jump into the wrapper. Its ranges: [x, x + j + 1) (j the index where the compare stops, at most tb's first
   0: inside tb) and [name, name + j + 1) (inside the 9-byte string, in TRANS_RO_RD; transport_cells gives its
   shadow: 0 for the first 8 bytes, 1 for the ninth). Besides the range's own shadow bytes, astrcmp_realizes asks
   every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of 64
   bytes). On image B the two names are in two groups (image A's share one): TRANS_PNAME0's group [0x7fffc230,
   0x7fffc238) is the shadow of [0x21180, 0x211c0), the 32 bytes before the name (a string of the UBSan build's
   source locations, which the record gives shadow 0) and the name; TRANS_PNAME1's group [0x7fffc238, 0x7fffc240) is
   the shadow of [0x211c0, 0x21200), the name and the 32 bytes after it (shadow 0 in the record). transport_cells
   gives 0x7fffc234 / 0x7fffc238 (0) and 0x7fffc235 / 0x7fffc239 (1); trans_pfrom_cells the four guard bytes
   0x7fffc236, 0x7fffc237, 0x7fffc23a, 0x7fffc23b (0xf9) and the zero shadow 0x7fffc230 - 0x7fffc233 and
   0x7fffc23c - 0x7fffc23f, rows of the record (lib/B/YF0m.v Tfib_const_shadow, Tfib_zero_shadow ranges (0x21180,
   0x28) and (0x211e0, ...)). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the strcmp wrapper uses below sp - 48 (astrcmp_realizes): PFROM_STK.

   The caller is on_announce (the call at 0x87eac, return address 0x87eb0; DgnTransportBList.v PCall
   TB_diginet_personality_from_name): a0 = s10 + 10 (the name field of the announce diginet_announce_parse filled,
   in its class-3 side-stack frame). It supplies the journal, the string's placement and bytes from its own walk.
   Form: lib/A/Prog/diginet_personality_from_name_cg.v (image A's statement of this function), at image B's entry,
   personalities[], names, runtime cells and listing names, with trans_pfrom_cells for image B's two shadow groups. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require codec_cells.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module CC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.codec_cells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_personality_from_name's frame (`sp = sp - 48` at its entry; no realignment) and the 2 * ESTACK its strcmp
   calls use below sp - 48 (astrcmp_realizes). *)
Definition PFROM_FRAME : Z := 48.
Definition PFROM_STK : Z := PFROM_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition PFROM_EV : Z := 0.

(* The result: codec_cells.v from_name_res at image B's personalities[] (0xa3b00; elements of 24 bytes). *)
Definition trans_pfrom_res (tb : list byte) : Z :=
  if list_eq_dec Z.eq_dec (CC.cstring (CC.zb tb)) CC.NAME_C24 then TRANS_PERS
  else if list_eq_dec Z.eq_dec (CC.cstring (CC.zb tb)) CC.NAME_PC then TRANS_PERS + 24
  else 0.
Lemma trans_pfrom_pers : TRANS_PERS = TI.ti_personalities timg_B.
Proof. reflexivity. Qed.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_const_shadow rows and Tfib_zero_shadow ranges) that the strcmp
   calls need beyond transport_cells: the guard granules of the two 9-byte names personalities[] points to
   (TRANS_PNAME0 0x211a0, TRANS_PNAME1 0x211c0), and the shadow 0 of the 32 bytes before the first name and after the
   second, the rest of the two aligned groups of 8 shadow bytes the names lie in. *)
Definition trans_pfrom_cells (B : asyms) : Prop :=
  decode_zshadow_at B (TRANS_PNAME0 - 32) TRANS_PNAME0 /\
  decode_zshadow_at B (TRANS_PNAME1 + 32) (TRANS_PNAME1 + 64) /\
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TRANS_PNAME0 + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_PNAME0 + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_PNAME1 + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_PNAME1 + 24))) 0xf9) (as_const B ly).
Lemma trans_pfrom_cells_rows :
  map BCells.shadow_addr [TRANS_PNAME0 - 32; TRANS_PNAME0 + 16; TRANS_PNAME0 + 24; TRANS_PNAME1 + 16;
                          TRANS_PNAME1 + 24; TRANS_PNAME1 + 32] =
  [0x7fffc230; 0x7fffc236; 0x7fffc237; 0x7fffc23a; 0x7fffc23b; 0x7fffc23c].
Proof. reflexivity. Qed.

(* The contract of the strcmp wrapper, the named hypothesis of this statement: the runtime registry's text of record
   (AStrcmpDef.astrcmp_realizes; libreac/fuzz_identity lib/Reusable/AStrcmpDef.v at origin/ossv/recipes), verbatim
   over this unit's lib/Reusable names, in the form of abcmp_realizes (YG0d.v); the same text as
   lib/A/Prog/diginet_personality_from_name_cg.v Section strcmp. The wrapper compares byte by byte up to the first
   index k where the bytes differ or s1's byte is 0, checks that [s1, s1 + k + 1) and [s2, s2 + k + 1) are marked
   usable, and returns sanitizer_common's CharCmpX (strcmp_res). *)
Section strcmp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Definition strcmp_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.

(* The compare stops at index k: the bytes before k are equal and not 0; at k they differ or s1's byte is 0. *)
Definition str_meet (W : world segs) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
  0 <= k /\
  (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                     aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
  aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
  (c1 <> c2 \/ c1 = 0).

Definition astrcmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  str_meet W mem x y k c1 c2 ->
  src_ok segs W regs mem x (k + 1) -> src_ok segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End strcmp.

Section pfrom. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X:
   a0 = trans_pfrom_res tb. *)
Definition transport_pfrom_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (tb : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs PFROM_STK PFROM_EV 0
    (fun _ => False) (fun regs2 _ _ => YK11.getr regs2 10 = w64 (trans_pfrom_res tb)).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_diginet_personality_from_name_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (x : Z) (tb : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 x ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - PFROM_STK -> spZ regs <= sp0 ->
    x <> 0 ->
    garr8 segs (mrestrict (w_H W) memc) x (map DSpec.bz tb) -> In (DSpec.b8 0) tb ->
    trans_src_ok B lyc Sc W memc x (Z.of_nat (length tb)) ->
    decode_off_win regs PFROM_STK x (Z.of_nat (length tb)) ->
    trans_rom_view_rd W memc ->
    st_nev S + k + PFROM_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_pfrom_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tb).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the shadow of
   personalities and of the two names), the rest of the names' shadow groups (trans_pfrom_cells), the two read-only
   facts of the record (they keep those bytes visible through the journal), the allocator and meter laws, and the
   strcmp contract at the listing's trampoline (the named hypothesis astrcmp_realizes) give the contract at
   TB_diginet_personality_from_name. *)
Definition transport_diginet_personality_from_name_cg_holds_stmt : Prop :=
  transport_cells B -> trans_pfrom_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @astrcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_strcmp)) ->
  transport_diginet_personality_from_name_cg (transportb_sigma TB_diginet_personality_from_name).
End pfrom.
