(* desk_named_cg: the ASan walk contract of desk_named (fuzz/fuzz_transport.c:265-273, spec_strz_len inlined; model
   lib/TModel/TCb.v desk_named_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x85100 =
   transportb_sigma TB_desk_named, size 212, as STATEMENTS only (no proof). It stores into no harness global and calls
   the bcmp wrapper, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the
   caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = p, not 0, with the bytes body at p (from the announce's body to the end of its block),
   placed by trans_src_ok and outside this call's stack window (decode_off_win); the two read-only strings it compares
   read as the image's (trans_rom_view_rd); desk_named_m timg_B Bw body = Some (Bw', r) (lib/B/Prog/TImgB.v timg_B:
   ti_spec_c24 = SPEC_C24 = 0xa3a00, ti_spec_pc = SPEC_PC = 0xa3a20). The function returns to ra with a0 = r, the
   callee-saved registers kept, no allocator event, no meter charge, every byte outside its stack window kept (it
   stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/desk_named_c.v) says: a0 = r; B' = B and wmem rsegs m' B; munch of the frame only. Its bytes_at /
   off_window premises become garr8 + trans_src_ok + decode_off_win, timg_plain becomes timg_B, and mem_inv is
   dropped. Its wmem premise has no counterpart: the function reads no byte of a harness global (measured:
   its only loads are of p + 24 .. p + 32, their shadow bytes, the runtime cells and, in the wrapper, the read-only
   strings), and the model's result does not depend on Bw; Bw' = Bw is the model's.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 212 code bytes of this function are equal in both files),
   53 words:
     0x85100          sp = sp - 16; ra at sp + 8, s0 at sp + 0 (0x85104, 0x85108), loaded back at 0x851a8, 0x851ac;
                      no side-stack frame, no frame pointer.
     0x8510c          p = 0 goes to the trap word at 0x851d0.
     0x85110 - 0x85114  p >= 2^64 - 24 (unsigned; p + 24 wraps) goes to the trap word.
     0x85118 - 0x85124  i = a1 = 0; a2 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds:
                      the shadow base 0x7fff8000 (transport_cells rows 1-2).
     0x85128 - 0x8515c  s0 = p + 24 (the announce's name, SPEC_ANN_NAME); spec_strz_len (p + 24): for i = 0 .. 8: when
                      the bitwise not of s0 is below i (unsigned; s0 + i wraps) the trap word; the instrumented check of
                      the 1-byte load at s0 + i (the shadow byte k at ((s0 + i) >> 3) + 0x7fff8000; k = 0 goes on; else
                      ((s0 + i) & 7) < k (signed) goes on; else the error path), then the byte; the first 0 ends the
                      loop with n = i (0x8516c); no 0 among the 9 bytes: the jump at 0x8515c to 0x851a4 (a0 = 0) and
                      the return.
     0x8516c - 0x85170  n <> 8: a0 = 0 (0x851a4) and the return.
     0x85174 - 0x85188  bcmp (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp) at 0x85184 with
                      (p + 24, 0x21060 = TRANS_STR_C24 ("CNTRL|24"), 8); 0 gives a0 = SPEC_C24 = 0xa3a00 (0x851b8) and
                      the return.
     0x8518c - 0x851a0  bcmp at 0x8519c with (p + 24, 0x21080 = TRANS_STR_PC ("MAINUNIT"), 8); 0 gives a0 = SPEC_PC =
                      0xa3a20 (0x851c4) and the return; else a0 = 0.
     0x851a8 - 0x851b4  ra, s0 reloaded, sp = sp + 16, return.
     0x851d0          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path.
   Against image A's code (lib/A/Prog/desk_named_cg.v, 49 words): the same loads, bcmp calls and results, with image
   B's addresses; image B's loop counts i up from 0 to 9 where image A's counts down from 9, and image B's code has
   the UBSan pointer checks image A's does not: the tests at 0x8510c, 0x85110 - 0x85114 and, in the loop, 0x8512c /
   0x85134, all to the trap word at 0x851d0.
  Trap path (from three branches) and the facts that rule it out: p = 0 by 0 < p; p + 24 and p + 24 + i (i <= 8)
   wrap only when p + 33 > 2^64, and every byte the loop reads lies inside body (below), which trans_src_ok places
   below 2^64 (decode_rd_ok: p + length body <= 2^63; a heap block: the allocator's blocks lie below its ceiling).
   No premise is added for them.
   Error path (1 call) and the fact that rules it out: errpath_load1 0x85168 (the call of __asan_report_load1, 0x59504
   = TB___asan_report_load1, with a0 = s0 + i): the model's list_strz_len (skipn 24 body) = Some _ puts every byte the
   loop reads inside body, which trans_src_ok marks usable; bcmp keeps every byte outside its stack window
   [sp - 16 - 2 * ESTACK, sp - 16), which decode_off_win puts body outside. The result: desk_named_m's cases are the
   code's (length 8 and equal to C24_NAME / PC_NAME, read through garr8 of body and trans_rom_view_rd of the strings;
   bcmp's result is 0 exactly when the bytes agree, abcmp_realizes).
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma
   TB___interceptor_trampoline_bcmp. Its ranges: [p + 24, p + 32) (inside body: list_strz_len found the 0 at index 8)
   and [0x21060, 0x21068) / [0x21080, 0x21088), in TRANS_RO_RD. Besides the range's own shadow bytes, abcmp_realizes
   asks every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of
   64 bytes). On image B the two strings are in two groups (image A's share one): TRANS_STR_C24's group
   [0x7fffc208, 0x7fffc210) is the shadow of SPEC_OUI (0x21040) and the string, TRANS_STR_PC's group
   [0x7fffc210, 0x7fffc218) is the shadow of the string and op_frame.CMD (0x210a0). transport_cells gives 0x7fffc208
   (SPEC_OUI, 3), 0x7fffc20c / 0x7fffc210 (0) and 0x7fffc20d / 0x7fffc211 (1), 0x7fffc214 (op_frame.CMD, 7);
   trans_dnamed_cells the ten guard bytes 0x7fffc209 - 0x7fffc20b, 0x7fffc20e, 0x7fffc20f, 0x7fffc212, 0x7fffc213,
   0x7fffc215 - 0x7fffc217 (0xf9), rows of the record (lib/B/YF0m.v Tfib_const_shadow). No program function is called.
   Stack: 16 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 16 (abcmp_realizes): DNAMED_STK.

   The caller is m_rx (the call at 0x84f50, return address 0x84f54; DgnTransportBList.v PCall TB_desk_named): a0 =
   the 8-byte word at m_rx's sp + 48 (f.body of its struct spec_frame at sp + 0, inside the received frame's heap
   block). It supplies the journal, the body's placement and bytes and the model call from its own walk.
   Form: lib/A/Prog/desk_named_cg.v (image A's statement of this function), at image B's entry, strings, results,
   runtime cells and listing names, with trans_dnamed_cells for image B's two shadow groups. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* desk_named's frame (`sp = sp - 16` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use below
   sp - 16 (abcmp_realizes, YG0d.v). *)
Definition DNAMED_FRAME : Z := 16.
Definition DNAMED_STK : Z := DNAMED_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition DNAMED_EV : Z := 0.

(* The two results agree with the image's symbols. *)
Lemma desk_named_results : TI.ti_spec_c24 timg_B = TRANS_SPEC_C24 /\ TI.ti_spec_pc timg_B = TRANS_SPEC_PC.
Proof. split; reflexivity. Qed.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_const_shadow rows) that the bcmp calls need beyond
   transport_cells: the guard granules of the two aligned groups of 8 shadow bytes the two 9-byte strings
   (TRANS_STR_C24 0x21060, TRANS_STR_PC 0x21080) lie in: SPEC_OUI's (0x21040, payload 3) and TRANS_STR_C24's for the
   first, TRANS_STR_PC's and op_frame.CMD's (TRANS_CMD 0x210a0, payload 7) for the second. *)
Definition trans_dnamed_cells (B : asyms) : Prop :=
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_C24 + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_C24 + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_PC + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_PC + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_CMD + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_CMD + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_CMD + 24))) 0xf9) (as_const B ly).
Lemma trans_dnamed_cells_rows :
  map BCells.shadow_addr [TRANS_SPEC_OUI + 8; TRANS_SPEC_OUI + 16; TRANS_SPEC_OUI + 24; TRANS_STR_C24 + 16;
                          TRANS_STR_C24 + 24; TRANS_STR_PC + 16; TRANS_STR_PC + 24; TRANS_CMD + 8; TRANS_CMD + 16;
                          TRANS_CMD + 24] =
  [0x7fffc209; 0x7fffc20a; 0x7fffc20b; 0x7fffc20e; 0x7fffc20f; 0x7fffc212; 0x7fffc213; 0x7fffc215; 0x7fffc216;
   0x7fffc217].
Proof. reflexivity. Qed.

Section dnamed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X:
   a0 = r and the model's world is the world it was given. *)
Definition transport_dnamed_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs DNAMED_STK DNAMED_EV 0
    (fun _ => False) (fun regs2 _ _ => YK11.getr regs2 10 = w64 r /\ Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_desk_named_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p r : Z) (body : list byte) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - DNAMED_STK -> spZ regs <= sp0 ->
    0 < p ->
    garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz body) ->
    trans_src_ok B lyc Sc W memc p (Z.of_nat (length body)) ->
    decode_off_win regs DNAMED_STK p (Z.of_nat (length body)) ->
    trans_rom_view_rd W memc ->
    TC.desk_named_m timg_B Bw body = Some (Bw', r) ->
    st_nev S + k + DNAMED_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_dnamed_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the shadow of the two
   strings and of their group neighbours SPEC_OUI and op_frame.CMD), the guard granules of the two groups
   (trans_dnamed_cells), the two read-only facts of the record (they keep the strings visible through the journal),
   the allocator and meter laws, and the bcmp contract at the listing's trampoline give the contract at
   TB_desk_named. *)
Definition transport_desk_named_cg_holds_stmt : Prop :=
  transport_cells B -> trans_dnamed_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_desk_named_cg (transportb_sigma TB_desk_named).
End dnamed.
