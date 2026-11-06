(* desk_named_cg: the ASan walk contract of desk_named (fuzz/fuzz_transport.c:265-273, spec_strz_len inlined; model
   lib/TModel/TCb.v desk_named_m) on fuzz_transport.asan (e89be137db17) at 0x84f40 = transport_sigma TS_desk_named,
   size 196, as STATEMENTS only (no proof). It stores into no harness global and calls the bcmp wrapper, so it takes
   decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post over the caller's donor journal
   ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = p, not 0, with the bytes body at p (from the announce's body to the end of its block),
   placed by trans_src_ok and outside this call's stack window (decode_off_win); the two read-only strings it compares
   read as the image's (trans_rom_view_rd); desk_named_m timg_A Bw body = Some (Bw', r) (lib/A/Prog/TImgA.v timg_A:
   ti_spec_c24 = SPEC_C24 = 0xa3da0, ti_spec_pc = SPEC_PC = 0xa3dc0). The function returns to ra with a0 = r, the
   callee-saved registers kept, no allocator event, no meter charge, every byte outside its stack window kept (it
   stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/desk_named_c.v) says: a0 = r; B' = B and wmem rsegs m' B; munch of the frame only. Its bytes_at /
   off_window premises become garr8 + trans_src_ok + decode_off_win, timg_plain becomes timg_A, and mem_inv is
   dropped. Its wmem premise has no counterpart: the function reads no byte of a harness global (measured:
   its only loads are of p + 24 .. p + 32, the runtime cells and, in the wrapper, the read-only strings), and the
   model's result does not depend on Bw; Bw' = Bw is the model's.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 49 words:
     0x84f40          sp = sp - 16; ra at sp + 8, s0 at sp + 0 (0x84f44, 0x84f48), loaded back at 0x84fdc, 0x84fe0;
                      no side-stack frame, no frame pointer.
     0x84f4c - 0x84f54  a1 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x84f58 - 0x84f9c  s0 = p + 24 (the announce's name, SPEC_ANN_NAME); spec_strz_len (p + 24): for i = 0 .. 8 the
                      instrumented check of the 1-byte load at p + 24 + i (the shadow byte k at (a >> 3) + 0x7fff8000;
                      k = 0 goes on; else (a & 7) < k (signed) goes on; else the error path), then the byte; the first 0
                      ends the loop (a2 = 9 - i); no 0 among the 9 bytes: the jump at 0x84f90 to 0x84fd8 (a0 = 0) and
                      the return.
     0x84fa0 - 0x84fa4  a length other than 8 (a2 <> 1): a0 = 0 (0x84fd8) and the return.
     0x84fa8 - 0x84fbc  bcmp (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x84fb8 with (p + 24,
                      0x210c0 = TRANS_STR_C24 ("CNTRL|24"), 8); 0 gives a0 = SPEC_C24 = 0xa3da0 (0x84fec) and the
                      return.
     0x84fc0 - 0x84fd4  bcmp at 0x84fd0 with (p + 24, 0x210e0 = TRANS_STR_PC ("MAINUNIT"), 8); 0 gives a0 = SPEC_PC =
                      0xa3dc0 (0x84ff8) and the return; else a0 = 0.
     0x84fdc - 0x84fe8  ra, s0 reloaded, sp = sp + 16, return.
   No trap path. Error path (1 call) and the fact that rules it out: errpath_load1 0x84f9c (p + 24 + i): the model's
   list_strz_len (skipn 24 body) = Some _ puts every byte the loop reads inside body, which trans_src_ok marks usable;
   bcmp keeps every byte outside its stack window [sp - 16 - 2 * ESTACK, sp - 16), which decode_off_win puts body
   outside. The result: desk_named_m's cases are the code's (length 8 and equal to C24_NAME / PC_NAME, read through
   garr8 of body and trans_rom_view_rd of the strings; bcmp's result is 0 exactly when the bytes agree,
   abcmp_realizes).
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp. Its ranges: [p + 24, p + 32) (inside body: list_strz_len found the 0 at index 8)
   and [0x210c0, 0x210c8) / [0x210e0, 0x210e8), in TRANS_RO_RD. Besides the range's own shadow bytes, abcmp_realizes
   asks every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of
   64 bytes): both strings' group is [0x7fffc218, 0x7fffc220); transport_cells gives 0x7fffc218 / 0x7fffc21c (0) and
   0x7fffc219 / 0x7fffc21d (1), trans_dnamed_cells the four guard bytes 0x7fffc21a, 0x7fffc21b, 0x7fffc21e, 0x7fffc21f
   (0xf9), rows of the record (lib/A/AF0m.v Tfib_const_shadow). No program function is called.
   Stack: 16 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 16 (abcmp_realizes): DNAMED_STK.

   The caller is m_rx (the call at 0x84dc4, return address 0x84dc8): a0 = s0 (f.body, inside the received frame's
   heap block). It supplies the journal, the body's placement and bytes and the model call from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
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
Lemma desk_named_results : TI.ti_spec_c24 timg_A = TRANS_SPEC_C24 /\ TI.ti_spec_pc timg_A = TRANS_SPEC_PC.
Proof. split; reflexivity. Qed.

(* The shadow facts of the record (lib/A/AF0m.v Tfib_const_shadow rows) that the bcmp calls need beyond
   transport_cells: the guard granules of the two 9-byte strings (TRANS_STR_C24 0x210c0, TRANS_STR_PC 0x210e0), which
   share the aligned group of 8 shadow bytes of their payloads. *)
Definition trans_dnamed_cells (B : asyms) : Prop :=
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TRANS_STR_C24 + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_STR_C24 + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_STR_PC + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_STR_PC + 24))) 0xf9) (as_const B ly).
Lemma trans_dnamed_cells_rows :
  map ACells.shadow_addr [TRANS_STR_C24 + 16; TRANS_STR_C24 + 24; TRANS_STR_PC + 16; TRANS_STR_PC + 24] =
  [0x7fffc21a; 0x7fffc21b; 0x7fffc21e; 0x7fffc21f].
Proof. reflexivity. Qed.

Section dnamed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X:
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
    TC.desk_named_m timg_A Bw body = Some (Bw', r) ->
    st_nev S + k + DNAMED_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_dnamed_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the shadow of the two
   strings), the strings' guard granules (trans_dnamed_cells), the two read-only facts of the record (they keep the
   strings visible through the journal), the allocator and meter laws, and the bcmp contract at the listing's
   trampoline give the contract at TS_desk_named. *)
Definition transport_desk_named_cg_holds_stmt : Prop :=
  transport_cells B -> trans_dnamed_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_desk_named_cg (transport_sigma TS_desk_named).
End dnamed.
