(* host_offset_cg: the ASan walk contract of host_offset (fuzz/fuzz_transport.c:254-262; model lib/TModel/TCb.v
   host_offset_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x85040 = transportb_sigma TB_host_offset, size 192,
   as STATEMENTS only (no proof). Image B only: image A's and the plain image's m_rx inline it (lib/Prog/T/m_rx_c.v;
   lib/Prog/T/m_rx_ann.v mrx_loopl), so no plain contract or image-A statement of this function exists. It stores into
   no harness global and calls the bcmp wrapper, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v
   decode_cg_post over the caller's donor journal ajournal); a G-form caller lifts it with
   lib/A/Prog/TransportGCg.v gx_call_cg. Form: the nearest image-A sibling of the family, lib/A/Prog/desk_named_cg.v (a
   donor-form reader of m_rx's announce body that calls only the bcmp wrapper), at this function's argument and model.

   The contract. a0 = p, not 0, with the bytes body at p (from the announce's body to the end of its block), placed
   by trans_src_ok and outside this call's stack window (decode_off_win); the read-only bytes it compares (HOST) read
   as the image's (trans_rom_view_rd); host_offset_m Bw body = Some (Bw', r). The function returns to ra with a0 = r
   (the offset i in 0 .. 9 of the first 6 bytes of body + i equal to HOST, or -1), the callee-saved registers kept, no
   allocator event, no meter charge, every byte outside its stack window kept (it stores nothing outside its own
   frame: E is empty), and Bw' = Bw (the model's: host_offset_m returns its world). The function reads no harness
   global (measured: it loads nothing itself; the bcmp wrapper reads [p + i, p + i + 6) and HOST), so the statement
   has no world relation.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 192 code bytes of this function are equal in both files),
   48 words:
     0x85040          sp = sp - 80; ra, s0 .. s7 at sp + 72 .. sp + 8 (0x85044 - 0x85064), loaded back at 0x850d0 -
                      0x850f0 (sp = sp + 80 at 0x850f4, return at 0x850f8); no side-stack frame, no frame pointer.
     0x85068 - 0x85088  s1 = p; s0 = i = 0; s4 = -p; s5 = 10 (the rounds left); s6 = (p <> 0); s2 = HOST = 0x20fe0 =
                      TRANS_HOST (the auipc / addi pair at 0x8507c); s3 = s7 = p (p + i).
     0x8508c - 0x8509c  one round per i = 0 .. 9 (fuzz_transport.c:258): a0 = (p + i = 0 mod 2^64); s6 = a0 goes to the
                      trap word at 0x850fc (the UBSan check of body + i: a nonzero p whose p + i wraps to 0, or p = 0 with
                      i <> 0); p + i below p (unsigned; it wraps) goes to the trap word.
     0x850a0 - 0x850b0  bcmp (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp) at 0x850ac with
                      (p + i, HOST, 6); 0 goes to 0x850cc: a0 = i and the return.
     0x850b4 - 0x850c4  i = the sign-extended low 32 bits of i + 1 (addiw), s5 = s5 - 1, s7 = s7 + 1, s3 = s3 + 1; s5 <> 0
                      goes back to 0x8508c.
     0x850c8 - 0x850cc  ten misses: a0 = -1 and the return.
     0x850fc          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path.
   Trap path (from two branches) and the facts that rule it out: 0 < p gives p <> 0 (the first branch then needs
   p + i = 0 mod 2^64); p + i wraps only when p + i >= 2^64, and on every run the model allows to reach round i it
   puts [p + i, p + i + 6) inside body (host_offset_loop is None when length body < i + 6), which trans_src_ok places
   below 2^64 (decode_rd_ok: p + length body <= 2^63; a heap block: the allocator's blocks lie below its ceiling).
   0 < p is the one premise the UBSan check asks for; desk_named's statement (the form) has it too.
   No error path: the function makes no instrumented access of its own (its only loads and stores are of its frame).
   The result: host_offset_m's rounds are the code's (round i runs when the model's i + SPEC_MAC <= SPEC_ANN_UNKNOWN,
   that is i <= 9, the code's ten rounds; beq_bytes (sub body i 6) HOST, read through garr8 of body and
   trans_rom_view_rd of HOST; bcmp's result is 0 exactly when the bytes agree, abcmp_realizes).
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma
   TB___interceptor_trampoline_bcmp. Its ranges: [p + i, p + i + 6) (inside body: the model's length test) and
   [0x20fe0, 0x20fe6) = HOST, in TRANS_RO_RD. Besides the range's own shadow bytes, abcmp_realizes asks every shadow
   byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of 64 bytes). HOST's
   group [0x7fffc1f8, 0x7fffc200) is the shadow of [0x20fc0, 0x21000): the redzone of LLVMFuzzerTestOneInput.SCALE
   (TRANS_SCALE 0x20fa0, payload 32) and HOST. transport_cells gives 0x7fffc1fc (HOST, 6); trans_hoff_cells the seven
   guard bytes 0x7fffc1f8 - 0x7fffc1fb and 0x7fffc1fd - 0x7fffc1ff (0xf9), rows of the record (lib/B/YF0m.v
   Tfib_const_shadow). The ranges of body come with the caller's facts (trans_src_ok). No program function is called.
   Stack: 80 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 80 (abcmp_realizes): HOFF_STK.

   The caller is m_rx (the call at 0x84d64, return address 0x84d68; DgnTransportBList.v PCall TB_host_offset): a0 =
   the 8-byte word at m_rx's sp + 48 (f.body of its struct spec_frame at sp + 0, inside the received frame's heap
   block), on a frame whose command is e1 (0xe1) and whose body has at least 33 bytes. It supplies the journal, the
   body's placement and bytes and the model call from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* host_offset's frame (`sp = sp - 80` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use below
   sp - 80 (abcmp_realizes, YG0d.v). *)
Definition HOFF_FRAME : Z := 80.
Definition HOFF_STK : Z := HOFF_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition HOFF_EV : Z := 0.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_const_shadow rows) that the bcmp calls need beyond
   transport_cells: the rest of the aligned group of 8 shadow bytes HOST (TRANS_HOST 0x20fe0, payload 6) lies in, the
   redzone of LLVMFuzzerTestOneInput.SCALE (TRANS_SCALE 0x20fa0, payload 32; redzone [0x20fc0, 0x20fe0)) and HOST's
   own guard granules. *)
Definition trans_hoff_cells (B : asyms) : Prop :=
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 40))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 48))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 56))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 24))) 0xf9) (as_const B ly).
Lemma trans_hoff_cells_rows :
  map BCells.shadow_addr [TRANS_SCALE + 32; TRANS_SCALE + 40; TRANS_SCALE + 48; TRANS_SCALE + 56; TRANS_HOST;
                          TRANS_HOST + 8; TRANS_HOST + 16; TRANS_HOST + 24] =
  [0x7fffc1f8; 0x7fffc1f9; 0x7fffc1fa; 0x7fffc1fb; 0x7fffc1fc; 0x7fffc1fd; 0x7fffc1fe; 0x7fffc1ff].
Proof. reflexivity. Qed.

Section hoff. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X:
   a0 = r and the model's world is the world it was given. *)
Definition transport_hoff_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs HOFF_STK HOFF_EV 0
    (fun _ => False) (fun regs2 _ _ => YK11.getr regs2 10 = w64 r /\ Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_host_offset_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p r : Z) (body : list byte) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - HOFF_STK -> spZ regs <= sp0 ->
    0 < p ->
    garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz body) ->
    trans_src_ok B lyc Sc W memc p (Z.of_nat (length body)) ->
    decode_off_win regs HOFF_STK p (Z.of_nat (length body)) ->
    trans_rom_view_rd W memc ->
    TC.host_offset_m Bw body = Some (Bw', r) ->
    st_nev S + k + HOFF_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_hoff_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the runtime cells (HOST's shadow), the rest of HOST's shadow group
   (trans_hoff_cells), the two read-only facts of the record (they keep HOST visible through the journal), the
   allocator and meter laws, and the bcmp contract at the listing's trampoline give the contract at TB_host_offset. *)
Definition transport_host_offset_cg_holds_stmt : Prop :=
  transport_cells B -> trans_hoff_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_host_offset_cg (transportb_sigma TB_host_offset).
End hoff.
