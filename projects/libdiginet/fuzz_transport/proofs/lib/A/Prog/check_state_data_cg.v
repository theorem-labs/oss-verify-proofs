(* check_state_data_cg: the ASan walk contract of check_state_data (fuzz/fuzz_transport.c:559-569; model
   lib/TModel/TCb.v check_state_data_m) on fuzz_transport.asan (e89be137db17) at 0x85638 =
   transport_sigma TS_check_state_data, size 424, as STATEMENTS only (no proof). It stores into no harness global and
   calls the bcmp wrapper, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post over
   the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = p, a struct diginet_notice n of 72 bytes (trans_ntc_at: lib/Prog/T/TContract.v ntc_at read
   through the walk's image view, each range it names placed by trans_src_ok and outside this call's stack window);
   Fr the current heap frame (trans_tframe_at: TContract.v tframe_at in the same form). The memory relates to the
   world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), and
   check_state_data_m Fr Bw n = Some (Bw', tt). The function returns to ra with the callee-saved registers kept, no
   allocator event, no meter charge, every byte outside its stack window kept (it stores nothing outside its own
   frame: E is empty), and Bw' = Bw. This is what the plain contract (lib/Prog/T/check_state_data_c.v) says: void;
   B' = B and wmem rsegs m' B; munch of the frame only. Its ntc_at / tframe_at / wmem premises become trans_ntc_at /
   trans_tframe_at / tw_at (their off_world clauses are not needed: the function writes no byte the world holds), and
   mem_inv is dropped.
   The two premises the plain contract does not have. First, trans_src_ok and decode_off_win of [y, y + n.body_len),
   y = OW.dn[GOT.ndata].body. The bcmp at 0x856f0 compares n.body_len bytes at y; for n.body_len > 0 the model's
   frame_read puts them inside Fr, but for n.body_len = 0 frame_read asks nothing of y, while the bcmp wrapper's
   contract needs 0 <= y, y <= 2 ^ 63 and amem_range y 0 (abcmp_realizes). m_rx stores into OW.dn[k].body only
   addresses in [tf_addr, tf_addr + length tf_bytes] of the frame it receives (tf_addr + the body offset; the end
   address included), and op_begin clears OW, so the caller supplies it from that invariant (decode_in_block of a
   range of the frame's heap block, of length 0 when n.body_len = 0). Second, n.body_len < 2 ^ 32: the bcmp
   wrapper's contract needs 0 <= n.body_len < 2 ^ 32 (abcmp_realizes). The model gives 0 <= n.body_len (frame_read
   is None at a negative length), but no other premise bounds it above: trans_ntc_at's trans_src_ok of the body
   allows the machine stack [ly_stk_lo, ly_stk_hi), whose length layout_ok (YG0f.v) does not bound below 2 ^ 32.
   notice carries the bound for a data notice; the one builder of a data notice (TSess.v on_data_m) sets body_len
   to the frame's fr_body_len, numbytes - 16 with numbytes a 16-bit field (DgnSpec.v), so on_data's walk has it
   from the frame.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 106 words:
     0x85638          sp = sp - 32; ra, s0 .. s2 at sp + 24 .. sp + 0 (0x8563c - 0x85648), loaded back at 0x85760 -
                      0x8576c; no side-stack frame, no frame pointer. s0 = p (0x8565c).
     0x8564c - 0x85658  g = GOT.ndata (the 4-byte load at GOT + 220 = 0x5e53bc, no instrumented check); g > 1 (signed)
                      goes to the trap.
     0x85660 - 0x8566c  a3 = OW (0x5f3060); OW.ndata (OW + 220, no instrumented check) <= g (signed) goes to the trap.
     0x85670 - 0x85678  s2 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte load
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path. An 8-byte load goes on only
                      at k = 0.
     0x8567c - 0x856bc  the checks of the 8-byte loads at p + 56 (n->body_len) and OW + 264 + 24 g (OW.dn[g].len); they
                      differ: the trap.
     0x856c0 - 0x856f4  the checks of the 8-byte loads at p + 48 (n->body) and OW + 256 + 24 g (OW.dn[g].body); bcmp
                      (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x856f0 with (n->body,
                      OW.dn[g].body, n->body_len); a result not 0 goes to the trap.
     0x856f8 - 0x85728  the checks of the 4-byte loads at p + 64 (n->counter) and OW + 272 + 24 g (OW.dn[g].counter);
                      they differ: the trap.
     0x8572c - 0x8575c  the checks of the 2-byte loads at p + 68 (n->retry) and OW + 276 + 24 g (OW.dn[g].retry); they
                      differ: the trap; else the return at 0x85774 (a0 not stated: void).
   The trap: 0x85778 call of before_abort (0x5a4c4), 0x8577c call of abort (0x93734); every branch to it is ruled out
   by check_state_data_m Fr Bw n = Some _: its tests are the code's tests, read through tw_at (GOT_ndata, OW_ndata,
   OW_dn_len / _body / _counter / _retry), trans_ntc_at (n's fields and body bytes) and trans_tframe_at with
   frame_read (the bytes at OW.dn[g].body), and bcmp's result is 0 exactly when the bytes agree (abcmp_realizes).
   Error paths (8 calls) and the facts that rule them out: errpath_load8 0x857c8 (p + 56), 0x857d4 (p + 48),
   errpath_load4 0x8578c (p + 64), errpath_load2 0x857b0 (p + 68): the 72 bytes at p are marked usable (trans_ntc_at's
   trans_src_ok) and p mod 8 = 0, so each 8-byte load reads one whole granule, whose shadow byte is 0; errpath_load8
   0x857d0, 0x857dc, errpath_load4 0x857a0, errpath_load2 0x857c4 (OW.dn[g]'s fields): 0 <= g <= 1 (the code's test
   and the model's g <? 0), so the 24 bytes of OW.dn[g] lie in OW's payload [OW, OW + 304), whose shadow is 0
   (trans_csdata_cells). bcmp keeps every byte outside its stack window [sp - 32 - 2 * ESTACK, sp - 32), which
   decode_off_win puts p's 72 bytes outside.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp. Its ranges: [n->body, + n.body_len) inside the n_body bytes (the model's
   length (n_body n) >= n_body_len n; trans_ntc_at's trans_src_ok) and [OW.dn[g].body, + n.body_len) (the first
   premise above). No program function is called.
   Stack: 32 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 32 (abcmp_realizes): CSDATA_STK.

   The caller is notice (the call at 0x83600, return address 0x83604, for a data notice): a0 = its argument n. It
   supplies the journal, the world relation, the model call and the notice, frame and OW.dn facts from its own walk.

   Also defined here: trans_ntc_at and trans_tframe_at (notice and check_state_desk use them), the ASan forms of
   lib/Prog/T/TContract.v ntc_at and tframe_at; and trans_tf_off_g, the part of tframe_at's off_world clause that
   trans_tframe_at drops (no byte of the frame is a byte of G), which io_recv, on_ack, on_data, diginet_session_wake,
   diginet_session_close, on_announce and diginet_session_rx take: each reads the frame, or hands it to a callee,
   after a G-form callee. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_state_data's frame (`sp = sp - 32` at its entry; no realignment) and the 2 * ESTACK its bcmp call uses below
   sp - 32 (abcmp_realizes, YG0d.v). *)
Definition CSDATA_FRAME : Z := 32.
Definition CSDATA_STK : Z := CSDATA_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CSDATA_EV : Z := 0.
(* struct diginet_notice: 72 bytes; its announce's version and name: 10 + 10 bytes (TContract.v ntc_at). *)
Definition NTC_SIZE : Z := 72.
Definition ANN_SIZE : Z := 20.

(* The shadow of OW's payload (304 bytes, 38 whole granules) is 0: a range of the record's as_zero_shadow. The code's
   instrumented loads read OW.dn[g]. *)
Definition trans_csdata_cells (B : asyms) : Prop := decode_zshadow_at B TA_OW (TA_OW + TW.SZ_OW).

Section csdata. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The current heap frame F, as lib/Prog/T/TContract.v tframe_at gives it, read through the walk's image view: None
   asks nothing; Some fr: tf_addr is not 0, the bytes tf_bytes lie there (garr8), trans_src_ok of the range (it is
   receive's heap block), and the range lies outside the callee's stack window [sp - K, sp). *)
Definition trans_tframe_at (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (regs : bvmap 5 word) (K : Z) (F : option TI.tframe) : Prop :=
  match F with
  | None => True
  | Some fr =>
      0 < TI.tf_addr fr /\
      garr8 segs (mrestrict (w_H W) memc) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr)) /\
      trans_src_ok B lyc Sc W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) /\
      decode_off_win regs K (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr)))
  end.

(* The part of lib/Prog/T/TContract.v tframe_at's off_world clause that trans_tframe_at drops (trans_src_ok admits a
   range of G): no byte of F is a byte of G (TransportG.v G_HARNESS; the plain clause puts F outside
   [W_BASE_PLAIN, W_BASE_PLAIN + W_LEN), the plain image of the 18 globals, which on image A is G). A walk that reads
   F, or hands F to a callee, after a call of a G-form callee (TransportGCg.v transport_cg_post or
   transport_cg_post_out) needs it: that callee's acall_kept_g keeps the image bytes outside G only, and its X ties
   the bytes of G to the model world only, so it carries neither the bytes nor the placement of an F inside G.
   Outside G, the block, frame, stack and image clauses of acall_kept_g carry them (DgnTransportCg.v
   trans_src_ok_kept), with the walk's own fact that F lies outside the callee's written range. The caller takes it
   from the plain tframe_at's off_world clause. *)
Definition trans_tf_off_g (F : option TI.tframe) : Prop :=
  forall fr, F = Some fr ->
    forall x, TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
      ~ W_journalG.inG TransportG.G_HARNESS x.

(* A struct diginet_notice at p, as lib/Prog/T/TContract.v ntc_at gives it, read through the walk's image view: the
   scalar fields, the personality pointer's value, the body bytes at the body pointer, and the announce (NULL exactly
   when n_ann = None; else 8-aligned, with the version bytes at it and the name bytes 10 further). The struct, the
   body and the announce are each placed by trans_src_ok and lie outside the callee's stack window [sp - K, sp). *)
Definition trans_ntc_at (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (regs : bvmap 5 word) (K p : Z) (n : TI.ntc) : Prop :=
  0 < p /\ p mod 8 = 0 /\
  trans_src_ok B lyc Sc W memc p NTC_SIZE /\ decode_off_win regs K p NTC_SIZE /\
  exists NB : list byte, garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz NB) /\ length NB = 72%nat /\
    TW.s32_at NB 0 = TI.n_kind n /\ TW.s32_at NB 4 = TI.n_state n /\ TW.s32_at NB 8 = TI.n_old n /\
    TW.s32_at NB 12 = TI.n_reason n /\
    TW.u_at NB 32 8 = TI.n_pers n /\ TW.s32_at NB 40 = TI.n_mac_offset n /\ TW.u_at NB 56 8 = TI.n_body_len n /\
    TW.u_at NB 64 4 = TI.n_counter n /\ TW.u_at NB 68 2 = TI.n_retry n /\
    garr8 segs (mrestrict (w_H W) memc) (TW.u_at NB 48 8) (map DSpec.bz (TI.n_body n)) /\
    trans_src_ok B lyc Sc W memc (TW.u_at NB 48 8) (Z.of_nat (length (TI.n_body n))) /\
    decode_off_win regs K (TW.u_at NB 48 8) (Z.of_nat (length (TI.n_body n))) /\
    match TI.n_ann n with
    | None => TW.u_at NB 24 8 = 0
    | Some an =>
        0 < TW.u_at NB 24 8 /\ TW.u_at NB 24 8 mod 8 = 0 /\
        garr8 segs (mrestrict (w_H W) memc) (TW.u_at NB 24 8) (map DSpec.bz (TI.ta_version an)) /\
        garr8 segs (mrestrict (w_H W) memc) (TW.u_at NB 24 8 + 10) (map DSpec.bz (TI.ta_name an)) /\
        trans_src_ok B lyc Sc W memc (TW.u_at NB 24 8) ANN_SIZE /\
        decode_off_win regs K (TW.u_at NB 24 8) ANN_SIZE
    end.

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_csdata_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CSDATA_STK CSDATA_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_state_data_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CSDATA_STK -> spZ regs <= sp0 ->
    trans_ntc_at lyc Sc W memc regs CSDATA_STK p n ->
    trans_tframe_at lyc Sc W memc regs CSDATA_STK Fr ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_state_data_m Fr Bw n = Some (Bw', tt) ->
    trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) ->
    decode_off_win regs CSDATA_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) ->
    TI.n_body_len n < 2 ^ 32 ->
    st_nev S + k + CSDATA_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_csdata_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), OW's shadow, the
   allocator and meter laws, and the bcmp contract at the listing's trampoline give the contract at
   TS_check_state_data. *)
Definition transport_check_state_data_cg_holds_stmt : Prop :=
  transport_cells B -> trans_csdata_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_check_state_data_cg (transport_sigma TS_check_state_data).
End csdata.
