(* notice_cg: the ASan walk contract of notice (fuzz/fuzz_transport.c:937-973; model lib/TModel/TCb.v notice_m) on
   fuzz_transport.asan (e89be137db17) at 0x83578 = TImgA.v ti_notice timg_A (the twin's symbol notice, size 600;
   transport_text + AF_notice in DgnTransportList.v; transport_obj 10 in DgnTransportAddr.v), as STATEMENTS only (no
   proof). It stores into GOT and M, two harness globals, and calls five harness check functions, so it is a G-form
   caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v
   G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS).

   notice is reached only through the session's notify pointer (struct diginet_session + 96, which
   diginet_session_init stores from its a3; LLVMFuzzerTestOneInput forms 0x83578 at 0x815dc and passes it). The
   indirect call sites are diginet_session_wake 0x86adc, diginet_session_close 0x87394,
   on_announce 0x87e48, 0x87f50, 0x880b0, 0x88184, on_ack 0x88674, on_data 0x88c9c, session_lost 0x8910c,
   diginet_session_tick 0x895ec, 0x898d0, 0x899d4, maybe_online 0x8b3d4. Each reads the pointer from the world
   (tw_read of S_notify; the model's call_notify, TSess.v, compares it with ti_notice timg_A) and applies this
   statement at that address, with a0 = the notify context (not read) and a1 = the address of the struct
   diginet_notice it built.

   The contract. a1 = p, a struct diginet_notice n (check_state_data_cg.v trans_ntc_at); Fr the current heap frame
   (check_state_data_cg.v trans_tframe_at); the read-only bytes the callees read (notice's own kind table,
   personalities[], SPEC_C24, SPEC_PC) read as the image's (trans_rom_view_rd). The memory relates to the world Bw by
   image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), and
   notice_m timg_A Fr Bw n = Some (Bw', tt). The function returns to ra with the callee-saved registers kept, no
   allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g
   G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - NOTICE_STK, sp), the
   image bytes outside G, the owned statics and errno, the caller's block and frame bytes outside notice_wr Bw n),
   and the world relation at Bw'. This is what the plain contract (lib/Prog/T/notice_c.v) says: void; wmem rsegs m'
   B' with B' the model's world; munch of the frame and the world only. Its premises become: ntc_at -> trans_ntc_at,
   tframe_at -> trans_tframe_at, relro_img -> trans_rom_view_rd, wmem -> tw_at, timg_plain -> timg_A; the off_world
   clauses of ntc_at and tframe_at -> notice_apart (no byte the call stores is a byte of the struct, of its body, of
   its announce or of Fr: the ranges a callee reads or names after a store); mem_inv is dropped.
   The one premise the plain contract does not have: for a data notice (n_kind n = N_DATA), the two premises
   check_state_data_cg.v adds: its run invariant on the OW.dn[GOT.ndata].body range (trans_src_ok and decode_off_win
   of [OW_dn_body Bw (GOT_ndata Bw), + n_body_len n)) and n_body_len n < 2 ^ 32 (the bcmp wrapper's length bound),
   stated on notice's own Bw and window; notice calls check_state_data before it stores anything, so the range and
   the world are the callee's (a caller carries it). The caller of a data notice (on_data) has
   the bound from the frame: the notice's body_len is the frame's fr_body_len (TSess.v on_data_m), numbytes - 16
   with numbytes a 16-bit field.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   600 code bytes and the 24 bytes of its table at 0x20fcc are equal in both files), 150 words:
     0x83578 - 0x8357c sp = sp - 16; ra at sp + 8, loaded back at 0x835dc, 0x8362c, 0x83710 and 0x8372c. No side-stack
                      frame, no frame pointer, no other register saved. a1 = p until 0x836bc on the N_STATE path,
                      until the call or tail jump on the N_DESK, N_ACK_LOST, N_DATA and N_ACKED paths, and until
                      0x83720 on the N_FOREIGN path.
     0x83580 - 0x83588 a5 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; else the error path. No check guards an access at a constant
                      address of GOT or M.
     0x8358c - 0x8359c the check of the 4-byte load at p; a0 = n->kind (4-byte signed load at p).
     0x835a0 - 0x835c4 n->kind - 1 > 5 (unsigned) goes to 0x8372c (the default, :970-971); else the jump through the
                      table TRANS_JT_NOTICE 0x20fcc (6 entries of 4 bytes, each added to 0x20fcc, plain loads; a
                      TRANS_RO_RD range): kind 1 (N_DESK) 0x835c8, 2 (N_STATE) 0x83638, 3 (N_DATA) 0x835fc,
                      4 (N_ACKED) 0x83618, 5 (N_ACK_LOST) 0x835e8, 6 (N_FOREIGN) 0x8371c.
     0x835c8 - 0x835e4 N_DESK (:959-961): the 4-byte load of GOT.desk (0x5e53b0 = GOT + 208), + 1, stored back; a0 = p;
                      ra loaded back, sp = sp + 16; jump (no link) to check_state_desk (0x8538c) at 0x835e4.
     0x835e8 - 0x835f8 N_ACK_LOST (:955-957): a0 = p; call of check_inflight_lost (0x852e4) at 0x835ec, return address
                      0x835f0; the 4-byte store of 0 at M.fly.on (0x5df1c0 = M + 96); to 0x8372c.
     0x835fc - 0x83614 N_DATA (:963-965): a0 = p; call of check_state_data (0x85638) at 0x83600, return address
                      0x83604; GOT.ndata (0x5e53bc = GOT + 220) + 1, stored back; to 0x8372c.
     0x83618 - 0x83634 N_ACKED (:951-953): GOT.acked (0x5e53b8 = GOT + 216) + 1, stored back; a0 = p; ra loaded back,
                      sp = sp + 16; jump (no link) to check_inflight_acked (0x85240) at 0x83634.
     0x83638 - 0x8364c N_STATE (:941-949): a6 = GOT (0x5e52e0); g = GOT.n (4-byte signed load at GOT + 0); a0 = p + 4;
                      15 < g (signed) goes to 0x836ec.
     0x83650 - 0x836e8 (:943-945) x = GOT + 12 g: the check of the 4-byte load at p + 4 and of the 4-byte store at
                      x + 4, the store of n->state at x + 4 (GOT.t[g].state); the same for p + 8 and x + 8
                      (GOT.t[g].old = n->old_state) and for p + 12 and x + 12 (GOT.t[g].reason = n->reason).
     0x836ec - 0x836f0 the 4-byte store of g + 1 at GOT + 0 (GOT.n++, :947).
     0x836f4 - 0x83718 the check of the 4-byte load at p + 4; n->state <> 2 (S_ONLINE) goes to 0x8372c; else ra loaded
                      back, sp = sp + 16, jump (no link) to check_state_online (0x8520c) at 0x83718.
     0x8371c - 0x83728 N_FOREIGN (:967-968): GOT.foreign (0x5e53b4 = GOT + 212) + 1, stored back.
     0x8372c - 0x83734 ra loaded back, sp = sp + 16, return (a0 .. a7 not stated: void).
   The model and the code: the dispatch and every test is notice_m's (n_kind n, GOT_n Bw < TRANS_MAX, n_state n =
   S_ONLINE), read through tw_at and trans_ntc_at; each store is the model's set_GOT_* / set_M_fly_on (put 4 of the
   low 32 bits). The code has no trap of its own: the model's None cases are GOT.n < 0 on the record path (the code
   would store outside GOT's payload: the error path) and the increments at INT_MAX (the code wraps), and each callee's
   traps are ruled out by its contract's model premise, which notice_m's branch supplies (check_state_desk_m timg_A
   Fr at the world after GOT.desk++, check_inflight_lost_m and check_state_data_m at Bw, check_inflight_acked_m after
   GOT.acked++, check_state_online_m after the record and GOT.n++).
   Error paths (8 calls) and the facts that rule them out:
     TS___asan_report_load4 0x83748 (p), 0x83758 and 0x83768 (p + 4), 0x83790 (p + 8), 0x837b8 (p + 12): the 72 bytes
       at p are marked usable (trans_ntc_at's trans_src_ok: a heap block, AR's shadow law; else decode_rd_ok) and
       p mod 8 = 0, so each 4-byte load lies in one granule.
     TS___asan_report_store4 0x8377c (x + 4), 0x837a4 (x + 8), 0x837cc (x + 12): on this path 0 <= g <= 15 (the code's
       test and the model's None at g < 0), so [x + 4, x + 16) lies in [GOT + 4, GOT + 196), inside GOT's payload,
       4-aligned, whose shadow is 0 (trans_notice_cells).
   Callee texts assumed (pc order): check_state_desk as check_state_desk_cg.v transport_check_state_desk_cg at
   transport_sigma TS_check_state_desk (tail jump at 0x835e4, from notice's entry sp and ra; a donor-form callee,
   through TransportGCg.v gx_call_cg); check_inflight_lost as check_inflight_lost_cg.v
   transport_check_inflight_lost_cg (a leaf, read through DgnTransportCg.v transport_leaf_at; call at 0x835ec,
   through gx_call_leaf and the leaf bridge); check_state_data as check_state_data_cg.v transport_check_state_data_cg
   at transport_sigma TS_check_state_data (call at 0x83600; gx_call_cg); check_inflight_acked as
   check_inflight_acked_cg.v transport_check_inflight_acked_cg (leaf; tail jump at 0x83634); check_state_online as
   check_state_online_cg.v transport_check_state_online_cg (leaf; tail jump at 0x83718). A donor callee keeps every
   byte of G (gx_call_cg: gx_ok and gx_noerrno), so the world relation after it is the one it was handed.
   Stack: 16 bytes of its own; the tail jumps run from the entry sp (check_state_desk's CSDESK_STK, a leaf's ESTACK);
   the calls run from sp - 16 (check_state_data's CSDATA_STK, a leaf's ESTACK): NOTICE_STK = 48 + 2 * ESTACK. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_inflight_lost_cg check_inflight_acked_cg check_state_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_lost_cg.
Module LIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_acked_cg.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_online_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* notice's entry: the value the model's call_notify tests the session's notify pointer against. *)
Lemma notice_at : TI.ti_notice timg_A = 0x83578 /\ TI.ti_notice timg_A = transport_obj 10.
Proof. split; reflexivity. Qed.

(* notice's frame (`sp = sp - 16` at its entry; no realignment). The tail jumps (check_state_desk, check_inflight_acked,
   check_state_online) run from the entry sp, the calls (check_inflight_lost, check_state_data) from sp - 16; a
   leaf's window is ESTACK. *)
Definition NOTICE_FRAME : Z := 16.
Definition NOTICE_STK : Z := Z.max (Z.max CSDESK_STK ESTACK) (NOTICE_FRAME + Z.max CSDATA_STK ESTACK).
Lemma notice_stk_eq : NOTICE_STK = NOTICE_FRAME + CSDATA_STK /\ NOTICE_STK = CSDESK_STK.
Proof. split; reflexivity. Qed.
(* No allocator event: neither notice nor a callee calls malloc or free or takes a side-stack frame. *)
Definition NOTICE_EV : Z := 0.

(* The bytes the code stores into G, exactly, by the notice's kind (notice_m): N_STATE: GOT.t[GOT.n] (12 bytes) when
   0 <= GOT.n < TRANS_MAX, and GOT.n; N_ACKED: GOT.acked; N_ACK_LOST: M.fly.on; N_DESK: GOT.desk; N_DATA:
   GOT.ndata; N_FOREIGN: GOT.foreign; any other kind: none. The callees store nothing outside their frames. *)
Definition notice_wr (Bw : list byte) (n : TI.ntc) (a : Z) : Prop :=
  (TI.n_kind n = TC.N_STATE /\
     ((0 <= TW.GOT_n Bw < TC.TRANS_MAX /\
       twa_fld TW.OFF_GOT TA_GOT (TW.A_GOT_t_state (TW.GOT_n Bw)) TW.GOT_t_ESZ a) \/
      twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_n 4 a)) \/
  (TI.n_kind n = TC.N_ACKED /\ twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_acked 4 a) \/
  (TI.n_kind n = TC.N_ACK_LOST /\ twa_fld TW.OFF_M TA_M TW.A_M_fly_on 4 a) \/
  (TI.n_kind n = TC.N_DESK /\ twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_desk 4 a) \/
  (TI.n_kind n = TC.N_DATA /\ twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_ndata 4 a) \/
  (TI.n_kind n = TC.N_FOREIGN /\ twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_foreign 4 a).

(* The shadow of GOT's payload (224 bytes, 28 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the stores at GOT.t[GOT.n] read it. *)
Definition trans_notice_cells (B : asyms) : Prop := decode_zshadow_at B TA_GOT (TA_GOT + TW.SZ_GOT).

Section notice. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* No byte the call stores is a byte of a range a callee reads or names after a store: the struct's 72 bytes (notice
   reads n->state again after the record, check_inflight_acked and check_state_desk read the struct after the
   increments), the body and the announce's 20 bytes (check_state_desk's trans_ntc_at names them after GOT.desk++;
   it reads the announce), and the frame Fr (check_state_desk reads it after GOT.desk++). The plain contract's ntc_at
   and tframe_at put them off the world. NB is the struct's bytes, as trans_ntc_at names them. *)
Definition notice_apart (W : world segs) (memc : word -> option byte) (p : Z) (n : TI.ntc) (Fr : option TI.tframe)
    (Bw : list byte) : Prop :=
  forall x, notice_wr Bw n x ->
    ~ (p <= x < p + NTC_SIZE) /\
    (forall NB : list byte, garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz NB) -> length NB = 72%nat ->
       ~ (TW.u_at NB 48 8 <= x < TW.u_at NB 48 8 + Z.of_nat (length (TI.n_body n))) /\
       (TI.n_ann n <> None -> ~ (TW.u_at NB 24 8 <= x < TW.u_at NB 24 8 + ANN_SIZE))) /\
    (forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)))).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range notice_wr Bw n,
   no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_notice_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n : TI.ntc) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    NOTICE_STK NOTICE_EV 0 (notice_wr Bw n)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_notice_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 11 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - NOTICE_STK -> spZ regs <= sp0 ->
    trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
    trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.notice_m timg_A Fr Bw n = Some (Bw', tt) ->
    notice_apart W memc p n Fr Bw ->
    (TI.n_kind n = TC.N_DATA ->
       trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) /\
       decode_off_win regs NOTICE_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) /\
       TI.n_body_len n < 2 ^ 32) ->
    st_nev S + k + NOTICE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_notice_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of GOT's
   payload, the allocator and meter laws, G inside the image, outside the allocator's statics and outside errno (a
   donor callee keeps G: gx_call_cg), and the contracts of the five callees give the contract at notice's entry. *)
Definition transport_notice_cg_holds_stmt : Prop :=
  transport_cells B -> trans_notice_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @transport_check_state_desk_cg fx' rc B MT (transport_sigma TS_check_state_desk)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIL.transport_check_inflight_lost_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_check_state_data_cg fx' rc B MT (transport_sigma TS_check_state_data)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIA.transport_check_inflight_acked_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSO.transport_check_state_online_cg) fx') ->
  transport_notice_cg (TI.ti_notice timg_A).
End notice.
