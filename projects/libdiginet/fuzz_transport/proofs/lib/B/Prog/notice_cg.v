(* notice_cg: image B's ASan walk contract of notice (fuzz/fuzz_transport.c:937-973; model lib/TModel/TCb.v notice_m)
   on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8341c = TImgB.v ti_notice timg_B (the twin's symbol notice, size
   652; transportb_text + AF_notice in DgnTransportBList.v; transportb_obj 10 in DgnTransportBAddr.v), as STATEMENTS
   only (no proof). It stores into GOT and M, two harness globals, and calls five harness check functions, so it is a
   G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx (image-free) over
   G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g over G_HARNESS_B).

   notice is reached only through the session's notify pointer (struct diginet_session + 96, which
   diginet_session_init stores from its a3; LLVMFuzzerTestOneInput forms 0x8341c with the auipc / addi pair at
   0x817a8 / 0x817b0 and passes it in a3 at its call of diginet_session_init, 0x817c4). The indirect call sites
   (measured on the twin: each `jalr` loads the pointer from s + 96 and a0 from s + 104 after their instrumented
   checks): set_state 0x874b0, on_announce 0x88094 and 0x88258, on_ack 0x887e4, on_data 0x88e28,
   diginet_session_tick 0x895f4. set_state (0x872cc) is a function on this image (image A inlines it); it is called
   by diginet_session_wake 0x86d2c, diginet_session_close 0x876f8, diginet_session_rx 0x87c08, on_announce 0x88128
   and 0x882b8, diginet_session_tick 0x8951c, and maybe_online (tail jump at 0x8af64). Each site reads the pointer
   from the world (tw_read of S_notify; the model's call_notify, TSess.v, compares it with ti_notice timg_B) and
   applies this statement at that address, with a0 = the notify context (not read) and a1 = the address of the struct
   diginet_notice it built.

   The contract. a1 = p, a struct diginet_notice n (check_state_data_cg.v trans_ntc_at); Fr the current heap frame
   (check_state_data_cg.v trans_tframe_at); the read-only bytes the callees read (notice's own kind table,
   personalities[], SPEC_C24, SPEC_PC) read as the image's (trans_rom_view_rd). The memory relates to the world Bw by
   image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), and
   notice_m timg_B Fr Bw n = Some (Bw', tt). The function returns to ra with the callee-saved registers kept, no
   allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g
   G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - NOTICE_STK, sp), the
   image bytes outside G, the owned statics and errno, the caller's block and frame bytes outside notice_wr Bw n),
   and the world relation at Bw'. This is what the plain contract (lib/Prog/T/notice_c.v) says: void; wmem rsegs m'
   B' with B' the model's world; munch of the frame and the world only. Its premises become: ntc_at -> trans_ntc_at,
   tframe_at -> trans_tframe_at, relro_img -> trans_rom_view_rd, wmem -> tw_at, timg_plain -> timg_B; the off_world
   clauses of ntc_at and tframe_at -> notice_apart (no byte the call stores is a byte of the struct, of its body, of
   its announce or of Fr: the ranges a callee reads or names after a store); mem_inv is dropped.
   The one premise the plain contract does not have (image A's form has it too): for a data notice
   (n_kind n = N_DATA), the two premises check_state_data_cg.v adds: its run invariant on the OW.dn[GOT.ndata].body
   range (trans_src_ok and decode_off_win of [OW_dn_body Bw (GOT_ndata Bw), + n_body_len n)) and n_body_len n < 2 ^ 32
   (the bcmp wrapper's length bound), stated on notice's own Bw and window; notice calls check_state_data (0x834b4)
   before it stores anything, so the range and the world are the callee's (a caller carries it).
   The caller of a data notice (on_data, its indirect call at 0x88e28) has the bound from the frame: the notice's
   body_len is the frame's fr_body_len (TSess.v on_data_m), numbytes - 16 with numbytes a 16-bit field.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; this function's 652 code bytes and the 24 bytes of its
   table at 0x20f7c are equal in the pin and the twin), 163 words:
     0x8341c - 0x83420 sp = sp - 16; ra at sp + 8, loaded back at 0x83490, 0x834e8, 0x835e4 and 0x83604. No side-stack
                      frame, no frame pointer, no other register saved. a1 = p until 0x8358c on the N_STATE path,
                      until the call or tail jump on the N_DESK, N_ACK_LOST, N_DATA and N_ACKED paths, and until
                      0x835f8 on the N_FOREIGN path.
     0x83424 - 0x8342c the UBSan checks of p: p = 0 (the null check) and p & 7 <> 0 (the alignment of struct
                      diginet_notice) go to the trap 0x83610.
     0x83430 - 0x83438 a5 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; else the error path. No check guards an access at a constant
                      address of GOT or M.
     0x8343c - 0x8344c the check of the 4-byte load at p; a0 = n->kind (4-byte signed load at p).
     0x83450 - 0x83474 n->kind - 1 > 5 (unsigned) goes to 0x83604 (the default, :970-971); else the jump through the
                      table TRANS_JT_NOTICE 0x20f7c (6 entries of 4 bytes, each added to 0x20f7c, plain loads; a
                      TRANS_RO_RD range): kind 1 (N_DESK) 0x83478, 2 (N_STATE) 0x834f4, 3 (N_DATA) 0x834b0,
                      4 (N_ACKED) 0x834d0, 5 (N_ACK_LOST) 0x8349c, 6 (N_FOREIGN) 0x835f0.
     each increment below: v + 1 (32 bits, sign-extended); v + 1 < v (signed), the UBSan overflow check, goes to the
                      trap 0x83610; else the 4-byte store of v + 1 back.
     0x83478 - 0x83498 N_DESK (:959-961): the increment of GOT.desk (0x5e5030 = GOT + 208); a0 = p; ra loaded back,
                      sp = sp + 16; jump (no link) to check_state_desk (0x854bc) at 0x83498.
     0x8349c - 0x834ac N_ACK_LOST (:955-957): a0 = p; call of check_inflight_lost (0x85408) at 0x834a0, return address
                      0x834a4; the 4-byte store of 0 at M.fly.on (0x5dee40 = M + 96); to 0x83604.
     0x834b0 - 0x834cc N_DATA (:963-965): a0 = p; call of check_state_data (0x857cc) at 0x834b4, return address
                      0x834b8; the increment of GOT.ndata (0x5e503c = GOT + 220); to 0x83604.
     0x834d0 - 0x834f0 N_ACKED (:951-953): the increment of GOT.acked (0x5e5038 = GOT + 216); a0 = p; ra loaded back,
                      sp = sp + 16; jump (no link) to check_inflight_acked (0x85358) at 0x834f0.
     0x834f4 - 0x83508 N_STATE (:941-949): a6 = GOT (0x5e4f60); g = GOT.n (4-byte signed load at GOT + 0); a0 = p + 4;
                      15 < g (signed) goes to 0x835bc.
     0x8350c - 0x835b8 (:943-945) the check of the 4-byte load at p + 4; g >= 16 (unsigned: g < 0 here; the UBSan index
                      check of GOT.t[g]) goes to the trap 0x83610; ~(GOT + 4) < 12 g (unsigned; the UBSan
                      pointer-overflow check) goes to the trap 0x83610; x = GOT + 12 g: the check of the 4-byte store
                      at x + 4, the store of n->state at x + 4 (GOT.t[g].state, 0x83558); the same for p + 8 and
                      x + 8 (GOT.t[g].old = n->old_state, 0x83588) and for p + 12 and x + 12 (GOT.t[g].reason =
                      n->reason, 0x835b8).
     0x835bc - 0x835c4 the increment of GOT.n at GOT + 0 (:947).
     0x835c8 - 0x835ec the check of the 4-byte load at p + 4; n->state <> 2 (S_ONLINE) goes to 0x83604; else ra loaded
                      back, sp = sp + 16, jump (no link) to check_state_online (0x85320) at 0x835ec.
     0x835f0 - 0x83600 N_FOREIGN (:967-968): the increment of GOT.foreign (0x5e5034 = GOT + 212).
     0x83604 - 0x8360c ra loaded back, sp = sp + 16, return (a0 .. a7 not stated: void).
   The model and the code: the dispatch and every test is notice_m's (n_kind n, GOT_n Bw < TRANS_MAX, n_state n =
   S_ONLINE), read through tw_at and trans_ntc_at; each store is the model's set_GOT_* / set_M_fly_on (put 4 of the
   low 32 bits), and each callee's traps are ruled out by its contract's model premise, which notice_m's branch
   supplies (check_state_desk_m timg_B Fr at the world after GOT.desk++, check_inflight_lost_m and check_state_data_m
   at Bw, check_inflight_acked_m after GOT.acked++, check_state_online_m after the record and GOT.n++).
   The trap: 0x83610 (`unimp`, the UBSan trap). From 0x83424 and 0x8342c: trans_ntc_at's 0 < p and p mod 8 = 0. From
   0x83484, 0x834c4, 0x834dc, 0x835c0, 0x835fc (GOT.desk, GOT.ndata, GOT.acked, GOT.n, GOT.foreign at INT_MAX):
   notice_m's int_inc is None there. From 0x83520 (g < 0 on the record path): notice_m is None at GOT.n < 0. From
   0x83538: on this path 0 <= g <= 15, so GOT + 4 + 12 g does not wrap.
   The differences from image A's code (lib/A/Prog/notice_cg.v): the addresses; the UBSan checks and their one trap
   are new. Image A's code has no trap of its own: there the model's None cases (GOT.n < 0 on the record path, the
   increments at INT_MAX) are an error path and a wrap; here they are the trap. No premise changes: every new trap is
   refuted by trans_ntc_at or the model premise, both in A's form. The callees' frames are A's (check_state_desk:
   `sp = sp - 48` at 0x854bc, two bcmp calls; check_state_data: `sp = sp - 32` at 0x857cc, one bcmp call), so
   NOTICE_STK is A's. notice_wr names a field's bytes by lib/B/Prog/m_set_cg.v twb_fld, image B's twin of
   lib/A/Prog/m_lost_cg.v twa_fld (image B has no m_lost function, so the twin lives in m_set_cg.v).
   Error paths (8 calls) and the facts that rule them out:
     __asan_report_load4 0x83620 (p), 0x83640 (p + 4, the record) and 0x83630 (p + 4, the S_ONLINE test), 0x83668
       (p + 8), 0x83690 (p + 12): the 72 bytes at p are marked usable (trans_ntc_at's trans_src_ok: a heap block, AR's
       shadow law; else decode_rd_ok) and p mod 8 = 0, so each 4-byte load lies in one granule.
     __asan_report_store4 0x83654 (x + 4), 0x8367c (x + 8), 0x836a4 (x + 12): on this path 0 <= g <= 15 (the code's
       test and the model's None at g < 0), so [x + 4, x + 16) lies in [GOT + 4, GOT + 196), inside GOT's payload,
       4-aligned, whose shadow is 0 (trans_notice_cells).
   Callee texts assumed (pc order): check_state_desk as image B's check_state_desk_cg.v
   transport_check_state_desk_cg at transportb_sigma TB_check_state_desk (tail jump at 0x83498, from notice's entry sp
   and ra; a donor-form callee, through TransportGCg.v gx_call_cg); check_inflight_lost as image B's
   check_inflight_lost_cg.v transport_check_inflight_lost_cg (a leaf, read through DgnTransportBCg.v
   transport_leaf_at; call at 0x834a0, through gx_call_leaf and the leaf bridge); check_state_data as image B's
   check_state_data_cg.v transport_check_state_data_cg at transportb_sigma TB_check_state_data (call at 0x834b4;
   gx_call_cg); check_inflight_acked as image B's check_inflight_acked_cg.v transport_check_inflight_acked_cg (leaf;
   tail jump at 0x834f0); check_state_online as image B's check_state_online_cg.v transport_check_state_online_cg
   (leaf; tail jump at 0x835ec). A donor callee keeps every byte of G (gx_call_cg: gx_ok and gx_noerrno), so the
   world relation after it is the one it was handed.
   Stack: 16 bytes of its own; the tail jumps run from the entry sp (check_state_desk's CSDESK_STK, a leaf's ESTACK);
   the calls run from sp - 16 (check_state_data's CSDATA_STK, a leaf's ESTACK): NOTICE_STK = 48 + 2 * ESTACK.
   Form: lib/A/Prog/notice_cg.v. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_inflight_lost_cg check_inflight_acked_cg check_state_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_cg.
Module LIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_cg.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* notice's entry: the value the model's call_notify tests the session's notify pointer against. *)
Lemma notice_at : TI.ti_notice timg_B = 0x8341c /\ TI.ti_notice timg_B = transportb_obj 10.
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
       twb_fld TW.OFF_GOT TB_GOT (TW.A_GOT_t_state (TW.GOT_n Bw)) TW.GOT_t_ESZ a) \/
      twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_n 4 a)) \/
  (TI.n_kind n = TC.N_ACKED /\ twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_acked 4 a) \/
  (TI.n_kind n = TC.N_ACK_LOST /\ twb_fld TW.OFF_M TB_M TW.A_M_fly_on 4 a) \/
  (TI.n_kind n = TC.N_DESK /\ twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_desk 4 a) \/
  (TI.n_kind n = TC.N_DATA /\ twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_ndata 4 a) \/
  (TI.n_kind n = TC.N_FOREIGN /\ twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_foreign 4 a).

(* The shadow of GOT's payload (224 bytes, 28 whole granules) is 0: a range of the record's as_zero_shadow (the
   Tfib_zero_shadow row (0x5e4f60, 0x5e5040 - 0x5e4f60), lib/B/YF0m.v:3112). The instrumented checks of the stores
   at GOT.t[GOT.n] read it. *)
Definition trans_notice_cells (B : asyms) : Prop := decode_zshadow_at B TB_GOT (TB_GOT + TW.SZ_GOT).

Section notice. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
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

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   notice_wr Bw n, no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_notice_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n : TI.ntc) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs NOTICE_STK NOTICE_EV 0 (notice_wr Bw n)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_notice_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 11 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - NOTICE_STK -> spZ regs <= sp0 ->
    trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n ->
    trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.notice_m timg_B Fr Bw n = Some (Bw', tt) ->
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
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_check_state_desk_cg fx' rc B MT (transportb_sigma TB_check_state_desk)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIL.transport_check_inflight_lost_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_check_state_data_cg fx' rc B MT (transportb_sigma TB_check_state_data)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIA.transport_check_inflight_acked_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSO.transport_check_state_online_cg) fx') ->
  transport_notice_cg (TI.ti_notice timg_B).
End notice.
