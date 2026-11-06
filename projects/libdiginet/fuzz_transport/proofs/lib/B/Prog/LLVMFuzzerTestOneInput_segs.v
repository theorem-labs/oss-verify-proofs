(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the interface of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (the context record, a state predicate per cut point, one statement per segment, the composition by SRr_bind / SRr_mono and the srealizes entry of cgif's lib/A/ACfh.v): the cut points, the registers and the frame are fuzz_uci.asan's, the slot is the core's lib/A/ACfn.v tfib_lib_contract_x_all, and the loop of five turns is composed by an induction on the turn. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module paths and module names changed; 979 of its 1018 lines of code are new or changed and 163 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segs: the INTERFACE of the image-B walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput
   (transportb_text = lib/B/YCfn.v A_LLVMF = 0x812a0, 7516 bytes; the statement
   transport_LLVMFuzzerTestOneInput_cg_holds_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v). It holds no stepping:
   1. lp_prem, the premises of the statement as a record, and lcx, the context of one call, with the slot's pre
      (lc_base) and post (lc_post) at it;
   2. the model's pieces the cuts name (copies of lib/TModel/TOps.v's and TCb.v's let-bindings, each checked against
      them by a lemma of lib/B/Prog/LLVMFuzzerTestOneInput_st.v);
   3. a state predicate at each cut point;
   4. thirty-three segment statements, collected in the record lc_segments;
   5. the composition llvmf_of_segments, proved: lc_segments gives the statement;
   6. the statements K1 .. K7 of the kit lemmas the segments share (named, unproved here; each is a sub-row).
   The cut structure is image A's (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v); the pcs, the registers, the spill slots
   and the code between the cuts are image B's own, measured on the listing lib/B/Prog/DgnTransportBList.v (slot k at
   0x812a0 + 4 k).

   The cut points, as offsets from the entry 0x812a0 (pc = 0x812a0 + offset):

     ENTRY  +0x000   the slot's pre                                           lc_base
     SM     +0x074   the return of __asan_stack_malloc_2 (call +0x070)        lc_st_sm
     CFGD   +0x358   the return of diginet_session_config_default (+0x354)    lc_st_cfgd
     SCAL   +0x4b0   after the stores of g_raw, g_now, g_fail_next and
                     g_last_counter, before the memset of M                   lc_st_scal
     INIT   +0x528   the return of diginet_session_init (+0x524)              lc_st_init
     HEAD   +0x58c   the loop head after `beqz s7` (+0x588: bytes are left),
                     operation number ops                                     lc_st_head
     ARMo   the nine op arms after the dispatch (`jr a0` at +0x5f0, `bltu a1, a0` at +0x5d4 for op 8):
                     op 0 +0x5f4, 1 +0x7b4, 2 +0x6e8, 3 +0x758, 4 +0x630, 5 +0x7f4, 6 +0x864, 7 +0x7a8, 8 +0x90c
                                                                              lc_st_arm
     RECV   +0xc00   the call of receive (ops 0 and 8 share it)               lc_st_recv
     BAR1   +0x1474  op 1's call of build_and_receive                         lc_st_bar1
     ANN    +0xdcc   op 2 after the mac copy into body (or none, mac > 12)    lc_st_ann
     BAR2   +0xe6c   op 2's call of build_and_receive                         lc_st_bar2
     TICK   +0xcf4   op 3's call of m_tick (after the g_now store)            lc_st_tick
     SUBR   +0x12bc  op 4, raw mode (g_raw <> 0), the length word read        lc_st_subr
     SUBT   +0xfa4   op 4, tagged mode (g_raw = 0)                            lc_st_subt
     SYSL   +0x10b0  op 4's spec_system_at loop head, index i                 lc_st_sysl
     SYSJ   +0x1170  op 4 after that loop (t2 = the sys flag)                 lc_st_sysj
     FIND   +0x11ec  op 4's find loop head over g_q, index i                  lc_st_find
     WANT   +0x1498  op 4 with want in s6, before diginet_session_submit      lc_st_want
     CMDW   +0x14cc  op 4 after check_latest_submit (or after the refusal
                     check when sys)                                          lc_st_cmdw
     S4     +0x1654  op 4's call of settle (raw and tagged meet)              lc_st_s4
     MSET   +0x8e8   op 6's call of m_set (image B only: m_set is a function) lc_st_mset
     CLS    +0x8ec   op 6 after m_close (m_set returned)                      lc_st_cls
     SET56  +0x900   ops 5 and 6: the call of settle                          lc_st_set56
     TAIL   +0x1670  the loop tail (`addiw s3, s3, 1`)                        lc_st_tail
     EXIT   +0x188   the epilogue (every return)                              lc_st_exit

   Error exits ruled out inside the segments: the size test `beqz a0` at +0x184 (its fall-through +0x188 is the
   epilogue; n < 2 ^ 26, the slot's pre, segment HDR); the real-stack arm +0x084 .. +0x09c (the flag word reads 1 by
   transport_cells and astack_malloc_realizes returns a frame, HDR; `beqz a2` at +0x068 is not taken, ENTRY); the
   no-return entry and abort at +0x1b48 / +0x1b4c after diginet_session_init (its result is SPEC_OK by the model,
   segment PRE); every __asan_report_* call in the segment owning its checked access; every one of the 74 branches to
   the UBSan trap word +0x1b44 (0x82de4) in the segment that runs it (both lists in
   lib/B/Prog/LLVMFuzzerTestOneInput_st.v section 5). The epilogue's real-stack arm +0x278 .. +0x2f4 is not taken
   (128(s1) holds the frame, not 0: segment EXIT).

   The frame. `addi sp, sp, -320` at +0x000 (the probe store `sd zero, 0(sp)` at +0x004), the 13 saves (ra, s0 .. s11)
   at sp0 - 8 .. sp0 - 104, s0 = sp0 (+0x03c), `andi sp, sp, -32` (+0x040), s1 = sp1 = 32 * ((sp0 - 320) / 32). The
   class-2 side-stack frame F (256 bytes): the struct diginet_cmd c at F + 32, body[34] at F + 96, the struct
   diginet_io io at F + 176, the flag pointer at F + 248; its 32 shadow bytes at s2 = SHADOW_OFF + F / 8 (lf_shm).
   s10 = SHADOW_OFF from +0x060 on. The spill slots at s1 + 32 .. s1 + 184 (lf_spills) are written in the prologue
   (+0x0a0 / +0x0d4, +0x45c .. +0x4a8, +0x4cc .. +0x514, +0x548 .. +0x584) and only read after; op 4 writes 0, 8, 16, 24
   and 64(s1); 208(s1) (+0x0a4) is read by no instruction. In the loop s3 = ops, s4 = c (F + 32), s6 = 1 (the
   constant the UBSan cursor tests compare with), s9 / s7 the cursor before an operation's byte and s8 / s11 after.

   The model. The world of each cut is TModel's world Bw (lib/TModel/TWorld.v) related to the memory by
   TWorldG.v tw_at TMAP_B (lib/B/Prog/TWorldB.v). The prologue's worlds come from the world Bw0 at the entry memory
   (TWorldB.v tw_exists_B); the loop's from InitOk / LoopOk at timg_B (lib/B/Prog/TImgB.v): at HEAD the world
   satisfies TSim/Agree.v agree timg_B ops (lc_opok); each arm's cuts carry the arm's model steps done so far, and TAIL
   carries the operation's model equation LLVMFuzzerTestOneInput_op_m timg_B B0 A D c0 k0 = Some (Bw, (c', k')) at a
   stream A = fun _ => a with recv_addr_ok a (the receive's address, any for ops 3 .. 7), from which LoopOk.op_ok gives
   agree timg_B (ops + 1) Bw (LLVMFuzzerTestOneInput_st.v lc_tail_agree).

   The G journal at every cut after the stack malloc is the caller's at FP = [] (no file range): the sink stays
   closed, so the journal keeps the file descriptors and the file system (LLVMFuzzerTestOneInput_st.v
   lc_journal_io); EXIT widens it to the post's FP = [sink_token] by lc_fp_token. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_init_cg m_wake_cg m_tick_cg m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_state_wake_code_cg check_refusal_submit_cg check_latest_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts InitOk.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TShape := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportShape.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_cg.
Module LCRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_cg.
Module LCLS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_submit_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. Constants of the code                                            *)
(* ------------------------------------------------------------------ *)

(* The frame (`addi sp, sp, -320` at +0x000), the side-stack class (`addi a0, zero, 0x100`, the call at +0x070) and
   its size. *)
Definition LF_FRAME : Z := 320.
Definition LF_CID : Z := 2.
Definition LF_FBYTES : Z := 256.
Lemma lf_fbytes : fs_frame_bytes LF_CID = LF_FBYTES.
Proof. reflexivity. Qed.
(* The 13 saved words (sd at sp + 0x138 .. sp + 0xd8 after `addi sp, sp, -320`, +0x008 .. +0x038; ld at +0x300 ..
   +0x330), as (bytes below the entry sp, register): ra, s0, s1, s2, .., s11. *)
Definition LF_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
   (96, 26); (104, 27)].

(* The cut points, as offsets from the entry. *)
Definition LO_SM : Z := 0x074.
Definition LO_CFGD : Z := 0x358.
Definition LO_SCAL : Z := 0x4b0.
Definition LO_INIT : Z := 0x528.
Definition LO_HEAD : Z := 0x58c.
Definition LO_ARMS : list Z := [0x5f4; 0x7b4; 0x6e8; 0x758; 0x630; 0x7f4; 0x864; 0x7a8; 0x90c].
Definition lo_arm (o : Z) : Z := nth (Z.to_nat o) LO_ARMS 0.
Definition LO_RECV : Z := 0xc00.
Definition LO_BAR1 : Z := 0x1474.
Definition LO_ANN : Z := 0xdcc.
Definition LO_BAR2 : Z := 0xe6c.
Definition LO_TICK : Z := 0xcf4.
Definition LO_SUBR : Z := 0x12bc.
Definition LO_SUBT : Z := 0xfa4.
Definition LO_SYSL : Z := 0x10b0.
Definition LO_SYSJ : Z := 0x1170.
Definition LO_FIND : Z := 0x11ec.
Definition LO_WANT : Z := 0x1498.
Definition LO_CMDW : Z := 0x14cc.
Definition LO_S4 : Z := 0x1654.
Definition LO_MSET : Z := 0x8e8.
Definition LO_CLS : Z := 0x8ec.
Definition LO_SET56 : Z := 0x900.
Definition LO_TAIL : Z := 0x1670.
Definition LO_EXIT : Z := 0x188.
Lemma lo_cut_pcs :
  transportb_text + LO_SM = 0x81314 /\ transportb_text + LO_CFGD = 0x815f8 /\ transportb_text + LO_SCAL = 0x81750 /\
  transportb_text + LO_INIT = 0x817c8 /\ transportb_text + LO_HEAD = 0x8182c /\
  map (fun o => transportb_text + o) LO_ARMS =
    [0x81894; 0x81a54; 0x81988; 0x819f8; 0x818d0; 0x81a94; 0x81b04; 0x81a48; 0x81bac] /\
  transportb_text + LO_RECV = 0x81ea0 /\ transportb_text + LO_BAR1 = 0x82714 /\
  transportb_text + LO_ANN = 0x8206c /\ transportb_text + LO_BAR2 = 0x8210c /\
  transportb_text + LO_TICK = 0x81f94 /\ transportb_text + LO_SUBR = 0x8255c /\
  transportb_text + LO_SUBT = 0x82244 /\ transportb_text + LO_SYSL = 0x82350 /\
  transportb_text + LO_SYSJ = 0x82410 /\ transportb_text + LO_FIND = 0x8248c /\
  transportb_text + LO_WANT = 0x82738 /\ transportb_text + LO_CMDW = 0x8276c /\
  transportb_text + LO_S4 = 0x828f4 /\ transportb_text + LO_MSET = 0x81b88 /\
  transportb_text + LO_CLS = 0x81b8c /\ transportb_text + LO_SET56 = 0x81ba0 /\
  transportb_text + LO_TAIL = 0x82910 /\ transportb_text + LO_EXIT = 0x81428.
Proof. repeat split; reflexivity. Qed.

(* The 32 shadow bytes of the frame (+0x0e4 .. +0x168): 0xf1 x4, c's four (0xf8 out of scope, 0 while op 4 runs:
   +0x630 / +0x165c), 0xf2 x4, body's five (0xf8, or 0 0 0 0 2 while op 2 runs: +0xa74 / +0xd7c and +0xe70), 0xf2 x5,
   io's four (0 for the whole call until the epilogue, +0x18c), 0xf3 x6. *)
Definition lf_shm (cin bin : bool) : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1] ++ repeat (if cin then 0 else 0xf8) 4 ++ [0xf2; 0xf2; 0xf2; 0xf2] ++
  (if bin then [0; 0; 0; 0; 2] else repeat 0xf8 5) ++ repeat 0xf2 5 ++ [0; 0; 0; 0] ++ repeat 0xf3 6.
Lemma lf_shm_len : forall cin bin, length (lf_shm cin bin) = 32%nat.
Proof. intros [|] [|]; reflexivity. Qed.

(* The spill slots, (offset from sp1, value), as the prologue stores them: at +0x0a0 / +0x0d4 (the frame: the stack
   malloc's result at 128(s1), the frame at 136(s1)), +0x45c .. +0x4a8 (the auipc pages of g_raw, g_now, g_fail_next,
   g_last_counter: transportb_hi 8, 9, 10, 11), +0x4cc .. +0x514 (M, the pages of g_nq and g_ncmd: transportb_hi 14,
   15, g_s), +0x548 .. +0x584 (the constants 0x610f and 0xffff, c + 3, the complement of c, the complement of body,
   body, body + 24, c + 1, c; c = F + 32, body = F + 96). *)
Definition lf_spill_sm (F : Z) : list (Z * Z) := [(128, F); (136, F)].
Definition lf_spill_scal (F : Z) : list (Z * Z) :=
  lf_spill_sm F ++ [(104, transportb_hi 8); (152, transportb_hi 9); (184, transportb_hi 10); (40, transportb_hi 11)].
Definition lf_spill_init (F : Z) : list (Z * Z) :=
  lf_spill_scal F ++ [(168, TB_M); (32, transportb_hi 14); (56, transportb_hi 15); (112, TB_g_s)].
Definition lf_spill_loop (F : Z) : list (Z * Z) :=
  lf_spill_init F ++
  [(88, 0x610f); (120, 0xffff); (48, F + 35); (160, 2 ^ 64 - 1 - (F + 32)); (72, 2 ^ 64 - 1 - (F + 96));
   (96, F + 96); (80, F + 120); (176, F + 33); (144, F + 32)].
Lemma lf_spill_pages :
  transportb_hi 8 = 0x5de6ec /\ transportb_hi 9 = 0x5de6f4 /\ transportb_hi 10 = 0x5de728 /\
  transportb_hi 11 = 0x5de73c /\ transportb_hi 14 = 0x5df784 /\ transportb_hi 15 = 0x5df788.
Proof. repeat split; reflexivity. Qed.
(* The pages address the globals the loop reads through them: g_raw at hi 8 + 0x674, g_now at hi 9 + 0x68c,
   g_fail_next at hi 10 + 0x678, g_last_counter at hi 11 + 0x684, g_nq at hi 14 - 0x1a4, g_ncmd at hi 15 - 0x188. *)
Lemma lf_spill_globals :
  transportb_hi 8 + 0x674 = TB_g_raw /\ transportb_hi 9 + 0x68c = TB_g_now /\
  transportb_hi 10 + 0x678 = TB_g_fail_next /\ transportb_hi 11 + 0x684 = TB_g_last_counter /\
  transportb_hi 14 - 0x1a4 = TB_g_nq /\ transportb_hi 15 - 0x188 = TB_g_ncmd.
Proof. repeat split; reflexivity. Qed.

(* The receive budget of one operation (receive_cg.v recv_cost n <= this for n <= 65535, mo_malloc_mono). *)
Definition lf_rcost (MT : ameter_ops) : Z := mo_malloc MT 65535 + mo_free MT.
Lemma lf_cost_eq : forall MT n, transport_llvmf_cost MT n = TC.OPS_MAX * lf_rcost MT.
Proof. intros MT n. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 1. The model's pieces the cuts name (TOps.v, TCb.v)                 *)
(* ------------------------------------------------------------------ *)

(* The prologue up to diginet_session_init (TOps.v LLVMFuzzerTestOneInput_m :353-393, below the size test):
   the world and the code it hands to the abort test. The cursor at the loop head is InitOk.v prologue_cursor. *)
Definition lc_pro_scal (D : list byte) (B1 : list byte) : list byte :=
  let size := Z.of_nat (length D) in
  let c0 := TOP.fuzz_in_m size in
  let (c1, flags) := TOP.fuzz_u8_m D c0 in
  let B2 := TW.set_Cfg_host_mac B1 TC.HOST in
  let B3 := TW.set_Cfg_auto_wake B2 (Z.land flags 1) in
  let B4 := TW.set_Cfg_sum_mode B3
              (if Z.land flags 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) in
  let B5 := TW.set_Cfg_desk_mac_set B4 (Z.land (Z.shiftr flags 2) 1) in
  let B6 := TW.set_Cfg_desk_mac B5 TC.DESK in
  let (c2, v1) := TOP.fuzz_u8_m D c1 in
  let B7 := TW.set_Cfg_max_retries B6 (v1 mod 8) in
  let (c3, v2) := TOP.fuzz_u8_m D c2 in
  let B8 := TW.set_Cfg_ack_timeout_ms B7 ((1 + v2) mod 2^32) in
  let (c4, v3) := TOP.fuzz_u16_m D c3 in
  let B9 := TW.set_Cfg_keepalive_ms B8 ((1 + v3) mod 2^32) in
  let (c5, v4) := TOP.fuzz_u8_m D c4 in
  let B10 := TW.set_Cfg_backoff_ms B9 v4 in
  let (c6, v5) := TOP.fuzz_u16_m D c5 in
  let B11 := TW.set_Cfg_offline_ms B10 ((1 + v5) mod 2^32) in
  let (c7, v6) := TOP.fuzz_u16_m D c6 in
  let B12 := TW.set_Cfg_wake_timeout_ms B11 ((1 + v6) mod 2^32) in
  let (c8, v7) := TOP.fuzz_u16_m D c7 in
  let B13 := TW.set_Cfg_display_gap_us B12 v7 in
  let (c9, v8) := TOP.fuzz_u8_m D c8 in
  let B14 := TW.set_Cfg_max_cmds B13 ((1 + v8 mod 255) mod 2^32) in
  let (c10, v9) := TOP.fuzz_u16_m D c9 in
  let B15 := TW.set_Cfg_max_body B14
               ((DSpec.SPEC_CMD_MAX + v9 mod (TC.SPEC_MAX_BODY - DSpec.SPEC_CMD_MAX + 1)) mod 2^32) in
  let B16 := TW.set_g_raw B15 (Z.land (Z.shiftr flags 3) 1) in
  let B17 := TW.set_g_now B16 1000000 in
  let B18 := TW.set_g_fail_next B17 0 in
  TW.set_g_last_counter B18 0.
Definition lc_pro_minit (B19 : list byte) : list byte :=
  let B20 := TW.upd B19 TW.OFF_M (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_M)) in
  let B21 := TW.set_M_desk_known B20 (TW.Cfg_desk_mac_set B20) in
  let B22 := TW.set_M_desk B21 TC.DESK in
  let B23 := TW.set_g_ncmd (TW.set_g_nq B22 0) 0 in
  TW.set_g_rx B23 0.
Definition lc_pro_m (I : TI.timg) (B : list byte) (D : list byte) : option (list byte * Z) :=
  match TS0.diginet_session_config_default_m B with
  | None => None
  | Some (B1, _) =>
      TS0.diginet_session_init_m (lc_pro_minit (lc_pro_scal D B1)) 0 (TI.ti_io_send I) (TI.ti_io_recv I)
        (TI.ti_io_now I) (TI.ti_notice I) 0
  end.
(* The flags byte and the cursor after it (+0x244 .. +0x274, +0x33c .. +0x344). *)
Definition lc_flags (D : list byte) : Z := snd (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))).
Definition lc_c1 (D : list byte) : TOP.fuzz_in := fst (TOP.fuzz_u8_m D (TOP.fuzz_in_m (Z.of_nat (length D)))).

(* The op code of the operation at cursor c and the cursor after its byte (TOps.v :288-289). *)
Definition lc_opc (D : list byte) (c : TOP.fuzz_in) : Z := snd (TOP.fuzz_u8_m D c) mod 9.
Definition lc_oc (D : list byte) (c : TOP.fuzz_in) : TOP.fuzz_in := fst (TOP.fuzz_u8_m D c).

(* Ops 0 and 8: the record receive is handed (TOps.v :291-293, :329-332): by_poll, poll_flags, the record's offset and
   length in D, and the cursor after it. *)
Record lrv := mkLrv { rv_bp : Z; rv_pf : Z; rv_off : Z; rv_n : Z; rv_c : TOP.fuzz_in }.
Definition lc_recv_vals (D : list byte) (c : TOP.fuzz_in) : lrv :=
  let (c1, opb) := TOP.fuzz_u8_m D c in
  if opb mod 9 =? 0 then
    let '(c2, off, n) := TOP.fuzz_record_m D c1 in mkLrv 0 0 off n c2
  else
    let (c2, pf) := TOP.fuzz_u8_m D c1 in
    let '(c3, off, n) := TOP.fuzz_record_m D c2 in mkLrv 1 pf off n c3.

(* Op 1, op_frame (TOps.v op_frame_m :144-151): sel, send, ack, retry, the body's offset and length, the cursor after. *)
Record lfv := mkLfv { fv_sel : Z; fv_send : Z; fv_ack : Z; fv_retry : Z; fv_off : Z; fv_len : Z; fv_c : TOP.fuzz_in }.
Definition lc_frame_vals (D Bw : list byte) (c1 : TOP.fuzz_in) : lfv :=
  let (c1', sel) := TOP.fuzz_u8_m D c1 in
  let (c2, send) := TOP.fuzz_u16_m D c1' in
  let (c3, ack0) := TOP.fuzz_u16_m D c2 in
  let ack := if Z.land sel 0x80 =? 0 then ack0 else TW.g_last_counter Bw in
  let (c4, r) := TOP.fuzz_u8_m D c3 in
  let retry := Z.land r 3 in
  let (c5, w) := TOP.fuzz_u16_m D c4 in
  let '(c6, off, len) := TOP.fuzz_take_m c5 (w mod (TC.SPEC_MAX_BODY + 1)) in
  mkLfv sel send ack retry off len c6.
(* The table entries op_frame reads (TOps.v :154-156) and the addresses the code loads for them: op_frame.DST
   (0xa3a80) holds HOST, SPEC_BCAST, OTHER, HOST, op_frame.SRC (0xa3a40) DESK, DESK2, HOST, NOTDD. *)
Definition lc_fdst (sel : Z) : list byte := nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) TOP.op_frame_DST [].
Definition lc_fsrc (sel : Z) : list byte := nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) TOP.op_frame_SRC [].
Definition lc_fcmd (sel : Z) : Z := nth (Z.to_nat (Z.land sel 7 mod 7)) TOP.op_frame_CMD 0.
Definition lc_fdst_a (sel : Z) : Z :=
  nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) [TRANS_HOST; TRANS_SPEC_BCAST; TRANS_OTHER; TRANS_HOST] 0.
Definition lc_fsrc_a (sel : Z) : Z :=
  nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) [TRANS_DESK; TRANS_DESK2; TRANS_HOST; TRANS_NOTDD] 0.

(* Op 2, op_announce (TOps.v op_announce_m :173-186): sel, mac, the name byte, body after the mac copy and the whole
   body, the cursor after. *)
Record lav := mkLav { av_sel : Z; av_mac : Z; av_nm : Z; av_body1 : list byte; av_body3 : list byte;
                      av_c : TOP.fuzz_in }.
Definition lc_ann_vals (D : list byte) (c1 : TOP.fuzz_in) : lav :=
  let (c1', sel) := TOP.fuzz_u8_m D c1 in
  let (c2, m) := TOP.fuzz_u8_m D c1' in
  let mac := m mod 16 in
  let (c3, nm) := TOP.fuzz_u8_m D c2 in
  let name := nm mod 3 in
  let body0 := repeat (DSpec.b8 0) (Z.to_nat (TC.SPEC_ANN_MIN + 1)) in
  let body1 := if mac <? 10 then TW.upd body0 mac TC.HOST
               else if mac <? 13 then TW.upd body0 (mac - 10) TC.OTHER
               else body0 in
  let body2 := TW.upd body1 TC.SPEC_ANN_VERSION TOP.ANN_VERSION_137 in
  let body3 := TW.upd body2 TC.SPEC_ANN_NAME (nth (Z.to_nat name) TOP.op_announce_NAME []) in
  mkLav sel mac nm body1 body3 c3.
Definition lc_acmd (sel : Z) : Z := if Z.land sel 1 =? 0 then TC.SPEC_CMD_E0 else TC.SPEC_CMD_E1.
(* op_announce.NAME (0xa3ac0) holds the three strings' addresses. *)
Definition lc_name_a (nm : Z) : Z := nth (Z.to_nat (nm mod 3)) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4] 0.

(* Op 3 (TOps.v :301-305): the world after the g_now store, from op_begin's world B1, and the cursor after the u16. *)
Definition lc_tick_w (D : list byte) (c1 : TOP.fuzz_in) (B1 : list byte) : list byte :=
  let (c2, sb) := TOP.fuzz_u8_m D c1 in
  let scale := nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0 in
  let (c3, t) := TOP.fuzz_u16_m D c2 in
  TW.set_g_now B1 ((TW.g_now B1 + scale * t) mod 2^64).
Definition lc_tick_c (D : list byte) (c1 : TOP.fuzz_in) : TOP.fuzz_in :=
  let (c2, sb) := TOP.fuzz_u8_m D c1 in fst (TOP.fuzz_u16_m D c2).

(* Op 4, op_submit (TOps.v op_submit_m :219-275). The key and display bytes (:221-225). *)
Record lsv := mkLsv { sv_key : Z; sv_display : Z; sv_c : TOP.fuzz_in }.
Definition lc_sub_kd (D : list byte) (c1 : TOP.fuzz_in) : lsv :=
  let (c1', kb) := TOP.fuzz_u8_m D c1 in
  let (c2, ab) := TOP.fuzz_u8_m D c1' in
  let key := DSpec.KEY (kb mod 9 + 1) ab in
  let (c3, db) := TOP.fuzz_u8_m D c2 in
  let display := Z.land db 1 in
  mkLsv key display c3.
(* The tagged mode up to the find (:237-246): serial, the world after the memset of g_cmd[serial], len, the take's
   offset and length, the bytes of c, the cursor after the take and the cursor after the len byte (before the take). *)
Record ltg := mkLtg { tg_serial : Z; tg_B2 : list byte; tg_len : Z; tg_off : Z; tg_n : Z; tg_cbytes : list byte;
                      tg_c : TOP.fuzz_in; tg_c4 : TOP.fuzz_in }.
Definition lc_tag_vals (D : list byte) (B1 : list byte) (c3 : TOP.fuzz_in) : ltg :=
  let serial := TW.g_ncmd B1 in
  let B2 := TW.upd B1 (TW.A_Cmd_st serial) (repeat (DSpec.b8 0) (Z.to_nat TW.Cmd_ESZ)) in
  let (c4, lb) := TOP.fuzz_u8_m D c3 in
  let len := lb mod 22 + 3 in
  let '(c5, off, n) := TOP.fuzz_take_m c4 (len - 3) in
  let cbytes := [DSpec.b8 TC.TAG; DSpec.b8 (Z.land serial 0x7f); DSpec.b8 (Z.land (Z.shiftr serial 7) 0x7f)]
                ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n)) in
  mkLtg serial B2 len off n cbytes c5 c4.
(* sys, at and want (:246-253). *)
Definition lc_sys (tv : ltg) : bool := DSpec.system_at (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)).
Definition lc_at (tv : ltg) (key : Z) : option Z :=
  if negb (TC.h_coalescable_m key =? 0) then TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) (tg_B2 tv) key 0
  else Some (-1).
Definition lc_want (tv : ltg) (at_ : Z) : Z :=
  if lc_sys tv then DSpec.SPEC_E_REFUSED
  else if (at_ <? 0) && (TW.g_nq (tg_B2 tv) =? TC.QUEUE_MAX) then DSpec.SPEC_E_SPACE
  else DSpec.SPEC_OK.
(* The raw mode's length word (:227), the take and the struct it hands diginet_session_submit (:227-231). *)
Definition lc_raw_w (D : list byte) (c3 : TOP.fuzz_in) : Z := snd (TOP.fuzz_u16_m D c3).
Definition lc_raw_c4 (D : list byte) (c3 : TOP.fuzz_in) : TOP.fuzz_in := fst (TOP.fuzz_u16_m D c3).
Record lrw := mkLrw { rw_len : Z; rw_off : Z; rw_t : Z; rw_c : TOP.fuzz_in }.
Definition lc_raw_vals (D : list byte) (c3 : TOP.fuzz_in) : lrw :=
  let (c4, w) := TOP.fuzz_u16_m D c3 in
  let '(c5, off, t) := TOP.fuzz_take_m c4 (w mod (DSpec.SPEC_CMD_MAX + 1)) in
  mkLrw (t mod 2^8) off t c5.
Definition lc_raw_cs (D : list byte) (rv : lrw) (display key : Z) : list byte :=
  TOP.cmd_struct (TW.sub D (rw_off rv) (Z.to_nat (rw_len rv)) ++ repeat (DSpec.b8 0) (Z.to_nat (24 - rw_len rv)))
    (rw_len rv) display key.

(* Op 6, m_close (TCb.v m_close_m :378-386) up to its call of m_set: the world handed to m_set (OW.e3 + 1 and
   M.fail = 0 when the desk is known, not foreign and not closed; then M.fly.on = 0), None on OW.e3's overflow. *)
Definition lc_close_w (B : list byte) : option (list byte) :=
  if TC.truth (TW.M_desk_known B) && negb (TC.truth (TW.M_foreign B)) && negb (TW.M_state B =? TC.S_CLOSED) then
    match TC.int_inc (TW.OW_e3 B) with
    | Some e3 => Some (TW.set_M_fly_on (TW.set_M_fail (TW.set_OW_e3 B e3) 0) 0)
    | None => None
    end
  else Some (TW.set_M_fly_on B 0).
(* The arguments of op 6's call of m_set (`addi a0, zero, 3`, `addi a1, zero, 8` at +0x8e0 / +0x8e4). *)
Lemma lc_close_args : TC.S_CLOSED = 3 /\ TC.R_CLOSED = 8.
Proof. split; reflexivity. Qed.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation tfib_K := YE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* 2. The premises of the statement, in its order                      *)
(* ------------------------------------------------------------------ *)

Record lp_prem : Prop := mkLpPrem {
  lp_pc_smalloc : pc_stack_malloc (as_code B) 2 = transportb_sigma TB___asan_stack_malloc_2;
  lp_cells : transport_cells B;
  lp_scfg_cells : trans_scfg_cells B;
  lp_recv_cells : trans_recv_cells B;
  lp_settle_cells : trans_settle_cells B;
  lp_llvmf_cells : trans_llvmf_cells B;
  lp_g_unowned : trans_g_unowned B;
  lp_g_no_errno : trans_g_no_errno B;
  lp_ro_unowned : trans_ro_rd_unowned B;
  lp_rom_no_errno : trans_rom_no_errno B;
  lp_rlo : RLO <= TRANS_RLO;
  lp_rhi : TRANS_RHI <= RHI;
  lp_laws : AR_laws segs B;
  lp_meter_laws : ameter_laws MT;
  lp_meter_fs_laws : ameter_fs_laws MT;
  lp_smp : stack_malloc_progressP B;
  lp_asf : astack_free_law segs B;
  lp_ffl : frame_flag_lawP segs B;
  lp_sink_img : @asink_img_laws tfib_sink_head segs B tfib_K;
  lp_sink_kept : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md';
  lp_meta_kept : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
       ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M;
  lp_ro_below : @ro_below_ofl segs RLO RHI tfib_sink_head;
  lp_smalloc : forall fx : YK11.FPState, @astack_malloc_realizes fx rc segs B 2;
  lp_memcpy : forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (transportb_sigma TB___asan_memcpy);
  lp_scfg : forall fx : YK11.FPState,
     @transport_diginet_session_config_default_cg fx rc B MT (transportb_sigma TB_diginet_session_config_default);
  lp_memset : forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (transportb_sigma TB___asan_memset);
  lp_sinit : forall fx : YK11.FPState,
     @transport_diginet_session_init_cg fx rc B MT (transportb_sigma TB_diginet_session_init);
  lp_mwake : forall fx : YK11.FPState, @transport_m_wake_cg fx rc B MT (transportb_sigma TB_m_wake);
  lp_wake : forall fx : YK11.FPState,
     @transport_diginet_session_wake_cg fx rc B MT (transportb_sigma TB_diginet_session_wake);
  lp_cswc : forall fx : YK11.FPState, @transport_leaf_at rc B (@LCSWC.transport_check_state_wake_code_cg) fx;
  lp_mset : forall fx : YK11.FPState, @transport_m_set_cg fx rc B MT (transportb_sigma TB_m_set);
  lp_close : forall fx : YK11.FPState,
     @transport_diginet_session_close_cg fx rc B MT (transportb_sigma TB_diginet_session_close);
  lp_settle : forall fx : YK11.FPState, @transport_settle_cg fx rc B MT (transportb_sigma TB_settle);
  lp_recv : forall fx : YK11.FPState, @transport_receive_cg fx rc B MT (transportb_sigma TB_receive) CTX_receive;
  lp_mtick : forall fx : YK11.FPState, @transport_m_tick_cg fx rc B MT (transportb_sigma TB_m_tick);
  lp_tick : forall fx : YK11.FPState,
     @transport_diginet_session_tick_cg fx rc B MT (transportb_sigma TB_diginet_session_tick);
  lp_strlen : forall fx : YK11.FPState,
     @astrlen_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strlen);
  lp_bar : forall fx : YK11.FPState,
     @transport_build_and_receive_cg fx rc B MT (transportb_sigma TB_build_and_receive) CTX_build_and_receive;
  lp_submit : forall fx : YK11.FPState,
     @transport_diginet_session_submit_cg fx rc B MT (transportb_sigma TB_diginet_session_submit);
  lp_crs : forall fx : YK11.FPState, @transport_leaf_at rc B (@LCRS.transport_check_refusal_submit_cg) fx;
  lp_cls : forall fx : YK11.FPState, @transport_leaf_at rc B (@LCLS.transport_check_latest_submit_cg) fx;
  lp_cost : forall n, 0 <= n -> transport_llvmf_cost MT n <= XL n }.

(* ------------------------------------------------------------------ *)
(* 3. The context of one call                                          *)
(* ------------------------------------------------------------------ *)

(* What the entry fixes and the whole walk reads: the caller's configuration, the slot's arguments, and the one value
   the prologue invents, the position of the class-2 side-stack frame. *)
Record lcx := mkLCx {
  l_fx : YK11.FPState;
  l_ly : alayout;
  l_S : astate;
  l_W : world segs;
  l_regs : bvmap 5 word;
  l_mem : word -> option byte;
  l_md : Model;
  l_p : Z;
  l_n : Z;
  l_pl : list byte;
  l_M : Z;
  l_fpos : Z }.

Definition lc_sp0 (cx : lcx) : Z := spZ (l_regs cx).
Definition lc_sp1 (cx : lcx) : Z := 32 * ((lc_sp0 cx - LF_FRAME) / 32).
Definition lc_F (cx : lcx) : Z := frame_addr (l_ly cx) LF_CID (l_fpos cx).
Definition lc_FL (cx : lcx) : Z := flag_addr (l_ly cx) LF_CID (l_fpos cx).
Definition lc_SH (cx : lcx) : Z := SHADOW_OFF + lc_F cx / 8.

(* The slot's pre at the entry configuration; every segment takes it. *)
Definition lc_base (cx : lcx) : Prop :=
  @tfib_lib_pre_x rc B MT XL RLO RHI (l_regs cx) (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    (l_p cx) (l_n cx) (l_pl cx) (l_M cx).

(* The slot's post at the return, at the leaf transport_shape's LIBK hands the continuation (lib/FrameSlotK.v
   kept_shape: LIBK pl fs K = K (LL 0 fs [])). *)
Definition lc_post (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = @cfg_at (l_fx cx) segs RA_LLVMF regs' mem' md' /\
    @tfib_lib_post_x rc TG.G_HARNESS_B B MT XL (l_regs cx) (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
      (l_p cx) (l_n cx) (l_M cx) (YO09.LL 0 (m_fs (l_md cx)) []) ly' S' W' regs' mem' md' k.

(* ------------------------------------------------------------------ *)
(* 4. The pieces every cut shares                                      *)
(* ------------------------------------------------------------------ *)

(* The machine at an offset of the entry; no instruction of this function touches the float state. *)
Definition lc_cfg (cx : lcx) (off : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : config :=
  mkCfg (@YK11.mkst (l_fx cx) regs' (w64 (transportb_text + off)) mem' (YK11.seg_rom segs)) md'.

(* The 13 saved words are the caller's (what the epilogue reloads). *)
Definition lc_saved (cx : lcx) (r : reader) : Prop :=
  Forall (fun o : Z * Z =>
    rdword r (lc_sp0 cx - fst o) = Some (bv_unsigned (YK11.getr (l_regs cx) (Z_to_bv 5 (snd o))))) LF_SAVED.

(* The spill slots of a list hold their values. *)
Definition lc_spills (cx : lcx) (l : list (Z * Z)) (r : reader) : Prop :=
  Forall (fun o : Z * Z => rdword r (lc_sp1 cx + fst o) = Some (snd o)) l.

(* The frame's 32 shadow bytes. *)
Definition lc_fsh (cx : lcx) (r : reader) (cin bin : bool) : Prop :=
  forall i, 0 <= i < 32 -> r (lc_SH cx + i) = Some (nth (Z.to_nat i) (lf_shm cin bin) 0).

(* The caller's input: its bytes at the current memory, and unchanged as the post states it. *)
Definition lc_input (cx : lcx) (W' : world segs) (mem' : word -> option byte) : Prop :=
  garr8 segs (rd W' mem') (l_p cx) (map (fun b : byte => bv_unsigned b) (l_pl cx)) /\
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W') mem' (l_p cx + i) = aview segs (w_H (l_W cx)) (l_mem cx) (l_p cx + i)).

(* The invariant of every point after the stack malloc: the caller's G journal at FP = [] (no file range: the sink
   stays closed, so the journal keeps the file descriptors and the file system, LLVMFuzzerTestOneInput_st.v
   lc_journal_io; EXIT widens it to the post's [sink_token] by lc_fp_token) with the class-2 frame owned and e
   events, the frames and blocks, s0 / s1 / sp, gp / tp, the realigned stack, the saved words, the frame (aligned,
   present, its flag pointer in its last word) and the input. *)
Definition lc_core (cx : lcx) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly' S' W' mem' md' e /\
  frames S' = [(LF_CID, l_fpos cx)] /\ ly_F ly' = ly_F (l_ly cx) /\
  Permutation (ablocks B ly' S') (ablocks B (l_ly cx) (l_S cx)) /\
  YK11.getr regs' 2 = w64 (lc_sp1 cx) /\ YK11.getr regs' 8 = w64 (lc_sp0 cx) /\ YK11.getr regs' 9 = w64 (lc_sp1 cx) /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - LF_FRAME /\ lc_sp1 cx mod 32 = 0 /\
  lc_saved cx (aview segs (w_H W') mem') /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + LF_FBYTES <= alloc_ceiling /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a) /\
  rdword (aview segs (w_H W') mem') (lc_F cx + LF_FBYTES - 8) = Some (lc_FL cx) /\
  lc_input cx W' mem'.

(* s2 = the frame's shadow address (+0x0e0) and s10 = the shadow base (+0x060). *)
Definition lc_fr (cx : lcx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 18 = w64 (lc_SH cx) /\ YK11.getr regs' 26 = w64 SHADOW_OFF.

(* io (+0x17c: the memcpy of __const.LLVMFuzzerTestOneInput.io): { NULL, io_send, io_recv, io_now }. *)
Definition lc_io (cx : lcx) (W' : world segs) (mem' : word -> option byte) : Prop :=
  garr8 segs (rd W' mem') (lc_F cx + 176)
    (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B) (TI.ti_io_now timg_B))).

(* The world relation at the model's world Bw. *)
Definition lc_tw (W' : world segs) (mem' : word -> option byte) (Bw : list byte) : Prop :=
  tw_at TMAP_B (aview segs (w_H W') mem') Bw.

(* The meter after k receptions: at most k receive budgets spent, OPS_MAX - k left. *)
Definition lc_meter (cx : lcx) (S' : astate) (k : Z) : Prop :=
  mo_le MT (l_S cx) S' (k * lf_rcost MT) /\ mo_ok MT S' ((TC.OPS_MAX - k) * lf_rcost MT).

(* The world at the entry memory the prologue's model starts from (tw_exists_B at the entry). *)
Definition lc_w0 (cx : lcx) (Bw0 : list byte) : Prop :=
  lc_tw (l_W cx) (l_mem cx) Bw0 /\ length Bw0 = Z.to_nat TW.W_LEN.

(* The operation's start: its number, the world, the cursor before the op byte and the receptions so far. *)
Record lop := mkLop { lo_ops : Z; lo_B : list byte; lo_c : TOP.fuzz_in; lo_k : nat }.

(* What holds at the head of operation ops (InitOk / LoopOk): the simulation invariant, ops below OPS_MAX, the cursor
   in range with bytes left, and at most one reception per operation so far. *)
Definition lc_opok (cx : lcx) (op : lop) : Prop :=
  AG.agree timg_B (lo_ops op) (lo_B op) /\ 0 <= lo_ops op < TC.OPS_MAX /\ QF.fuzz_in_ok (l_pl cx) (lo_c op) /\
  TOP.fi_n (lo_c op) <> 0 /\ Z.of_nat (lo_k op) <= lo_ops op.

(* The loop's common facts at a cut inside operation op: lc_core, s2 / s10, every spill slot, the frame shadow with c
   and body in or out of scope, the operation's start facts, the events and the meter after k receptions, s3 = ops. *)
Definition lc_lcore (cx : lcx) (op : lop) (cin bin : bool) (k : nat) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (e : Z) : Prop :=
  lc_core cx ly' S' W' regs' mem' md' e /\ lc_fr cx regs' /\
  lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W') mem') /\
  lc_fsh cx (aview segs (w_H W') mem') cin bin /\
  lc_opok cx op /\ 0 <= e <= RECV_EV * Z.of_nat k /\ lc_meter cx S' (Z.of_nat k) /\
  YK11.getr regs' 19 = w64 (lo_ops op).

(* The machine cursor: register rp holds p + fi_off c and rn holds fi_n c. *)
Definition lc_cur (cx : lcx) (regs' : bvmap 5 word) (rp rn : Z) (c : TOP.fuzz_in) : Prop :=
  YK11.getr regs' (Z_to_bv 5 rp) = w64 (l_p cx + TOP.fi_off c) /\ YK11.getr regs' (Z_to_bv 5 rn) = w64 (TOP.fi_n c).

(* The loop's two constants: s4 = c (F + 32, from +0x538; op 4's tagged mode reuses s4 and reloads it from 144(s1))
   and s6 = 1 (+0x540; reset to 1 by every operation that reuses s6). *)
Definition lc_s46 (cx : lcx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 20 = w64 (lc_F cx + 32) /\ YK11.getr regs' 22 = w64 1.

(* ------------------------------------------------------------------ *)
(* 5. The state at each cut                                            *)
(* ------------------------------------------------------------------ *)

(* +0x074, the return of __asan_stack_malloc_2: a0 = F; s0, s1, s6 = p, s5 = n, s10 = the shadow base; nothing of G
   or of the frame's shadow written yet (the frame's shadow is zero, astack_malloc_realizes); no event, no meter; the
   G journal at FP = [], as lc_core states it. *)
Definition lc_st_sm (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = lc_cfg cx LO_SM regs' mem' md' /\
    ajournal_gx TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
      [(LF_CID, l_fpos cx)] ly' S' W' mem' md' 0 /\
    frames S' = [(LF_CID, l_fpos cx)] /\ ly_F ly' = ly_F (l_ly cx) /\
    ablocks B ly' S' = ablocks B (l_ly cx) (l_S cx) /\
    YK11.getr regs' 2 = w64 (lc_sp1 cx) /\ YK11.getr regs' 8 = w64 (lc_sp0 cx) /\ YK11.getr regs' 9 = w64 (lc_sp1 cx) /\
    YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
    YK11.getr regs' 10 = w64 (lc_F cx) /\ YK11.getr regs' 22 = w64 (l_p cx) /\ YK11.getr regs' 21 = w64 (l_n cx) /\
    YK11.getr regs' 26 = w64 SHADOW_OFF /\
    lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - LF_FRAME /\ lc_sp1 cx mod 32 = 0 /\
    lc_saved cx (aview segs (w_H W') mem') /\
    4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + LF_FBYTES <= alloc_ceiling /\
    (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a) /\
    rdword (aview segs (w_H W') mem') (lc_F cx + LF_FBYTES - 8) = Some (lc_FL cx) /\
    zero_shadow (aview segs (w_H W') mem') SHADOW_OFF (lc_F cx) LF_FBYTES /\
    (forall a, W_journalG.inG TG.G_HARNESS_B a -> aview segs (w_H W') mem' a = aview segs (w_H (l_W cx)) (l_mem cx) a) /\
    lc_input cx W' mem' /\
    lc_meter cx S' 0.

(* +0x358, the return of diginet_session_config_default: the frame's header, shadow (lf_shm false false) and io
   written, the flags byte read: s3 / s7 the cursor after it (+0x248 / +0x270, or +0x344 / +0x33c when n = 0),
   s8 = flags, s5 = g_cfg (+0x34c), s4 = io (+0x0a8); the model's world is config_default's world from the entry
   world Bw0. *)
Definition lc_st_cfgd (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' Bw0 B1,
    c' = lc_cfg cx LO_CFGD regs' mem' md' /\
    lc_core cx ly' S' W' regs' mem' md' 0 /\ lc_fr cx regs' /\
    lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W') mem') /\
    lc_fsh cx (aview segs (w_H W') mem') false false /\ lc_io cx W' mem' /\
    lc_meter cx S' 0 /\
    lc_cur cx regs' 19 23 (lc_c1 (l_pl cx)) /\ YK11.getr regs' 24 = w64 (lc_flags (l_pl cx)) /\
    YK11.getr regs' 21 = w64 TB_g_cfg /\ YK11.getr regs' 20 = w64 (lc_F cx + 176) /\
    lc_w0 cx Bw0 /\ TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) /\ lc_tw W' mem' B1.

(* +0x4b0, after the config bytes (+0x3a0 .. +0x43c and the out-of-line pieces +0x1868 .. +0x1b40, which rejoin
   the chain at +0x3fc .. +0x43c) and the stores of g_raw, g_now, g_fail_next (one byte) and g_last_counter
   (+0x460, +0x470, +0x4a4, +0x4ac): s9 / s7 the loop's cursor (InitOk.prologue_cursor), s6 = the desk_mac_set bit
   (+0x37c), s5 = g_cfg, s4 = io, s11 = 0x6000 (`lui s11, 6` at +0x440, read at +0x544); the world lc_pro_scal of
   config_default's world. *)
Definition lc_st_scal (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' Bw0 B1,
    c' = lc_cfg cx LO_SCAL regs' mem' md' /\
    lc_core cx ly' S' W' regs' mem' md' 0 /\ lc_fr cx regs' /\
    lc_spills cx (lf_spill_scal (lc_F cx)) (aview segs (w_H W') mem') /\
    lc_fsh cx (aview segs (w_H W') mem') false false /\ lc_io cx W' mem' /\
    lc_meter cx S' 0 /\
    lc_cur cx regs' 25 23 (IOK.prologue_cursor (l_pl cx)) /\
    YK11.getr regs' 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) /\
    YK11.getr regs' 21 = w64 TB_g_cfg /\ YK11.getr regs' 20 = w64 (lc_F cx + 176) /\
    YK11.getr regs' 27 = w64 0x6000 /\
    lc_w0 cx Bw0 /\ TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) /\
    lc_tw W' mem' (lc_pro_scal (l_pl cx) B1).

(* +0x528, the return of diginet_session_init: a0 = its result rc, s9 / s7 the cursor, s11 = 0x6000; the world and
   rc are the model's prologue lc_pro_m from Bw0. *)
Definition lc_st_init (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' Bw0 B25 r,
    c' = lc_cfg cx LO_INIT regs' mem' md' /\
    lc_core cx ly' S' W' regs' mem' md' 0 /\ lc_fr cx regs' /\
    lc_spills cx (lf_spill_init (lc_F cx)) (aview segs (w_H W') mem') /\
    lc_fsh cx (aview segs (w_H W') mem') false false /\
    lc_meter cx S' 0 /\
    lc_cur cx regs' 25 23 (IOK.prologue_cursor (l_pl cx)) /\ YK11.getr regs' 10 = w64 r /\
    YK11.getr regs' 27 = w64 0x6000 /\
    lc_w0 cx Bw0 /\ lc_pro_m timg_B Bw0 (l_pl cx) = Some (B25, r) /\ lc_tw W' mem' B25.

(* +0x58c, the head of operation lo_ops op, bytes left (`beqz s7` at +0x588 not taken): s9 / s7 the cursor lo_c op,
   s4 = c, s6 = 1; the world lo_B op; lo_k op receptions so far. *)
Definition lc_st_head (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    c' = lc_cfg cx LO_HEAD regs' mem' md' /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    lc_cur cx regs' 25 23 (lo_c op) /\ lc_s46 cx regs'.

(* The first instruction of arm o (o = the op byte mod 9): the op byte read (s9 / s7 the cursor before it, s8 / s11
   after it: +0x58c, +0x5cc), the world unchanged. *)
Definition lc_st_arm (cx : lcx) (op : lop) (o : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    c' = lc_cfg cx (lo_arm o) regs' mem' md' /\
    o = lc_opc (l_pl cx) (lo_c op) /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    lc_cur cx regs' 25 23 (lo_c op) /\ lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) /\
    lc_s46 cx regs'.

(* +0xc00, the call of receive (ops 0 and 8): a0 = the record's address, a1 = its length, a2 = by_poll, a3 = the poll
   flags (lc_recv_vals); s5 / s11 the cursor after the record (+0xbec / +0xbf0, +0xa4c / +0xa50); the world
   unchanged. *)
Definition lc_st_recv (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    let rv := lc_recv_vals (l_pl cx) (lo_c op) in
    c' = lc_cfg cx LO_RECV regs' mem' md' /\
    (lc_opc (l_pl cx) (lo_c op) = 0 \/ lc_opc (l_pl cx) (lo_c op) = 8) /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    YK11.getr regs' 10 = w64 (l_p cx + rv_off rv) /\ YK11.getr regs' 11 = w64 (rv_n rv) /\
    YK11.getr regs' 12 = w64 (rv_bp rv) /\ YK11.getr regs' 13 = w64 (rv_pf rv) /\
    lc_cur cx regs' 21 27 (rv_c rv) /\ lc_s46 cx regs'.

(* +0x1474, op 1's call of build_and_receive: a0 / a1 the dst / src table entries (+0x1440 / +0x1454), a2 = send
   (+0x1468), a3's low 32 bits = ack (the two bytes, or the sign-extending `lw` of g_last_counter at +0xd20), a4 =
   retry (+0x146c), a5 = cmd (+0x1460), a6 = the body in the input (+0x1470), a7 = its length; s5 / s11 the cursor
   after the take (+0x145c / +0x1464). *)
Definition lc_st_bar1 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    let fv := lc_frame_vals (l_pl cx) (lo_B op) (lc_oc (l_pl cx) (lo_c op)) in
    c' = lc_cfg cx LO_BAR1 regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 1 /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    YK11.getr regs' 10 = w64 (lc_fdst_a (fv_sel fv)) /\ YK11.getr regs' 11 = w64 (lc_fsrc_a (fv_sel fv)) /\
    bv_unsigned (YK11.getr regs' 12) mod 2 ^ 32 = fv_send fv /\
    bv_unsigned (YK11.getr regs' 13) mod 2 ^ 32 = fv_ack fv /\
    YK11.getr regs' 14 = w64 (fv_retry fv) /\ YK11.getr regs' 15 = w64 (lc_fcmd (fv_sel fv)) /\
    YK11.getr regs' 16 = w64 (l_p cx + fv_off fv) /\ YK11.getr regs' 17 = w64 (fv_len fv) /\
    lc_cur cx regs' 21 27 (fv_c fv) /\ lc_s46 cx regs'.

(* +0xdcc, op 2 after the zero fill of body (+0xa9c or +0xda4) and the mac copy (+0xdc8; none when mac > 12, the
   `bltu` at +0xe94), body in scope (shadow 12 .. 16 = 0 0 0 0 2: +0xa74 .. +0xa88 or +0xd7c .. +0xd90): body holds
   av_body1; s5 = sel (+0x70c, or 0 at +0xa70), s6 = the name index nm mod 3 (+0xd74, or 0 at +0x750 / +0xaa4),
   s9 = body (+0xa90 / +0xd98), s8 / s11 the cursor after the three reads, s4 = c. *)
Definition lc_st_ann (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    let av := lc_ann_vals (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
    c' = lc_cfg cx LO_ANN regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 2 /\
    lc_lcore cx op false true (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    garr8 segs (rd W' mem') (lc_F cx + 96) (TW.zs (av_body1 av)) /\
    YK11.getr regs' 21 = w64 (av_sel av) /\ YK11.getr regs' 22 = w64 (av_nm av mod 3) /\
    YK11.getr regs' 25 = w64 (lc_F cx + 96) /\ lc_cur cx regs' 24 27 (av_c av) /\
    YK11.getr regs' 20 = w64 (lc_F cx + 32).

(* +0xe6c, op 2's call of build_and_receive: a0 = SPEC_BCAST, a1 = DESK, a2 = a3 = a4 = 0, a5 = the command
   (+0xe44), a6 = body, a7 = 34; body holds av_body3 (in scope); s8 / s11 the cursor, s4 = c. *)
Definition lc_st_bar2 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e,
    let av := lc_ann_vals (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
    c' = lc_cfg cx LO_BAR2 regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 2 /\
    lc_lcore cx op false true (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' (lo_B op) /\
    garr8 segs (rd W' mem') (lc_F cx + 96) (TW.zs (av_body3 av)) /\
    YK11.getr regs' 10 = w64 TRANS_SPEC_BCAST /\ YK11.getr regs' 11 = w64 TRANS_DESK /\
    YK11.getr regs' 12 = w64 0 /\ YK11.getr regs' 13 = w64 0 /\ YK11.getr regs' 14 = w64 0 /\
    YK11.getr regs' 15 = w64 (lc_acmd (av_sel av)) /\ YK11.getr regs' 16 = w64 (lc_F cx + 96) /\
    YK11.getr regs' 17 = w64 34 /\
    lc_cur cx regs' 24 27 (av_c av) /\ YK11.getr regs' 20 = w64 (lc_F cx + 32).

(* +0xcf4, op 3's call of m_tick: op_begin's world B1, then the g_now store (lc_tick_w, +0xcf0); s6 = g_now's page
   (transportb_hi 9, `ld s6, 0x98(s1)` at +0xcdc: g_now is read again through it after m_tick, +0xcf8), s8 / s11 the
   cursor after the u16, s4 = c. *)
Definition lc_st_tick (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let c1 := lc_oc D (lo_c op) in
    c' = lc_cfg cx LO_TICK regs' mem' md' /\
    lc_opc D (lo_c op) = 3 /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    TC.op_begin_m (lo_B op) = Some (B1, tt) /\ lc_tw W' mem' (lc_tick_w D c1 B1) /\
    YK11.getr regs' 22 = w64 (transportb_hi 9) /\
    lc_cur cx regs' 24 27 (lc_tick_c D c1) /\
    YK11.getr regs' 20 = w64 (lc_F cx + 32).

(* Op 4 after op_begin, the memset of c and the key and display bytes (c in scope, +0x630): c holds
   cmd_struct (24 zeros) 0 display key (key word at c + 28, +0xb00; display byte at c + 25, +0xb3c or +0xb98), the
   world op_begin's B1. *)
Definition lc_sub_common (cx : lcx) (op : lop) (B1 : list byte) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (e : Z) : Prop :=
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  lc_opc D (lo_c op) = 4 /\
  lc_lcore cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
  TC.op_begin_m (lo_B op) = Some (B1, tt) /\ lc_tw W' mem' B1 /\
  garr8 segs (rd W' mem') (lc_F cx + 32) (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd) (sv_key kd))).
(* +0x12bc, raw mode (g_raw B1 <> 0), the length word read (+0xb48 .. +0xb8c, +0xf78 .. +0xf90, +0xba0 .. +0xbac,
   +0x128c .. +0x12b8): a1 = the u16 w, s8 / s7 the cursor after it, s5 = the queue length before (S_queued of the
   start world, sign-extended from 32 bits as the `lw` at +0x64c leaves it and check_refusal_submit's a2 asks),
   s4 = c, s6 = 1. *)
Definition lc_st_subr (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
    c' = lc_cfg cx LO_SUBR regs' mem' md' /\
    lc_sub_common cx op B1 ly' S' W' regs' mem' md' e /\ TW.g_raw B1 <> 0 /\
    YK11.getr regs' 21 = w64 (bv_swrap 32 (TW.S_queued (lo_B op))) /\
    YK11.getr regs' 11 = w64 (lc_raw_w D (sv_c kd)) /\ lc_cur cx regs' 24 23 (lc_raw_c4 D (sv_c kd)) /\
    lc_s46 cx regs'.
(* +0xfa4, tagged mode (g_raw B1 = 0; +0xd14 or +0xf94): s9 / s6 the cursor after the display byte, s4 = 1 (the
   constant of the UBSan cursor test at +0xfec; c is reloaded from 144(s1) at +0xffc / +0x1038), 24(s1) = the queue
   length before (sign-extended, +0xd14 / +0xf94). *)
Definition lc_st_subt (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
    c' = lc_cfg cx LO_SUBT regs' mem' md' /\
    lc_sub_common cx op B1 ly' S' W' regs' mem' md' e /\ TW.g_raw B1 = 0 /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 24) =
      Some (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op))))) /\
    lc_cur cx regs' 25 22 (sv_c kd) /\ YK11.getr regs' 20 = w64 1.

(* The tagged mode after the memset of g_cmd[serial] (+0xfe0), the len byte, the tag and serial bytes and the copy of
   the input bytes into c (+0x109c): the world tg_B2, c holds cmd_struct cbytes len display key, 24(s1) the queue
   length before, 16(s1) the cursor's bytes left before the take (+0x1084), 8(s1) the bytes taken (+0x1098),
   64(s1) serial (+0xfb0); s8 = the cursor after the take (+0x1088; its bytes left are 16(s1) - 8(s1), +0x1644),
   s11 = g_cmd (+0xfc8), s4 = c, s7 = 0x401 (+0xfac, the bound of the find loop's index test). *)
Definition lc_tag_common (cx : lcx) (op : lop) (B1 : list byte) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (e : Z) : Prop :=
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_opc D (lo_c op) = 4 /\
  lc_lcore cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
  TC.op_begin_m (lo_B op) = Some (B1, tt) /\ TW.g_raw B1 = 0 /\ 0 <= tg_serial tv < TC.CMDS_MAX /\
  lc_tw W' mem' (tg_B2 tv) /\
  garr8 segs (rd W' mem') (lc_F cx + 32) (TW.zs (TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd))) /\
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 24) =
    Some (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op))))) /\
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 tv)) /\
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 8) = Some (tg_n tv) /\
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (tg_serial tv) /\
  YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off (tg_c tv)) /\ YK11.getr regs' 27 = w64 TB_g_cmd /\
  YK11.getr regs' 20 = w64 (lc_F cx + 32) /\ YK11.getr regs' 23 = w64 0x401.

(* +0x10b0, the head of turn i of the spec_system_at loop over c (+0x10b0 .. +0x1134): no hit at the positions below
   i; a2 = len (+0x10a0), a3 = i + 3, s5 = g_cmd + 40 serial (+0xfcc), s6 = 3, s9 = 0xf0 (+0x1074 / +0x1078). *)
Definition lc_st_sysl (cx : lcx) (op : lop) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in
    c' = lc_cfg cx LO_SYSL regs' mem' md' /\
    lc_tag_common cx op B1 ly' S' W' regs' mem' md' e /\
    0 <= i < tg_len tv - 3 /\ i < 21 /\
    (forall j : nat, (j < Z.to_nat i)%nat -> DSpec.sys_hit (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) j = false) /\
    YK11.getr regs' 12 = w64 (tg_len tv) /\ YK11.getr regs' 13 = w64 (i + 3) /\
    YK11.getr regs' 21 = w64 (TB_g_cmd + 40 * tg_serial tv) /\
    YK11.getr regs' 22 = w64 3 /\ YK11.getr regs' 25 = w64 0xf0.

(* +0x1170, after the loop (or with len < 4, +0x115c): t2 = 1 exactly when spec_system_at finds a hit (+0x1164 ..
   +0x116c), s5 = g_cmd + 40 serial. *)
Definition lc_st_sysj (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in
    c' = lc_cfg cx LO_SYSJ regs' mem' md' /\
    lc_tag_common cx op B1 ly' S' W' regs' mem' md' e /\
    YK11.getr regs' 7 = w64 (if lc_sys tv then 1 else 0) /\
    YK11.getr regs' 21 = w64 (TB_g_cmd + 40 * tg_serial tv).

(* +0x11ec, the head of turn i of the find loop over g_q (key coalescable, g_nq <> 0): the search from i answers as the
   search from 0; a0 = a6 = g_q + 4 i, a4 = i, a5 = i + 1, a3 = g_nq, a7 = 2 ^ 32 - 1, a2 = key (zero-extended,
   +0x1170), t2 = the sys flag, s5 = g_cmd + 40 serial. *)
Definition lc_st_find (cx : lcx) (op : lop) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
    let tv := lc_tag_vals D B1 (sv_c kd) in
    c' = lc_cfg cx LO_FIND regs' mem' md' /\
    lc_tag_common cx op B1 ly' S' W' regs' mem' md' e /\
    TC.h_coalescable_m (sv_key kd) <> 0 /\
    0 <= i < TW.g_nq (tg_B2 tv) /\ i < TC.CMDS_MAX /\
    TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) (tg_B2 tv) (sv_key kd) 0 =
      TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat i) (tg_B2 tv) (sv_key kd) i /\
    YK11.getr regs' 10 = w64 (TB_g_q + 4 * i) /\ YK11.getr regs' 16 = w64 (TB_g_q + 4 * i) /\
    YK11.getr regs' 14 = w64 i /\ YK11.getr regs' 15 = w64 (i + 1) /\
    YK11.getr regs' 13 = w64 (TW.g_nq (tg_B2 tv)) /\ YK11.getr regs' 17 = w64 (2 ^ 32 - 1) /\
    YK11.getr regs' 12 = w64 (sv_key kd) /\ YK11.getr regs' 7 = w64 (if lc_sys tv then 1 else 0) /\
    YK11.getr regs' 21 = w64 (TB_g_cmd + 40 * tg_serial tv).

(* +0x1498, the tagged mode with want decided (+0x1190 .. +0x11b0, +0x1480 .. +0x1494): s6 = want, s9 = at mod 2 ^ 32,
   zero-extended (i, or 0xffffffff for -1: +0x1184, +0x1238 / +0x1240), s5 = the sys flag (+0x1194), 0(s1) =
   g_cmd + 40 serial (+0x1190). *)
Definition lc_st_want (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1 at_,
    let D := l_pl cx in
    let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
    let tv := lc_tag_vals D B1 (sv_c kd) in
    c' = lc_cfg cx LO_WANT regs' mem' md' /\
    lc_tag_common cx op B1 ly' S' W' regs' mem' md' e /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx) = Some (TB_g_cmd + 40 * tg_serial tv) /\
    lc_at tv (sv_key kd) = Some at_ /\
    YK11.getr regs' 22 = w64 (lc_want tv at_) /\ YK11.getr regs' 25 = w64 (at_ mod 2 ^ 32) /\
    YK11.getr regs' 21 = w64 (if lc_sys tv then 1 else 0).

(* +0x14cc, after diginet_session_submit, check_refusal_submit and (unless sys) check_latest_submit: the world B5 of
   the model's three steps; s6 = want, s9 = at mod 2 ^ 32 (zero-extended), s8 / s11 / s4 as before, 0(s1), 8(s1),
   16(s1) and 64(s1) kept. *)
Definition lc_st_cmdw (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1 at_ B3 rc B4 B5,
    let D := l_pl cx in
    let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
    let tv := lc_tag_vals D B1 (sv_c kd) in
    let cs := TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) in
    c' = lc_cfg cx LO_CMDW regs' mem' md' /\
    lc_opc D (lo_c op) = 4 /\
    lc_lcore cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
    TC.op_begin_m (lo_B op) = Some (B1, tt) /\ TW.g_raw B1 = 0 /\ 0 <= tg_serial tv < TC.CMDS_MAX /\
    lc_at tv (sv_key kd) = Some at_ /\
    TS0.diginet_session_submit_m (tg_B2 tv) cs = Some (B3, rc) /\
    TC.check_refusal_submit_m B3 cs rc (TW.S_queued (lo_B op)) = Some (B4, tt) /\
    (if lc_sys tv then B5 = B4 else TC.check_latest_submit_m B4 rc (lc_want tv at_) = Some (B5, tt)) /\
    lc_tw W' mem' B5 /\
    garr8 segs (rd W' mem') (lc_F cx + 32) (TW.zs cs) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx) = Some (TB_g_cmd + 40 * tg_serial tv) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 tv)) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 8) = Some (tg_n tv) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (tg_serial tv) /\
    YK11.getr regs' 22 = w64 (lc_want tv at_) /\ YK11.getr regs' 25 = w64 (at_ mod 2 ^ 32) /\
    YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off (tg_c tv)) /\ YK11.getr regs' 27 = w64 TB_g_cmd /\
    YK11.getr regs' 20 = w64 (lc_F cx + 32).

(* +0x1654, op 4's call of settle (`mv a0, zero` +0x1654, the call +0x1658), raw (+0x1344) and tagged (+0x1650): the
   world Bw, at which settle_m Bw 0 answers Some (Bw, tt), and the operation's model equation, whose result is Bw
   (settle keeps the world: LLVMFuzzerTestOneInput_st.v lc_settle_world); s8 / s11 the cursor after the take, s4 = c,
   s6 = 1. *)
Definition lc_st_s4 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e Bw c5,
    c' = lc_cfg cx LO_S4 regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 4 /\
    lc_lcore cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' Bw /\
    TC.settle_m Bw 0 = Some (Bw, tt) /\
    (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
               Some (Bw, (c5, lo_k op))) /\
    lc_cur cx regs' 24 27 c5 /\ lc_s46 cx regs'.

(* +0x8e8, op 6's call of m_set (image B only): op_begin (+0x878, +0x88c, +0x890 .. +0x8a8) and m_close's own steps
   (+0x89c .. +0x8dc: OW.e3 + 1 and M.fail = 0 when the desk is known, not foreign and not closed, then M.fly.on = 0)
   done, the world lc_close_w of op_begin's world; a0 = S_CLOSED, a1 = R_CLOSED; s8 / s11 the cursor after the op
   byte, s4 = c, s6 = 1. *)
Definition lc_st_mset (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1 B2,
    c' = lc_cfg cx LO_MSET regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 6 /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    TC.op_begin_m (lo_B op) = Some (B1, tt) /\ lc_close_w B1 = Some B2 /\ lc_tw W' mem' B2 /\
    YK11.getr regs' 10 = w64 TC.S_CLOSED /\ YK11.getr regs' 11 = w64 TC.R_CLOSED /\
    lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) /\ lc_s46 cx regs'.

(* +0x8ec, op 6 after m_set returned: the world of m_close_m. *)
Definition lc_st_cls (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1 B2,
    c' = lc_cfg cx LO_CLS regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 6 /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    TC.op_begin_m (lo_B op) = Some (B1, tt) /\ TC.m_close_m B1 = Some (B2, tt) /\ lc_tw W' mem' B2 /\
    lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) /\ lc_s46 cx regs'.

(* +0x900, the call of settle of ops 5 and 6: the world Bw, at which settle_m Bw 0 answers Some (Bw, tt), and the
   operation's model equation, whose result is Bw; the cursor (s8 / s11) is the one after the op byte. *)
Definition lc_st_set56 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e Bw,
    c' = lc_cfg cx LO_SET56 regs' mem' md' /\
    (lc_opc (l_pl cx) (lo_c op) = 5 \/ lc_opc (l_pl cx) (lo_c op) = 6) /\
    lc_lcore cx op false false (lo_k op) ly' S' W' regs' mem' md' e /\
    lc_tw W' mem' Bw /\
    TC.settle_m Bw 0 = Some (Bw, tt) /\
    (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
               Some (Bw, (lc_oc (l_pl cx) (lo_c op), lo_k op))) /\
    lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) /\ lc_s46 cx regs'.

(* +0x1670, the loop tail of operation lo_ops op: the operation done, by the model's equation at the stream
   fun _ => a; s8 / s11 the cursor after it, s3 = ops, s4 = c, s6 = 1; k receptions now. *)
Definition lc_st_tail (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e a Bw cn k',
    c' = lc_cfg cx LO_TAIL regs' mem' md' /\
    lc_lcore cx op false false k' ly' S' W' regs' mem' md' e /\
    recv_addr_ok a /\
    TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) (fun _ => a) (l_pl cx) (lo_c op) (lo_k op) = Some (Bw, (cn, k')) /\
    lc_tw W' mem' Bw /\
    lc_cur cx regs' 24 27 cn /\ lc_s46 cx regs'.

(* +0x188, the epilogue: the frame with its base shadow and the two spill slots of the frame (136(s1) for the header
   store at +0x1a4, 128(s1) for the real-stack test at +0x1ac), at most EV_LIB events and the meter within the cost,
   from k <= OPS_MAX receptions. *)
Definition lc_st_exit (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e k,
    c' = lc_cfg cx LO_EXIT regs' mem' md' /\
    lc_core cx ly' S' W' regs' mem' md' e /\ lc_fr cx regs' /\
    lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W') mem') /\
    lc_fsh cx (aview segs (w_H W') mem') false false /\
    0 <= k <= TC.OPS_MAX /\ 0 <= e <= RECV_EV * k /\ lc_meter cx S' k.

(* ------------------------------------------------------------------ *)
(* 6. The segment statements                                           *)
(* ------------------------------------------------------------------ *)

(* Each comment names the code blocks the segment's walk runs (offsets from the entry; the control-flow region from
   its start cut to the next cuts, the out-of-line slow paths of the checked loads, their report calls and the UBSan
   trap word +0x1b44 included), as LLVMFuzzerTestOneInput_st.v section 5 lists them per segment. *)

(* ENTRY, +0x000 .. +0x070: the frame and the probe store, the 13 saves, s0, the realign into s1, s5 = n, the two GOT
   words and the cells they point at (s10 = the shadow base), s6 = p, `beqz a2` at +0x068 (not taken: the flag word
   is 1; its target +0x078 and the real-stack arm after it are refuted), `addi a0, zero, 0x100` and the call of
   __asan_stack_malloc_2 by lp_smalloc at lp_pc_smalloc's pc, at the position and state that lp_smp
   (stack_malloc_progressP, with AR's am_wf and frames S = []) gives; that position is the existential the rest of
   the walk is built on. *)
Definition lc_entry_stmt : Prop :=
  lp_prem ->
  forall (fx : YK11.FPState) ly S (W : world segs) regs mem md p n pl M,
    @tfib_lib_pre_x rc B MT XL RLO RHI regs ly S W mem md p n pl M ->
    SRr segs W (@cfg_at fx segs A_LLVMF regs mem md)
      (fun W' c' => exists fpos, lc_st_sm (mkLCx fx ly S W regs mem md p n pl M fpos) W' c').

(* HDR, +0x074, +0x07c .. +0x184, +0x244 .. +0x274, +0x33c .. +0x354 and the slow path +0x1b54 .. +0x1b64 (report
   +0x1b64): the real-stack arm +0x084 .. +0x09c not entered (the call returned F), F into 128(s1), 208(s1) and
   136(s1), the header (magic, descriptor, the function's address) at F, the 32 shadow bytes, the memcpy of io
   (+0x17c), the size test (+0x180 / +0x184; its fall-through +0x188 refuted: n < 2 ^ 26), the flags byte (+0x244 ..
   +0x274: the UBSan cursor test +0x250 / +0x254, the checked load at p when n > 0; +0x33c .. +0x344 when n = 0) and
   the call of diginet_session_config_default (+0x354, lp_scfg) at g_cfg. *)
Definition lc_hdr_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_sm cx W' c' -> SRr segs W' c' (lc_st_cfgd cx).

(* CFG, +0x358 .. +0x4ac, the out-of-line pieces +0x1868 .. +0x1b40 and the slow paths and reports +0x1b68 ..
   +0x1c14, +0x1c2c .. +0x1c38, +0x1d3c .. +0x1d58: the memcpy of HOST into g_cfg (+0x368), the three flag bits, the
   memcpy of DESK (+0x39c), the fourteen config bytes (each a UBSan cursor test and a checked load at the cursor while
   bytes are left) and their stores into g_cfg, then the stores of g_raw, g_now, g_fail_next (one byte) and
   g_last_counter. *)
Definition lc_cfg_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_cfgd cx W' c' -> SRr segs W' c' (lc_st_scal cx).

(* MINIT, +0x4b0 .. +0x524: the memset of M + 8 (1640 bytes, +0x4c4), desk_known at M, the memcpy of DESK to M + 4
   (+0x4e0), the stores of g_nq, g_ncmd and g_rx, and the call of diginet_session_init (+0x524, lp_sinit) with
   a2 = io (F + 176), a3 = notice, a4 = 0. *)
Definition lc_minit_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_scal cx W' c' -> SRr segs W' c' (lc_st_init cx).

(* PRE, +0x528 .. +0x588: `beqz a0` at +0x528 (taken: the model's rc is SPEC_OK, so the `j` at +0x52c to the abort
   pair +0x1b48 / +0x1b4c is not reached), s3 = 0, s4 = c, s6 = 1 and the spill slots of the loop (+0x548 .. +0x584),
   `beqz s7` at +0x588 (no byte left: the epilogue). The head's simulation facts come from the model's prologue
   (lc_pro_agree_stmt). *)
Definition lc_pre_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_init cx W' c' ->
    SRr segs W' c' (fun W2 c2 => (exists op, lo_ops op = 0 /\ lc_st_head cx op W2 c2) \/ lc_st_exit cx W2 c2).

(* HEAD, +0x58c .. +0x5f0, the slow path +0x16b8 .. +0x16c0 and its report +0x1c60 .. +0x1c64: the UBSan cursor test
   (+0x590 / +0x594), the checked load of the op byte, op = byte % 9 (+0x5b0 .. +0x5c8), `bltu a1, a0` (op 8, +0x5d4)
   and the jump through the table at 0x20f5c (`jr a0`, +0x5f0) to arm op. *)
Definition lc_head_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_head cx op W' c' ->
    SRr segs W' c' (fun W2 c2 => exists o, lc_st_arm cx op o W2 c2).

(* OP0, +0x5f4 .. +0x62c, +0x9f8 .. +0xa04, +0xbb0 .. +0xbfc, the slow paths +0x16f4 .. +0x16fc, +0x1754 .. +0x175c
   and the reports +0x1c88 .. +0x1c8c, +0x1cc4 .. +0x1cc8 (op 0): the record's length (fuzz_record: two UBSan cursor
   tests and checked loads, the min with the bytes left, the UBSan test of the take at +0xbe8), then the arguments of
   receive: by_poll = 0, poll_flags = 0. *)
Definition lc_op0_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 0 W' c' -> SRr segs W' c' (lc_st_recv cx op).

(* OP8, +0x90c .. +0x940, +0xa24 .. +0xa5c, +0xc84 .. +0xcb0, +0xf4c .. +0xf74, the slow paths +0x170c .. +0x1714,
   +0x176c .. +0x1774, +0x17c0 .. +0x17c8 and the reports +0x1c98 .. +0x1c9c, +0x1cd0 .. +0x1cd4, +0x1d00 .. +0x1d04
   (op 8): the poll flags byte, then the record and the arguments: by_poll = 1 (the take's UBSan test at +0xa44, the
   jump to the call at +0xa5c). *)
Definition lc_op8_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 8 W' c' -> SRr segs W' c' (lc_st_recv cx op).

(* RECV, +0xc00 .. +0xc04 and +0x1478 .. +0x147c: the call of receive (lp_recv at CTX_receive), `j` to +0x1478,
   s8 = s5, `j` to the tail; the operation's model equation from receive's X. *)
Definition lc_recv_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_recv cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP1, +0x7b4 .. +0x7f0, +0xa08 .. +0xa20, +0xc08 .. +0xc80, +0xd1c .. +0xd38, +0xec4 .. +0xf48, +0x1348 .. +0x1470,
   +0x15dc .. +0x15e4, +0x168c .. +0x16b4, the slow paths +0x16c4 .. +0x16cc, +0x1700 .. +0x1708, +0x173c .. +0x1744,
   +0x1760 .. +0x1768, +0x17a8 .. +0x17bc, +0x1814 .. +0x1828, +0x185c .. +0x1864 and the reports +0x1c20 .. +0x1c28,
   +0x1c68 .. +0x1c6c, +0x1c90 .. +0x1c94, +0x1cb8, +0x1ccc, +0x1cf4 .. +0x1cfc, +0x1d20 .. +0x1d28 (op 1, op_frame):
   the checked byte loads of sel, send, ack, retry and w, the plain load of g_last_counter when sel & 0x80 (+0xd20),
   len = min (w mod 1485, n) (+0x136c .. +0x13b4), the checked 8-byte loads of op_frame.DST / SRC and the checked byte
   load of op_frame.CMD (+0x13b8 .. +0x1460), with their UBSan tests. *)
Definition lc_op1_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 1 W' c' -> SRr segs W' c' (lc_st_bar1 cx op).

(* BAR1, +0x1474 .. +0x147c: the call of build_and_receive (lp_bar at CTX_build_and_receive), s8 = s5, `j` to the
   tail. *)
Definition lc_bar1_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_bar1 cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP2A, +0x6e8 .. +0x754, +0xa70 .. +0xaac, +0xd3c .. +0xdc8, +0xe90 .. +0xec0, the slow paths +0x16d0 .. +0x16d8,
   +0x1730 .. +0x1738, +0x179c .. +0x17a4 and the reports +0x1c70 .. +0x1c74, +0x1cb0 .. +0x1cb4, +0x1cec .. +0x1cf0
   (op 2): the checked byte loads of sel, mac and name (name mod 3 by the divisor constant 0x10310, +0xd58 .. +0xd74),
   body's shadow into scope, the memset of body (+0xa9c or +0xda4) and the memcpy of HOST (body + mac, mac < 10) or
   OTHER (body + mac - 10, 10 <= mac <= 12) into it (+0xdc8; none when mac > 12), with the UBSan tests of body + mac
   (+0xdb4 / +0xe9c, +0xea8, +0xeb0). *)
Definition lc_op2a_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 2 W' c' -> SRr segs W' c' (lc_st_ann cx op).

(* OP2B, +0xdcc .. +0xe68 and the report +0x1c1c: "1.37" at body + 15 (+0xdd4 .. +0xdf0), the checked 8-byte load of
   op_announce.NAME[name] (+0xe24), the strlen wrapper (+0xe2c, lp_strlen), the memcpy of the name to body + 24
   (+0xe3c), and the arguments of build_and_receive, with the UBSan tests of body + 15, body + 24 and NAME + 8 name
   (+0xdd0, +0xdf8, +0xe0c). *)
Definition lc_op2b_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_ann cx op W' c' -> SRr segs W' c' (lc_st_bar2 cx op).

(* BAR2, +0xe6c .. +0xe8c: the call of build_and_receive, body's shadow out of scope (+0xe70 .. +0xe84), s6 = 1,
   `j` to the tail. *)
Definition lc_bar2_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_bar2 cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP3A, +0x758 .. +0x7a4, +0x958 .. +0x9f4, +0xa60 .. +0xa6c, +0xcb4 .. +0xcf0, the slow paths +0x16e8 .. +0x16f0,
   +0x1724 .. +0x172c, +0x1778 .. +0x1780 and the reports +0x1c18, +0x1c80 .. +0x1c84, +0x1ca8 .. +0x1cac, +0x1cd8
   (op 3): the checked byte load, the checked 8-byte load of SCALE (+0x978, the UBSan index test +0x790), op_begin
   (the memsets of OW and GOT at +0x98c / +0x9a0, the load of g_fail_next, OW.desk_off, M.fail), the u16,
   g_now += SCALE * u16 (+0xcdc .. +0xcf0). *)
Definition lc_op3a_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 3 W' c' -> SRr segs W' c' (lc_st_tick cx op).

(* OP3B, +0xcf4 .. +0xd10 and +0xe88 .. +0xe8c: the calls of m_tick, diginet_session_tick (a1 = g_now read again,
   +0xcf8) and settle (a0 = 1), s6 = 1, `j` to the tail. *)
Definition lc_op3b_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_tick cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP4A, +0x630 .. +0x6e4, +0x944 .. +0x954, +0xab0 .. +0xbac, +0xd14 .. +0xd18, +0xf78 .. +0xfa0, +0x128c .. +0x12b8,
   the slow paths +0x16dc .. +0x16e4, +0x1718 .. +0x1720, +0x1748 .. +0x1750, +0x1784 .. +0x178c, +0x1808 .. +0x1810
   and the reports +0x1c78 .. +0x1c7c, +0x1ca0 .. +0x1ca4, +0x1cbc .. +0x1cc0, +0x1cdc .. +0x1ce0, +0x1d1c (op 4): c's
   shadow into scope, the load of g_s.queued into s5 (+0x64c), op_begin (memsets +0x664 / +0x678), the memset of c
   (+0x6a0), the key and display bytes into c, the load of g_raw and `beqz` (+0xb44 or +0xb9c), and in raw mode the
   two bytes of the length word. *)
Definition lc_op4a_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 4 W' c' ->
    SRr segs W' c' (fun W2 c2 => lc_st_subr cx op W2 c2 \/ lc_st_subt cx op W2 c2).

(* OP4R, +0x12bc .. +0x1344 (raw mode): w mod 25, the take (UBSan test +0x1300), c.len (+0x1310), the memcpy of the
   input bytes into c (+0x131c), the calls of diginet_session_submit (+0x132c) and check_refusal_submit (+0x133c),
   `j` to the settle call. *)
Definition lc_op4r_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_subr cx op W' c' -> SRr segs W' c' (lc_st_s4 cx op).

(* OP4T, +0xfa4 .. +0x10ac, +0x115c .. +0x1160, the slow path +0x1790 .. +0x1798 and the report +0x1ce4 .. +0x1ce8
   (tagged mode): serial and its UBSan index test (+0xfb4), the memset of g_cmd[serial] (+0xfe0, UBSan test +0xfd0),
   the len byte (cursor test +0xfec; len mod 22 by the divisor constant 0x103a8), the tag and serial bytes into c, the
   memcpy of the input bytes to c + 3 (+0x109c, UBSan tests of the take +0x108c / +0x1090), and the entry of the
   spec_system_at loop (len < 4: none, +0x115c). *)
Definition lc_op4t_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_subt cx op W' c' ->
    SRr segs W' c' (fun W2 c2 => lc_st_sysl cx op 0 W2 c2 \/ lc_st_sysj cx op W2 c2).

(* OP4SYS, +0x10b0 .. +0x1158, +0x1164 .. +0x116c and the reports +0x1c3c .. +0x1c4c: one turn of the
   spec_system_at loop (the checked loads of c[i], c[i + 1], c[i + 3] with their UBSan tests +0x10b4, +0x10e4,
   +0x110c and slow paths +0x1138 .. +0x1158), its exit to SYSJ. *)
Definition lc_op4sys_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (i : Z) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_sysl cx op i W' c' ->
    SRr segs W' c' (fun W2 c2 => lc_st_sysl cx op (i + 1) W2 c2 \/ lc_st_sysj cx op W2 c2).

(* OP4COAL, +0x1170 .. +0x11e8 and +0x1480 .. +0x1494: the key's kind (coalescable unless 0, 8 or 9), the plain load of
   g_nq, the entry of the find loop, or want with at = -1 (+0x1190 .. +0x11b0, +0x1480 .. +0x1494). *)
Definition lc_op4coal_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_sysj cx op W' c' ->
    SRr segs W' c' (fun W2 c2 => lc_st_find cx op 0 W2 c2 \/ lc_st_want cx op W2 c2).

(* OP4FIND, +0x11ec .. +0x1288, its exit to want +0x1190 .. +0x11b0 and +0x1480 .. +0x1494, and the reports +0x1c50 ..
   +0x1c58: one turn of the find loop (the UBSan index tests +0x11ec, +0x1208, +0x1218, the checked loads of g_q[i] and
   g_cmd[g_q[i]].key with their slow paths +0x126c .. +0x1288). *)
Definition lc_op4find_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (i : Z) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_find cx op i W' c' ->
    SRr segs W' c' (fun W2 c2 => lc_st_find cx op (i + 1) W2 c2 \/ lc_st_want cx op W2 c2).

(* OP4SUB, +0x1498 .. +0x14c8: the calls of diginet_session_submit (+0x14a4), check_refusal_submit (+0x14b8) and,
   unless sys, check_latest_submit (+0x14c8). *)
Definition lc_op4sub_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_want cx op W' c' -> SRr segs W' c' (lc_st_cmdw cx op).

(* OP4ST, +0x14cc .. +0x15d8, +0x15e8 .. +0x1650, the slow paths +0x17cc .. +0x1804, +0x182c .. +0x1858 and the
   reports +0x1c5c, +0x1d08 .. +0x1d18, +0x1d2c .. +0x1d38: when want = 0 the UBSan tests of serial and the pointer
   (+0x14dc / +0x14e0), the checked stores of g_cmd[serial]'s st, key, display, len and the memcpy of c's bytes
   (+0x1558), then the replace (g_cmd[g_q[at]].st: +0x1564 .. +0x15d8) or the append (g_nq + 1: +0x15e8 .. +0x1624),
   both ending in the store g_q[at or old g_nq] = serial and the reload of s4 (+0x1628 .. +0x1630); g_ncmd + 1 and the
   cursor's bytes left (+0x1634 .. +0x1650). *)
Definition lc_op4st_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_cmdw cx op W' c' -> SRr segs W' c' (lc_st_s4 cx op).

(* OP4S, +0x1654 .. +0x166c: the call of settle (a0 = 0), c's shadow out of scope. *)
Definition lc_op4s_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_s4 cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP5, +0x7f4 .. +0x860 (op 5): op_begin (memsets +0x808 / +0x81c), the calls of m_wake (+0x838),
   diginet_session_wake (+0x850, a1 = g_now) and check_state_wake_code (+0x85c, a leaf), s6 = 1, `j` to the settle
   call. *)
Definition lc_op5_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 5 W' c' -> SRr segs W' c' (lc_st_set56 cx op).

(* OP6A, +0x864 .. +0x8e4 (op 6): op_begin (memsets +0x878 / +0x88c) and m_close up to its call of m_set (the plain
   loads of M.desk_known, M.foreign, M.state and OW.e3, OW.e3 + 1 with the UBSan test +0x8cc / +0x8d0, M.fail = 0,
   M.fly.on = 0), a0 = 3, a1 = 8. *)
Definition lc_op6a_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 6 W' c' -> SRr segs W' c' (lc_st_mset cx op).

(* OP6M, +0x8e8 (image B only): the call of m_set (lp_mset). *)
Definition lc_op6m_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_mset cx op W' c' -> SRr segs W' c' (lc_st_cls cx op).

(* OP6B, +0x8ec .. +0x8fc: the plain load of g_now and the call of diginet_session_close. *)
Definition lc_op6b_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_cls cx op W' c' -> SRr segs W' c' (lc_st_set56 cx op).

(* SET56, +0x900 .. +0x908: the call of settle (a0 = 0), `j` to the tail. *)
Definition lc_set56_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_set56 cx op W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* OP7, +0x7a8 .. +0x7b0 (op 7): the one-byte store g_fail_next = s6 = 1, `j` to the tail. *)
Definition lc_op7_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_arm cx op 7 W' c' -> SRr segs W' c' (lc_st_tail cx op).

(* TAIL, +0x1670 .. +0x1688 and +0x588: ops + 1 (`addiw`), s7 = s11, s9 = s8, `beq s3, a0` (ops + 1 = 1024: the
   epilogue, +0x1688), `j` to +0x588, `beqz s7` (no byte left: the epilogue) or the next head; the next head's
   simulation facts by LLVMFuzzerTestOneInput_st.v lc_tail_opok. *)
Definition lc_tail_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (op : lop) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_tail cx op W' c' ->
    SRr segs W' c'
      (fun W2 c2 => (exists op', lo_ops op' = lo_ops op + 1 /\ lc_st_head cx op' W2 c2) \/ lc_st_exit cx W2 c2).

(* EXIT, +0x188 .. +0x240 and +0x278 .. +0x338: io's shadow out of scope, the header word 0x45e0360e at F (through
   136(s1)), `beqz a1` (not taken: 128(s1) = F; the real-stack arm +0x278 .. +0x2f4 refuted), the 32 shadow bytes to
   0xf5, the release through the flag pointer at F + 248 (astack_free_law, +0x238 / +0x23c), a0 = 0, sp = s0 - 320,
   the 13 reloads, sp + 320 and `ret`. The post's clauses from the journal at FP = [] with own = [] after the
   release: HSINK_KEPT (lp_sink_kept) at FP = [], its premise ~ sink_open_fp [] by YCbq.v sink_closed_nil, gives
   asink_none; HMETA_KEPT (lp_meta_kept) gives ameta_inv; LLVMFuzzerTestOneInput_st.v lc_journal_io gives the file
   descriptors and m_fs md' = m_fs md (= ll_fs (LL 0 (m_fs md) [])); lc_fp_token widens the journal to the post's
   FP = [sink_token]. *)
Definition lc_exit_stmt : Prop :=
  lp_prem -> forall (cx : lcx) (W' : world segs) (c' : config),
    lc_base cx -> lc_st_exit cx W' c' -> SRr segs W' c' (lc_post cx).

Record lc_segments : Prop := mkLcSegments {
  sg_entry : lc_entry_stmt; sg_hdr : lc_hdr_stmt; sg_cfg : lc_cfg_stmt; sg_minit : lc_minit_stmt;
  sg_pre : lc_pre_stmt; sg_head : lc_head_stmt;
  sg_op0 : lc_op0_stmt; sg_op8 : lc_op8_stmt; sg_recv : lc_recv_stmt;
  sg_op1 : lc_op1_stmt; sg_bar1 : lc_bar1_stmt;
  sg_op2a : lc_op2a_stmt; sg_op2b : lc_op2b_stmt; sg_bar2 : lc_bar2_stmt;
  sg_op3a : lc_op3a_stmt; sg_op3b : lc_op3b_stmt;
  sg_op4a : lc_op4a_stmt; sg_op4r : lc_op4r_stmt; sg_op4t : lc_op4t_stmt; sg_op4sys : lc_op4sys_stmt;
  sg_op4coal : lc_op4coal_stmt; sg_op4find : lc_op4find_stmt; sg_op4sub : lc_op4sub_stmt;
  sg_op4st : lc_op4st_stmt; sg_op4s : lc_op4s_stmt;
  sg_op5 : lc_op5_stmt; sg_op6a : lc_op6a_stmt; sg_op6m : lc_op6m_stmt; sg_op6b : lc_op6b_stmt;
  sg_set56 : lc_set56_stmt;
  sg_op7 : lc_op7_stmt; sg_tail : lc_tail_stmt; sg_exit : lc_exit_stmt }.

(* ------------------------------------------------------------------ *)
(* 7. The composition                                                  *)
(* ------------------------------------------------------------------ *)

(* An SRr obligation whose post is "AI gives srealizes" is a srealizes. *)
Lemma lc_srz_enter : forall (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* The bounds the inductions read off the loop cuts. *)
Lemma lc_head_lt : forall cx op W c, lc_st_head cx op W c -> 0 <= lo_ops op < TC.OPS_MAX.
Proof.
intros cx op W c H. destruct H as (ly' & S' & regs' & mem' & md' & e & _ & HL & _).
destruct HL as (_ & _ & _ & _ & (_ & Hops & _) & _). exact Hops.
Qed.

Lemma lc_arm_o : forall cx op o W c, lc_st_arm cx op o W c -> 0 <= o < 9.
Proof.
intros cx op o W c H. destruct H as (ly' & S' & regs' & mem' & md' & e & _ & Ho & _).
rewrite Ho. unfold lc_opc. apply Z.mod_pos_bound. lia.
Qed.

Lemma lc_sysl_lt : forall cx op i W c, lc_st_sysl cx op i W c -> 0 <= i < 21.
Proof.
intros cx op i W c H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H).
cbv zeta in H. destruct H as (_ & _ & Hi & Hi21 & _). lia.
Qed.

Lemma lc_find_lt : forall cx op i W c, lc_st_find cx op i W c -> 0 <= i < TC.CMDS_MAX.
Proof.
intros cx op i W c H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H).
cbv zeta in H. destruct H as (_ & _ & _ & Hi & Hc & _). lia.
Qed.

Section comp.
Hypothesis SG : lc_segments.
Hypothesis HP : lp_prem.
Variable cx : lcx.
Hypothesis HB : lc_base cx.

(* The spec_system_at loop: from the head of turn i the walk reaches SYSJ. *)
Lemma lc_sys_run : forall (m : nat) (op : lop) (i : Z), i + Z.of_nat m = 21 ->
  forall W c, lc_st_sysl cx op i W c -> SRr segs W c (lc_st_sysj cx op).
Proof.
intros m op. induction m as [|m IH]; intros i Hi W c HL.
- exfalso. pose proof (lc_sysl_lt cx op i W c HL). lia.
- eapply SRr_bind; [exact (sg_op4sys SG HP cx op i W c HB HL)|].
  intros W2 c2 _ [HL2 | HJ].
  + exact (IH (i + 1) ltac:(lia) W2 c2 HL2).
  + exact (SRr_ret segs W2 c2 (lc_st_sysj cx op) HJ).
Qed.

(* The find loop: from the head of turn i the walk reaches WANT. *)
Lemma lc_find_run : forall (m : nat) (op : lop) (i : Z), i + Z.of_nat m = TC.CMDS_MAX ->
  forall W c, lc_st_find cx op i W c -> SRr segs W c (lc_st_want cx op).
Proof.
intros m op. induction m as [|m IH]; intros i Hi W c HL.
- exfalso. pose proof (lc_find_lt cx op i W c HL). lia.
- eapply SRr_bind; [exact (sg_op4find SG HP cx op i W c HB HL)|].
  intros W2 c2 _ [HL2 | HJ].
  + exact (IH (i + 1) ltac:(lia) W2 c2 HL2).
  + exact (SRr_ret segs W2 c2 (lc_st_want cx op) HJ).
Qed.

(* Op 4: from the arm to the tail. *)
Lemma lc_op4_run : forall (op : lop) W c, lc_st_arm cx op 4 W c -> SRr segs W c (lc_st_tail cx op).
Proof.
intros op W c HA.
assert (S4T : forall W4 c4, lc_st_s4 cx op W4 c4 -> SRr segs W4 c4 (lc_st_tail cx op))
  by (intros W4 c4 H4; exact (sg_op4s SG HP cx op W4 c4 HB H4)).
assert (WT : forall W5 c5, lc_st_want cx op W5 c5 -> SRr segs W5 c5 (lc_st_tail cx op)).
{ intros W5 c5 H5. eapply SRr_bind; [exact (sg_op4sub SG HP cx op W5 c5 HB H5)|].
  intros W6 c6 _ H6. eapply SRr_bind; [exact (sg_op4st SG HP cx op W6 c6 HB H6)|].
  intros W7 c7 _ H7. exact (S4T W7 c7 H7). }
assert (JT : forall W5 c5, lc_st_sysj cx op W5 c5 -> SRr segs W5 c5 (lc_st_tail cx op)).
{ intros W5 c5 H5. eapply SRr_bind; [exact (sg_op4coal SG HP cx op W5 c5 HB H5)|].
  intros W6 c6 _ [HF | HW].
  - eapply SRr_bind; [exact (lc_find_run (Z.to_nat TC.CMDS_MAX) op 0 ltac:(reflexivity) W6 c6 HF)|].
    intros W7 c7 _ H7. exact (WT W7 c7 H7).
  - exact (WT W6 c6 HW). }
eapply SRr_bind; [exact (sg_op4a SG HP cx op W c HB HA)|].
intros W1 c1 _ [HR | HT].
- eapply SRr_bind; [exact (sg_op4r SG HP cx op W1 c1 HB HR)|].
  intros W2 c2 _ H2. exact (S4T W2 c2 H2).
- eapply SRr_bind; [exact (sg_op4t SG HP cx op W1 c1 HB HT)|].
  intros W2 c2 _ [HS | HJ].
  + eapply SRr_bind; [exact (lc_sys_run 21 op 0 ltac:(reflexivity) W2 c2 HS)|].
    intros W3 c3 _ H3. exact (JT W3 c3 H3).
  + exact (JT W2 c2 HJ).
Qed.

(* Every arm reaches the tail. *)
Lemma lc_arm_run : forall (op : lop) (o : Z) W c, lc_st_arm cx op o W c -> SRr segs W c (lc_st_tail cx op).
Proof.
intros op o W c HA. pose proof (lc_arm_o cx op o W c HA) as Ho.
assert (Hc : o = 0 \/ o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
- eapply SRr_bind; [exact (sg_op0 SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. exact (sg_recv SG HP cx op W1 c1 HB H1).
- eapply SRr_bind; [exact (sg_op1 SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. exact (sg_bar1 SG HP cx op W1 c1 HB H1).
- eapply SRr_bind; [exact (sg_op2a SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. eapply SRr_bind; [exact (sg_op2b SG HP cx op W1 c1 HB H1)|].
  intros W2 c2 _ H2. exact (sg_bar2 SG HP cx op W2 c2 HB H2).
- eapply SRr_bind; [exact (sg_op3a SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. exact (sg_op3b SG HP cx op W1 c1 HB H1).
- exact (lc_op4_run op W c HA).
- eapply SRr_bind; [exact (sg_op5 SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. exact (sg_set56 SG HP cx op W1 c1 HB H1).
- eapply SRr_bind; [exact (sg_op6a SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. eapply SRr_bind; [exact (sg_op6m SG HP cx op W1 c1 HB H1)|].
  intros W2 c2 _ H2. eapply SRr_bind; [exact (sg_op6b SG HP cx op W2 c2 HB H2)|].
  intros W3 c3 _ H3. exact (sg_set56 SG HP cx op W3 c3 HB H3).
- exact (sg_op7 SG HP cx op W c HB HA).
- eapply SRr_bind; [exact (sg_op8 SG HP cx op W c HB HA)|].
  intros W1 c1 _ H1. exact (sg_recv SG HP cx op W1 c1 HB H1).
Qed.

(* The loop, by induction on the operations left (OPS_MAX - ops): from a head the walk reaches the epilogue. *)
Lemma lc_loop_run : forall (m : nat) (op : lop), lo_ops op + Z.of_nat m = TC.OPS_MAX ->
  forall W c, lc_st_head cx op W c -> SRr segs W c (lc_st_exit cx).
Proof.
intros m. induction m as [|m IH]; intros op Hm W c HH.
- exfalso. pose proof (lc_head_lt cx op W c HH). lia.
- eapply SRr_bind; [exact (sg_head SG HP cx op W c HB HH)|].
  intros W1 c1 _ (o & HA).
  eapply SRr_bind; [exact (lc_arm_run op o W1 c1 HA)|].
  intros W2 c2 _ HT.
  eapply SRr_bind; [exact (sg_tail SG HP cx op W2 c2 HB HT)|].
  intros W3 c3 _ [(op' & Hop' & HH') | HX].
  + exact (IH op' ltac:(lia) W3 c3 HH').
  + exact (SRr_ret segs W3 c3 (lc_st_exit cx) HX).
Qed.

(* From the stack malloc's return to the epilogue. *)
Lemma lc_body_run : forall W c, lc_st_sm cx W c -> SRr segs W c (lc_st_exit cx).
Proof.
intros W c HSM.
eapply SRr_bind; [exact (sg_hdr SG HP cx W c HB HSM)|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (sg_cfg SG HP cx W1 c1 HB H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (sg_minit SG HP cx W2 c2 HB H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (sg_pre SG HP cx W3 c3 HB H3)|]. intros W4 c4 _ [(op & Hop & HH) | HX].
- exact (lc_loop_run (Z.to_nat TC.OPS_MAX) op ltac:(rewrite Hop; reflexivity) W4 c4 HH).
- exact (SRr_ret segs W4 c4 (lc_st_exit cx) HX).
Qed.
End comp.

Theorem llvmf_of_segments : lc_segments -> @transport_LLVMFuzzerTestOneInput_cg_holds_stmt rc B MT XL RLO RHI.
Proof.
intros SG.
unfold transport_LLVMFuzzerTestOneInput_cg_holds_stmt.
intros HPCS HCELLS HSCFGC HRECVC HSETC HLLC HGU HGNE HROU HRNE HRLO HRHI LAWS MTL MTF SMP ASF FFL AIL HSINK HMETA
  ROB ASM2 AMEMCPY ASCFG AMEMSET ASINIT AMWAKE AWAKE ACSWC AMSET ACLOSE ASETTLE ARECV AMTICK ATICK ASTRLEN ABAR
  ASUBMIT ACRS ACLS HXL.
pose proof (mkLpPrem HPCS HCELLS HSCFGC HRECVC HSETC HLLC HGU HGNE HROU HRNE HRLO HRHI LAWS MTL MTF SMP ASF FFL AIL
  HSINK HMETA ROB ASM2 AMEMCPY ASCFG AMEMSET ASINIT AMWAKE AWAKE ACSWC AMSET ACLOSE ASETTLE ARECV AMTICK ATICK ASTRLEN
  ABAR ASUBMIT ACRS ACLS HXL) as HP.
intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
change (@LIBK TShape.transport_shape pl (m_fs md) K) with (K (YO09.LL 0 (m_fs md) [])).
eapply lc_srz_enter; [exact HAI|].
eapply (SRr_mono segs W (@cfg_at fx segs A_LLVMF regs mem md)
          (fun W' c' => exists fpos, lc_post (mkLCx fx ly S W regs mem md p n pl M fpos) W' c')).
- eapply SRr_bind; [exact (sg_entry SG HP fx ly S W regs mem md p n pl M HPRE)|].
  intros W1 c1 _ (fpos & HSM).
  set (cx := mkLCx fx ly S W regs mem md p n pl M fpos) in *.
  assert (HB : lc_base cx) by exact HPRE.
  eapply SRr_bind; [exact (lc_body_run SG HP cx HB W1 c1 HSM)|].
  intros W2 c2 _ HX.
  eapply SRr_mono; [exact (sg_exit SG HP cx W2 c2 HB HX)|].
  intros W3 c3 _ HPOST. exists fpos. exact HPOST.
- intros W' c' Hwle (fpos & HPOST) HAI'.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Hc & HQ).
  apply (HK (YO09.LL 0 (m_fs md) []) W' c' Hwle HAI').
  exists ly', S', regs', mem', md', k. exact (conj Hc HQ).
Qed.

(* ------------------------------------------------------------------ *)
(* 8. The kit lemmas the segments share (statements; each a sub-row)   *)
(* ------------------------------------------------------------------ *)

(* K1. The read-only bytes the walk reads (TRANS_RO_RD) read as the image at every cut state: the entry's
   arodata_okS covers the RELRO tables (lp_rlo, lp_rhi), and the G journal and every callee keep an image byte that is
   not in G, not an owned static (lp_ro_unowned) and not errno (lp_rom_no_errno). *)
Definition lc_rom_view_stmt : Prop :=
  lp_prem -> forall (cx : lcx) ly' S' (W' : world segs) regs' mem' md' e,
    lc_base cx -> lc_core cx ly' S' W' regs' mem' md' e -> trans_rom_view_rd W' mem'.

(* K2. trans_src_ok's read-only disjunct for the read-only ranges the walk hands a callee: build_and_receive's dst /
   src, the memcpy sources (HOST, DESK, OTHER, io, the name at +0xe3c) and the string the strlen wrapper scans
   (+0xe2c): every byte in TRANS_RO_RD, the shadow facts (trans_sh_any, LLVMFuzzerTestOneInput_st.v lc_sh_any) and
   decode_rd_ok at the call state (the bytes from K1, amem_range, the bounds). The list is st.v lc_ro_ranges. *)
Definition lc_src_ro_stmt : Prop :=
  lp_prem -> forall (cx : lcx) ly' S' (W' : world segs) regs' mem' md' e (q n : Z),
    lc_base cx -> lc_core cx ly' S' W' regs' mem' md' e ->
    In (q, n) [(TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_OTHER, 6); (TRANS_DESK2, 6);
               (TRANS_NOTDD, 6); (TRANS_STR_C24, 8); (TRANS_STR_C24, 9); (TRANS_STR_PC, 8); (TRANS_STR_PC, 9);
               (TRANS_STR4, 5); (TRANS_STR4, 6); (TRANS_IO, 32)] ->
    trans_src_ok B ly' S' W' mem' q n.

(* K3. The strlen wrapper's facts at op 2's call (+0xe2c) for x = NAME[name], k = 8, 8 or 5: first_byte (the string's
   bytes and its NUL, from the image through K1), the rest of the NUL's 8-byte word visible, and aro_unowned (the
   slot's arodata_okS kept across the calls). *)
Definition lc_strlen_facts_stmt : Prop :=
  lp_prem -> forall (cx : lcx) ly' S' (W' : world segs) regs' mem' md' e (nm : Z),
    lc_base cx -> lc_core cx ly' S' W' regs' mem' md' e ->
    let x := lc_name_a nm in
    let k := Z.of_nat (length (nth (Z.to_nat (nm mod 3)) TOP.op_announce_NAME [])) in
    first_byte segs W' mem' x (k + 1) 0 k /\
    (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W') mem' a <> None) /\
    aro_unowned segs B (aview segs (w_H W') mem').

(* K4. The model's prologue (TOps.v LLVMFuzzerTestOneInput_m up to diginet_session_init) answers SPEC_OK at a world
   where TSim/Agree.v agree timg_B 0 holds. It follows from the computation of InitOk.v prologue_ok's proof, not from
   its statement: prologue_ok hides the world behind exists B0, and its loop equation fixes neither B0 nor the code
   (both sides can be None). The sub-row replays that script at this goal under prologue_ok's own premises
   (timg_ok timg_B: LLVMFuzzerTestOneInput_sat.v lc_timg_B_ok; any world of W_LEN bytes; length D < FUZZ_INPUT_MAX);
   LLVMFuzzerTestOneInput_st.v lc_pro_eq makes lc_pro_m TOps.v's prologue. PRE takes QueueFacts.fuzz_in_ok D
   (prologue_cursor D) from prologue_ok's third conjunct. *)
Definition lc_pro_agree_stmt : Prop :=
  forall (Bw0 D : list byte), length Bw0 = Z.to_nat TW.W_LEN -> Z.of_nat (length D) < TOP.FUZZ_INPUT_MAX ->
    exists B25, lc_pro_m timg_B Bw0 D = Some (B25, DSpec.SPEC_OK) /\ AG.agree timg_B 0 B25.

(* K5. receive's run invariant (3) (receive_cg.v recv_dn_each) at a world where the simulation invariant holds, for
   the bytes RECV, BAR1 and BAR2 hand receive (the call world is lo_B op at all three): TSim/RxOpLib.v rxop_begin,
   TSim/RxData.v rxdata_mtail_ok (OW.dn's body at tf_addr + 30 with the frame's body length) and, on the by-poll path,
   rxop_pre_g_poll, rxop_drain_step and rxop_poll_ok against diginet_session_poll_cg.v poll_rx_each. rxop_poll_ok's
   statement does not carry poll_dn_in at each hand-over: the sub-row reopens its proof there, as image A's
   LLVMFuzzerTestOneInput_kit_dn_each.v does at timg_A. *)
Definition lc_dn_each_stmt : Prop :=
  forall (ops : Z) (Bw bytes : list byte) (bp pf : Z),
    AG.agree timg_B ops Bw -> 0 <= ops < TC.OPS_MAX -> (bp = 0 \/ bp = 1) -> 0 <= pf < 256 ->
    Z.of_nat (length bytes) <= 65535 -> recv_dn_each timg_B Bw bytes bp pf.

(* K6. The run invariants and g_fail_next <= 1 that receive, build_and_receive (and, in part, diginet_session_tick,
   diginet_session_wake and diginet_session_close) ask, at a world where the simulation invariant holds (the statement's
   header (1), (2), (4), (5): Agree.v b8_on01 / b8_frames, d2_cmd, d3_ncmd, a1_max_cmds / a1_max_body, e1_fail_next;
   TickTakeQ.v tt_sq_ok; Deadline.v queued_le; TickTakeW.v tk_cfg_max_cmds / tk_cfg_max_body) (any ops: d3_ops bounds
   it by OPS_MAX = CMDS_MAX, so it also serves settle's (2) at an operation's end world, agree timg_B (ops + 1)). *)
Definition lc_runinv_stmt : Prop :=
  forall (ops : Z) (Bw : list byte), AG.agree timg_B ops Bw ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) /\
    TW.S_queued Bw <= TC.QUEUE_MAX /\
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
    TW.g_ncmd Bw <= TC.CMDS_MAX /\ 1 <= TW.S_cfg_max_cmds Bw /\ 1 <= TW.S_cfg_max_body Bw /\
    TW.g_fail_next Bw <= 1.

(* K7. The frame-pointer chain at a call from a loop cut: s0 = sp0, whose record is [RA_LLVMF, the driver's s0]
   (lc_saved), and the entry chain [] (the slot's afn_pre), kept above sp0 by the journal. Its spine is [] (sp0 within
   16 bytes of ly_top) or [RA_LLVMF], so raZ :: spine ch is in CTX_receive / CTX_build_and_receive for the return
   addresses LLVMF_RA_RECV / LLVMF_RA_BAR. *)
Definition lc_chain_stmt : Prop :=
  lp_prem -> forall (cx : lcx) ly' S' (W' : world segs) regs' mem' md' e,
    lc_base cx -> lc_core cx ly' S' W' regs' mem' md' e ->
    exists ch, @achain rc ly' (aview segs (w_H W') mem') (lc_sp1 cx) (lc_sp0 cx) ch /\
      (spine ch = [] \/ spine ch = [RA_LLVMF]).

End seg.
