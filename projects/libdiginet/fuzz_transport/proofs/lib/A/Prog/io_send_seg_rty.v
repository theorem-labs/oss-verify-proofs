(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 830 of its 891 lines of code are new or changed and 1078 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_fly.v, with its module paths and module names changed; 578 of its 667 lines of code are new or changed and 802 lines of the source are left out. *)
(* io_send_seg_rty: the retry arm of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the frozen statement is lib/A/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), 0x830f0 .. 0x83120 = transport_text + IOS_AT 0x390 .. + 0x3c0.

   The code (io_send_cg.v header lines 112-114), with sp = the walk's sp (the entry sp less IOSEND_FRAME = 160) and
   M = TA_M:
     0x830f0 - 0x830fc  a2 = sp + 8, a0 = s1 (p), a1 = s0 (len); `jal` check_inflight_retry (transport_sigma
                        TS_check_inflight_retry) at 0x830fc, return address 0x83100 = transport_text + IOS_AT 0x3a0;
     0x83100 - 0x8311c  a0 = M; a1 = the 4-byte load of M.fly.retries (M + 108), sign-extended; a2 = the 8-byte load
                        of g_now; a1 = a1 + 1; the 4-byte store of a1 at M + 108; the 8-byte store of a2 at M + 112
                        (M.fly.sent);
     0x83120            `j` 0x83384 = transport_text + IOS_EPI.

   The segment is ios_rty_arm, in continuation form: from io_send_seg_e2.v's cut ios_e2_at at the world ios_B0 Bw
   (the state ios_e2_head hands its f.retry <> 0 exit) to the same cut at the world the retry arm leaves,
   Bw' = set_M_fly_sent (set_M_fly_retries B0 (u32 (M_fly_retries B0 + 1))) (g_now B0) with B0 = ios_B0 Bw
   (io_send_segs.v ios_arm_retry). It is proved in three steps:
     the call setup     one run of DgnTransportPaLib.v paj_run_tok over io_send_seg_e2.v ios_e2_state with no write
                        window (io_send_seg_e2.v ios_e2_stop_cir: it stops at the jal); the cut is carried to the
                        call's memory by io_send_seg_e2.v ios_e2_keep;
     the call           the DONOR call of check_inflight_retry through TransportGCg.v gx_call_cg with the contract
                        check_inflight_retry_cg.v transport_check_inflight_retry_cg, its post read by
                        DgnTransportCg.v decode_cg_post_dcg, as io_send_seg_csf.v calls check_sent_frame. Its
                        premises are the cut's (the frame and the struct spec_frame f at sp + 8, the world relation at
                        B0), the window (CIR_STK below sp - 160), the model call check_inflight_retry_m B0 frame
                        (ios_arm_retry) and M_fly_len B0 <= SPEC_MAX_FRAME: io_send_seg_cut.v ios_fix's guarded bound
                        on Bw, whose guard M_fly_on Bw <> 0 the model call's first test gives, with M_fly_on and
                        M_fly_len of B0 those of Bw (B0 differs from Bw only at g_fail_next's byte, world offset
                        0xfdc8; M.fly.on is at 0x60 and M.fly.len at 0x668). After it: the journal, the running
                        acall_kept_g by TransportGCg.v dk_kept_trans_nf_g, the frame by io_send_seg_src.v
                        ios_src_ok_acall_g (60 <= len: io_send_seg_frm.v ios_len60), the saved words and the struct
                        (above the callee's window), the world by gx_kept and TWorldG.v tw_kept;
     the tail           one run of paj_run_to_tok over ios_e2_state with the fly write window (io_send_seg_e2.v
                        ios_e2_stop_retry); the two stored values are read back from the chunks of the run's last
                        state (M + 112: g_now; M + 108: the sign-extended M.fly.retries plus 1, whose four low bytes
                        are u32 (M_fly_retries B0 + 1)), the world is two io_send_seg_world.v ios_tw_step at the M row
                        of TWorldA.v TMAP_A, and the running kept fact grows by the 12 stored bytes, which are bytes
                        of G and of iosend_wr (io_send_seg_world.v ios_wr_fly_retries / ios_wr_fly_sent). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA DgnTransportLeafb CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src io_send_seg_csf
  io_send_seg_fly io_send_seg_e2.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_frame_cg check_latest_control_cg check_state_wake_cg check_inflight_new_cg check_latest_frame_cg
  check_keepalive_due_cg check_latest_display_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_control_cg.
Module LAF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_frame_cg.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_cg.
Module LKD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_due_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_display_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model side                                                      *)
(* ------------------------------------------------------------------ *)

Lemma rty_len_B : forall T rd Bw, tw_at T rd Bw -> Z.of_nat (length Bw) = TW.W_LEN.
Proof.
  intros T rd Bw H. rewrite (tw_len T rd Bw H). rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia].
Qed.

(* ios_B0 Bw stores only g_fail_next's byte (world offset 0xfdc8): M.fly.on (0x60 .. 0x63) and M.fly.len
   (0x668 .. 0x66f) are those of Bw. *)
Lemma rty_B0_on : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_fly_on (ios_B0 Bw) = TW.M_fly_on Bw.
Proof.
  intros Bw HL. unfold ios_B0, TW.set_g_fail_next, TW.M_fly_on.
  rewrite (TWL.s32_at_upd_out Bw (TW.put 1 0))
    by (rewrite ?TWL.length_put, ?HL; try change (Z.of_nat 1) with 1;
        unfold TW.A_M_fly_on, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN; lia).
  reflexivity.
Qed.

Lemma rty_B0_len : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_fly_len (ios_B0 Bw) = TW.M_fly_len Bw.
Proof.
  intros Bw HL. unfold ios_B0, TW.set_g_fail_next, TW.M_fly_len.
  rewrite (TWL.u_at_upd_out Bw (TW.put 1 0))
    by (rewrite ?TWL.length_put, ?HL; try change (Z.of_nat 1) with 1; try change (Z.of_nat 8) with 8;
        unfold TW.A_M_fly_len, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN; lia).
  reflexivity.
Qed.

(* check_inflight_retry_m's first test (:459): no frame in flight is None. *)
Lemma rty_cir_on : forall Bx frame Bx', TC.check_inflight_retry_m Bx frame = Some (Bx', tt) -> TW.M_fly_on Bx <> 0.
Proof.
  intros Bx frame Bx' H. unfold TC.check_inflight_retry_m, TC.truth in H. cbv zeta in H.
  destruct (TW.M_fly_on Bx =? 0) eqn:E.
  - cbn [negb orb] in H. discriminate H.
  - apply Z.eqb_neq. exact E.
Qed.

(* The callee's run invariant at the world it is handed: io_send_seg_cut.v ios_fix's guarded bound, whose guard
   the model call gives. *)
Lemma rty_fly_len_bound : forall Bw frame,
  Z.of_nat (length Bw) = TW.W_LEN ->
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
  TC.check_inflight_retry_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  TW.M_fly_len (ios_B0 Bw) <= TC.SPEC_MAX_FRAME.
Proof.
  intros Bw frame HL HG HM. rewrite (rty_B0_len Bw HL). apply HG.
  rewrite <- (rty_B0_on Bw HL). exact (rty_cir_on _ _ _ HM).
Qed.

Lemma rty_truth : forall frame, ios_e2_rty frame <> 0 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = true.
Proof.
  intros frame H. unfold TC.truth. apply negb_true_iff. apply Z.eqb_neq. exact H.
Qed.

(* The four low bytes of the sign-extended M.fly.retries plus 1 are those of u32 (M.fly.retries + 1). *)
Lemma rty_le_byte_inc : forall x (j : nat),
  YO0f.le_byte (bv_swrap 32 x + 1) 4 j = YO0f.le_byte (DSpec.u32 (x + 1)) 4 j.
Proof.
  intros x j. unfold YO0f.le_byte, DSpec.u32.
  assert (E : (bv_swrap 32 x + 1) mod 2 ^ (8 * Z.of_nat 4) = (x + 1) mod 2 ^ 32 mod 2 ^ (8 * Z.of_nat 4)).
  { pose proof (ifly_swrap_mod 32 x) as Hs. change (2 ^ Z.of_N 32) with 4294967296 in Hs.
    change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ 32) with 4294967296.
    rewrite Z.mod_mod by lia. rewrite Zplus_mod, Hs, <- Zplus_mod. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* The `addi a1, a1, 1` after the sign-extending `lw` of M.fly.retries. *)
Lemma rty_den_inc : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 u + 1).
Proof.
  intros E n u Hn Hu.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff n 0))) (Z_to_bv 64 1)).
  rewrite (ifly_sext_den E n 32 4 u Hn Hu eq_refl ltac:(lia) ltac:(lia)).
  apply alu64_add_lit.
Qed.

(* The world the tail leaves: the two stores at the M row, every other payload byte unchanged. *)
Lemma rty_world : forall (Bx : list byte) (rd0 rdF : Z -> option Z),
  tw_at TMAP_A rd0 Bx ->
  (forall j, (j < 4)%nat ->
     rdF (TA_M + 108 + Z.of_nat j) = Some (YO0f.le_byte (DSpec.u32 (TW.M_fly_retries Bx + 1)) 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_M + 112 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bx) 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 108 <= x < TA_M + 112) -> ~ (TA_M + 112 <= x < TA_M + 120) ->
     rdF x = rd0 x) ->
  tw_at TMAP_A rdF
    (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx)).
Proof.
  intros Bx rd0 rdF Htw V108 V112 Hk.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  unfold TW.set_M_fly_sent, TW.set_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_retries.
  pose proof (ios_tw_start rdF rd0 Bx Htw) as H0.
  pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 108 (TW.OFF_M + 96 + 12) 4
    (DSpec.u32 (TW.M_fly_retries Bx + 1)) H0 TMAP_A_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V108) as H1.
  pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 112 (TW.OFF_M + 96 + 16) 8 (TW.g_now Bx) H1
    TMAP_A_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V112) as H2.
  apply (ios_tw_end rdF rd0 _ _ H2).
  intros x Hx HP. ios_unP HP. apply Hk; (exact Hx || lia).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state of the tail                                      *)
(* ------------------------------------------------------------------ *)

(* The tail reads and writes only M.fly.retries (M + 108, 4 bytes) and M.fly.sent (M + 112, 8) and reads g_now;
   it touches no stack cell. Atoms beyond the 32 registers: 32 M.fly.retries, 33 g_now. The M region carries the
   write window, so the engine's frame_of keeps every other byte; io_send_seg_e2.v's state cannot serve here,
   since its facts name no atom and the shadow-safety check of a write window (YCbn.v cells_safe_b) needs the
   base's value. *)
Definition rty_fly_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 108 120 108 120 [YP09.mkChunk 108 (CVal 4 (SOff 32 0))].
Definition rty_now_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition rty_regions : smem := [rty_fly_region; rty_now_region].
Definition rty_facts : facts :=
  mkFacts [(A_OBJ 8, mkAF TA_M TA_M 5); (A_OBJ 27, mkAF TA_g_now TA_g_now 5)] [] [].
Definition rty_ss (pc : Z) : sstate := mkSS pc sr_atoms rty_regions None rty_facts.
Definition RTY_SH : list shent := [].
Definition RTY_Bx : sv := SOff 20 0.

(* Where the token engine stops: M.fly.retries + 1 and M.fly.sent = g_now, then the `j` to the epilogue. *)
Definition rty_run_to (stop pc : Z) :=
  let ss := rty_ss pc in
  let K := run_K A_LIM RTY_Bx RTY_SH ss in
  match sym_run_toN_pi_tok transport_tpi transport_tw K RTY_Bx YC4b.Bspan RTY_SH FUEL stop ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.

Lemma rty_stop : rty_run_to IOS_EPI (IOS_AT 0x3a0) = (IOS_EPI, PTS_running).
Proof. vm_compute. reflexivity. Qed.

(* The w bytes of chunk c of region idx of the state HS, read through the view (io_send_seg_fly.v ifly_chunk). *)
Ltac rty_chunk HS idx c UB wn v tac V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in let Hden := fresh "Hden" in
  pose proof (YC4b.st_ok_region_nth _ _ _ idx _ HS eq_refl) as RG;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (ifly_Forall_nth _ _ c _ HC eq_refl) as HC1;
  lazymatch type of HC1 with
  | YP09.chunk_ok _ ?Ex _ _ (YP09.mkChunk _ (CVal ?wN ?e)) =>
      assert (Hden : sv_denot Ex e = Z_to_bv 64 v) by tac;
      pose proof (ifly_chunk_rd _ _ _ _ _ wN wn _ v eq_refl ltac:(lia) HC1 Hden) as V
  end;
  clear HC HC1 Hden.

Section rty. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The return address of the call is the cut IOS_AT 0x3a0. *)
Lemma rty_pc : Z_to_bv 64 (BASE + 7836) = w64 (transport_text + IOS_AT 0x3a0).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The walk's valuation at the cut of the tail: the registers, M.fly.retries and g_now. *)
Definition rty_E (regs : bvmap 5 word) (flyr now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 flyr; Z_to_bv 64 now]).

Lemma rty_agree : forall regs flyr now,
  env_agree 32 (Ereg regs [Z_to_bv 64 flyr; Z_to_bv 64 now]) (rty_E regs flyr now).
Proof.
  intros. split; [intros n Hn; unfold rty_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The state the token engine runs the tail from: M.fly.retries (readable, and writable: a byte of G) and
   g_now (read only). *)
Lemma rty_entry : forall (W : world segs) (regs : bvmap 5 word) mem (flyr now : Z),
  0 <= flyr < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_M + 108) 4 flyr ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_g_now + 0) 8 now ->
  st_ok_pi segs VAL (rty_E regs flyr now) (rty_ss (IOS_AT 0x3a0))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_AT 0x3a0)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs RTY_Bx RTY_SH (rty_E regs flyr now) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem flyr now Hflyr Hnow V108 Vnow.
  assert (EM : TA_M = 6156640) by reflexivity. assert (EN : TA_g_now = 6156544) by reflexivity.
  set (E := rty_E regs flyr now).
  assert (E32 : ew E 32 = Z_to_bv 64 flyr)
    by (unfold E, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 now)
    by (unfold E, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, rty_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct ios_e2_vals as (V8 & V27 & _ & _ & _).
  assert (B8 : base_val E (Some (A_OBJ 8)) = TA_M).
  { cbn [base_val]. rewrite (EOB 8%nat ltac:(lia)), V8. apply unsigned_lit_small. lia. }
  assert (B27 : base_val E (Some (A_OBJ 27)) = TA_g_now).
  { cbn [base_val]. rewrite (EOB 27%nat ltac:(lia)), V27. apply unsigned_lit_small. lia. }
  assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TA_M) by exact B8.
  assert (U27 : bv_unsigned (ew E (A_OBJ 27)) = TA_g_now) by exact B27.
  split; [|unfold sh_ok, RTY_SH; constructor].
  rewrite restrict_mkst_fx. unfold rty_ss, rty_regions.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold rty_fly_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B8. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw).
        apply (ios_inG_row _ _ _ (TA_M + o) TMAP_A_M). unfold TW.SZ_M. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ TA_M 108 4 (SOff 32 0) flyr);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia
          | exact V108].
    + unfold rty_now_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 33 0) now);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact Vnow].
  - apply pairwise_disjoint_of_extents.
    unfold rty_fly_region, rty_now_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite B8, B27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold rty_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U27. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM, ?EN; reflexivity].
Qed.


(* ------------------------------------------------------------------ *)
(* Carrying the cut across the two stores                              *)
(* ------------------------------------------------------------------ *)

(* A stretch that writes only M + 108 .. M + 119 (bytes of M's payload, so of G, outside g_s's payload) keeps
   every memory fact of the cut but the world relation: the frame lies outside G or inside g_s's payload
   (iosend_frame_at), the struct spec_frame and the saved words lie in the machine stack, the shadow band above
   M. The world relation at the new world Bx' comes from the stretch itself. *)
Lemma rty_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx Bx',
  AR_laws segs B ->
  0 < Z.of_nat (length frame) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 108 <= a < TA_M + 120) ->
     aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  tw_at TMAP_A (aview segs (w_H W3) mem4) Bx' ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 Bx'.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx Bx' LAWS Hn0 Hfr HSP KV AT CUR RG R24 HTW4.
  destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
  assert (EF : IOSEND_FRAME = 160) by reflexivity.
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ES : SF_SIZE = 80) by reflexivity.
  assert (EM : TA_M = 6156640) by reflexivity.
  assert (EGS : TA_g_s = 6158784) by reflexivity.
  assert (SGS : TW.SZ_g_s = 18264) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof CUR3 as (HJ3 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof (proj1 HJi3) as HAR3.
  pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
                ltac:(lia)) as HPL.
  assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ (TA_M + 108 <= a < TA_M + 120)).
  { intros a Ha HW. destruct Hfr as [HnG | [HG1 HG2]].
    - apply (HnG a Ha). apply (ios_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia.
    - lia. }
  assert (KSF : forall a, spZ regs - IOSEND_FRAME + IOS_F_OFF <= a <
                          spZ regs - IOSEND_FRAME + IOS_F_OFF + SF_SIZE -> ~ (TA_M + 108 <= a < TA_M + 120))
    by (intros a Ha; lia).
  assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                  aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s)
    by (intros s Hs; apply KV; lia).
  split; [exact CUR|].
  split.
  { (* the saved words *)
    unfold ios_saved in SAVED |- *. rewrite Forall_forall in SAVED |- *. intros o Ho.
    assert (Hfo : 0 < fst o <= 72).
    { unfold IOS_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- (SAVED o Ho). apply rdword_ext. intros kk Hkk. apply KV; lia. }
  split; [exact RG|]. split; [exact R24|].
  split.
  { (* the struct *)
    destruct SFR as (Hfp0 & Hfp8 & SB & HG & HL & HR). split; [exact Hfp0|]. split; [exact Hfp8|].
    exists SB. split; [|exact (conj HL HR)].
    refine (ios_garr8_keep W3 W3 mem3 mem4 _ _ _ HG). intros j Hj. rewrite length_map in Hj.
    apply KV; [lia | apply KSF; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
            (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
            (fun a Ha => KV a ltac:(lia) (KSF a Ha)) KSH). }
  split.
  { (* the frame *)
    refine (ios_garr8_keep W3 W3 mem3 mem4 _ _ _ GARR). intros j Hj. rewrite length_map in Hj.
    apply KV; [destruct HPL as [Pl|Pl]; lia | apply KFR; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF
            (fun a Ha => KV a ltac:(destruct HPL as [Pl|Pl]; lia) (KFR a Ha)) KSH). }
  exact HTW4.
Qed.

(* ------------------------------------------------------------------ *)
(* The tail: 0x83100 .. 0x83120                                        *)
(* ------------------------------------------------------------------ *)

(* From the return of check_inflight_retry: M.fly.retries + 1 and M.fly.sent = g_now, then `j` to the epilogue. *)
Lemma ios_rty_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) (Bx : list byte)
    (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @AR rc segs B lyc Sc W memc mdc ->
  ios_e2_fix B STK sp0 regs p frame -> iosend_frame_at p (Z.of_nat (length frame)) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  (forall mem4 md4 regs4,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4
       (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx)) ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_EPI) regs4 mem4 md4) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x3a0) regs3 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc FIX Hfr AT HK.
  pose proof AT as AT0.
  destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47 & Hra & Hra4 & Hgp & Htp).
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (ios_e2_cut_vals B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
              ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & V40 & V108 & Vnow & Ve2 & Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8496) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (EM : TA_M = 6156640) by reflexivity.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
  destruct (rty_entry W3 regs3 mem3 (ios_e2_flyr Bx) (ios_e2_now Bx) Z3 Z4 V108 Vnow) as [HS SHOK].
  set (E0 := rty_E regs3 (ios_e2_flyr Bx) (ios_e2_now Bx)) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rty_E; apply Eimg_env).
  assert (X32 : ew E0 32 = Z_to_bv 64 (ios_e2_flyr Bx))
    by (unfold E0, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (X33 : ew E0 33 = Z_to_bv 64 (ios_e2_now Bx))
    by (unfold E0, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  destruct ios_e2_vals as (V8 & _ & _ & _ & _).
  assert (UM : bv_unsigned (ew E0 (A_OBJ 8)) = TA_M).
  { unfold E0, rty_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
    apply unsigned_lit_small. lia. }
  assert (UM' : bv_unsigned (ew E0 249%nat) = TA_M) by exact UM.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
                TG.G_HARNESS HGX 0 []) as RUNTO.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x3a0)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  (* the run: a0 = M, a1 = M.fly.retries (sign-extended), a2 = g_now, a1 + 1, the two stores, `j` *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_EPI.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (first
      [ apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
          rewrite UM' in Ha; apply (ios_inG_row _ _ _ a TMAP_A_M); unfold TW.SZ_M; lia |]
      | apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |] ]).
    apply awr_ok_x_nil. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 108 <= a < TA_M + 120) ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha H1.
    apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 108 <= x < TA_M + 120) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(rewrite ?UM' in Hx; lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* the registers the run keeps *)
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ios_e2_kept HS (rty_agree regs3 _ _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (R21 : YK11.getr regs3 21 = w64 (bv_unsigned (YK11.getr regs3 21)))
    by (unfold w64; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (ios_e2_regs_step regs regs3 (ms_regs ms1) p frame fail _ RG R21 R24 KR) as (RG1 & _ & R241).
  (* the two stored values, read from the last state's chunks of M.fly *)
  rty_chunk HS 0%nat 0%nat UM' 8%nat (ios_e2_now Bx)
    ltac:(cbn [sv_denot]; rewrite X33, Z.add_0_r; apply Z_to_bv_bv_unsigned) V112.
  rty_chunk HS 0%nat 1%nat UM' 4%nat (bv_swrap 32 (ios_e2_flyr Bx) + 1)
    ltac:(apply (rty_den_inc E0 32 (ios_e2_flyr Bx) X32); lia) V108'.
  (* the world *)
  assert (HTW1 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms1))
           (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx))).
  { apply (rty_world Bx (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms1)) HTW).
    - intros j Hj. rewrite <- rty_le_byte_inc. exact (V108' j Hj).
    - intros j Hj. exact (V112 j Hj).
    - intros x Hx N1 N2. pose proof (GLOW x (ios_tw_in_G x Hx)) as Hl.
      apply KV; [unfold kLowMemEnd in Hl; lia | lia]. }
  (* the running kept fact: the 12 stored bytes are bytes of G and of iosend_wr *)
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
      (fun x => TA_M + 108 <= x < TA_M + 120) LAWS HGX HARc HKEPT KV GA); [| lia | lia].
    intros a Ha. cbv beta in Ha. right. split.
    - apply (ios_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia.
    - destruct (Z_lt_le_dec a (TA_M + 112)) as [H1|H1];
        [apply ios_wr_fly_retries; lia | apply ios_wr_fly_sent; lia]. }
  assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1)
                  (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1)))
                     (TW.g_now Bx)))
    by exact (rty_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 mem3 md3 regs3 (ms_mem ms1) md4 (ms_regs ms1) Bx _
               LAWS Hn0 Hfr HSP KV AT0 CUR1 RG1 R241 HTW1).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transport_text + IOS_EPI) rg mm mdx) Q) end.
  exact (HK _ _ _ AT1).
Qed.

(* ------------------------------------------------------------------ *)
(* The retry arm: 0x830f0 .. 0x83120                                   *)
(* ------------------------------------------------------------------ *)

(* From io_send_seg_e2.v ios_e2_head's f.retry <> 0 exit (the cut at the world ios_B0 Bw, s5 = f.cmd) to the
   epilogue, at the world Bw' the dispatch leaves (io_send_segs.v ios_arm_retry). The exit continuation is
   io_send_seg_e2.v ios_e2_seg_stmt's epilogue continuation. *)
Lemma ios_rty_arm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (cmd : Z) (Bw Bw' : list byte)
    ly3 S3 (W3 : world segs) mem4 md4 (regs4 : bvmap 5 word) (Q : world segs -> config -> Prop),
  ios_e2_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
    ly3 S3 W3 mem4 md4 regs4 (ios_B0 Bw) ->
  YK11.getr regs4 21 = w64 cmd -> cmd = DSpec.sf_cmd (TC.rf frame) ->
  (cmd = TC.SPEC_CMD_E2 \/ cmd = TC.SPEC_CMD_DATA) -> ios_e2_rty frame <> 0 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  ios_arm Bw frame = Some (Bw', tt) ->
  (forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
       ly5 S5 W5 mem5 md5 regs5 Bw' ->
     SRr segs W5 (@cfg_at fx segs (transport_text + IOS_EPI) regs5 mem5 md5) Q) ->
  SRr segs W3 (@cfg_at fx segs (transport_text + IOS_AT 0x390) regs4 mem4 md4) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame cmd Bw Bw'
  ly3 S3 W3 mem4 md4 regs4 Q HL HFX AT R21 Hcmd Hc2 Hrty HM HA HK.
destruct HL as (HCELLS & LAWS & MTL & HGX & HGE & HCIR & _ & _).
destruct HFX as (HJe & Hra0 & Hra4 & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & Hoff & Hfr
  & _ & _ & HTWe & HFLY & _ & Hev).
(* the model: the call at B0 = ios_B0 Bw, its run invariant, the world the arm leaves *)
assert (LB : Z.of_nat (length Bw) = TW.W_LEN) by exact (rty_len_B _ _ _ HTWe).
assert (HCMD : DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 \/ DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA)
  by (rewrite <- Hcmd; exact Hc2).
destruct (ios_arm_retry Bw frame Bw' HA HCMD (rty_truth frame Hrty)) as [HMC EBw'].
pose proof (rty_fly_len_bound Bw frame LB HFLY HMC) as HFL.
pose proof (ios_len60 _ _ _ HM) as H60.
subst Bw'.
(* the entry journal: its AR, the stack, the layout *)
pose proof HJe as (_ & _ & (memS & HJei & _) & _). rewrite !Z.add_0_r in HJei.
pose proof HJei as (HARc & HLEc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLEc as (_ & _ & _ & _ & _ & EFc & _ & _ & _ & Eloc & Ehic & _).
clear HJei memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (CS : CIR_STK = 8240) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hn0 : 0 < Z.of_nat (length frame)) by lia.
assert (FIX : ios_e2_fix B STK sp0 regs p frame).
{ unfold ios_e2_fix.
  split; [exact Hp0|]. split; [exact Hn0|]. split; [exact Hoff|]. split; [exact Hsp16|].
  split; [exact Hlo|]. split; [exact Hhi|]. split; [lia|]. split; [lia|].
  split; [exact Hra0|]. split; [exact Hra4|]. split; [exact Hgp | exact Htp]. }
(* the tail, from the return of the call *)
assert (KT : forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
   ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
     ly5 S5 W5 mem5 md5 regs5 (ios_B0 Bw) ->
   SRr segs W5 (@cfg_at fx segs (transport_text + IOS_AT 0x3a0) regs5 mem5 md5) Q).
{ intros ly5 S5 W5 mem5 md5 regs5 AT5.
  exact (ios_rty_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame (TW.g_fail_next Bw)
           ly5 S5 W5 mem5 md5 regs5 (ios_B0 Bw) Q LAWS HGX HARc FIX Hfr AT5 (HK ly5 S5 W5)). }
clear HK.
(* the cut *)
pose proof AT as AT0.
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
destruct (ios_e2_cut_vals B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame
            (TW.g_fail_next Bw) ly3 S3 W3 mem4 md4 regs4 (ios_B0 Bw) AT0)
  as (V38 & V40 & V108 & Vnow & Ve2 & Z1 & Z2 & Z3 & Z4 & Z5).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HJ as (_ & _ & (memS & HJ2i & _) & _). rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _).
destruct HLE2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJ2i memS.
(* the call setup, 0x830f0 .. 0x830fc: a2 = sp + 8, a0 = p, a1 = len, `jal check_inflight_retry` *)
pose proof (ios_e2_state false false false (IOS_AT 0x390) (spZ regs - IOSEND_FRAME)
              (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr (ios_B0 Bw)) (ios_e2_now (ios_B0 Bw))
              (ios_e2_e2v (ios_B0 Bw))
              W3 regs4 mem4 R2 ltac:(lia) ltac:(lia) Z1 Z2 Z3 Z4 Z5 V38 V40 V108 Vnow Ve2) as HS.
set (E0 := ios_e2_E regs4 (ios_e2_rty frame) (ios_e2_snd frame) (ios_e2_flyr (ios_B0 Bw))
             (ios_e2_now (ios_B0 Bw)) (ios_e2_e2v (ios_B0 Bw))) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ios_e2_E; apply Eimg_env).
assert (SHOK : sh_ok segs ios_e2_Bx [] E0 (mrestrict (w_H W3) mem4)) by apply Forall_nil.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs4 r)
  by (intros n r Hn; unfold E0, ios_e2_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 160)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, IOSEND_FRAME; apply unsigned_lit_small; lia).
assert (ERA : BASE + 7836 = 536832) by (vm_compute; reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
              TG.G_HARNESS HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + IOS_AT 0x390)) mem4
    (YK11.seg_rom segs)) md4) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
rename ms into msT.
assert (KV : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W3) (ms_mem msT) a = aview segs (w_H W3) mem4 a).
{ intros a Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. cbv beta. ics_win Hin Hx ltac:(lia). }
assert (GA : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msT) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                 ly3 S3 W3 (ms_mem msT) md5).
{ unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
  apply (ics_kept_step B TG.G_HARNESS lyc Sc W memc mdc W3 mem4 (ms_mem msT)
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
    LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) ltac:(lia) ltac:(lia)). }
pose proof CUR1 as (_ & _ & _ & _ & HKEPT1).
pose proof (regs_kept_of_st_ok _ E0 _ _ regs4 _ ios_e2_kept HS (ios_e2_agree regs4 _ _ _ _ _)
              ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
destruct (ios_e2_regs_step regs regs4 (ms_regs msT) p frame (TW.g_fail_next Bw) cmd RG R21 R24 KR)
  as (RG1 & R211 & R241).
assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame
                (TW.g_fail_next Bw) ly3 S3 W3 (ms_mem msT) md5 (ms_regs msT) (ios_B0 Bw)).
{ apply (ios_e2_keep B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
           ly3 S3 W3 mem4 md4 regs4 W3 (ms_mem msT) md5 (ms_regs msT) (ios_B0 Bw)
           (spZ regs - IOSEND_FRAME) (spZ regs - IOSEND_FRAME)
           LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(intros a Ha _; exact (KV a Ha)) AT0 CUR1 RG1 R241). }
destruct AT1 as (_ & SAVED1 & _ & _ & SFR1 & _ & GARR1 & SRCF1 & HTW1).
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) in SFR1 by (unfold IOS_F_OFF; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
(* the registers at the call *)
pmkst HS.
ics_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
ics_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length frame))) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
ics_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (spZ regs - 152)) Q12 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 7836)) RA ltac:(apply codeptr_val; exact HEI).
ics_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
ics_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
assert (ESP : bv_unsigned (YK11.getr (ms_regs msT) (Z_to_bv 5 2)) = spZ regs - 160)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs msT) = spZ regs - 160) by exact ESP.
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + 7836)))
  by (apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]).
(* 0x830fc: check_inflight_retry, through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_check_inflight_retry)) mm rom)
    mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3
    (ms_mem msT) md5 (k + 0) _ (ms_regs msT) CIR_STK CIR_EV 0 (fun _ => False)
    (fun _ _ _ => ios_B0 Bw = ios_B0 Bw) HGX HGE HJ).
  intros memS HJd.
  eapply SRr_mono.
  { apply (HCIR fx STK sp0 FP ly S W0 memS md0 own ly3 S3 W3 (ms_mem msT) md5 (k + 0) (ms_regs msT)
      p (spZ regs - 152) frame (ios_B0 Bw) (ios_B0 Bw) HJd).
    - exact (eq_ind_r (fun w => YK0s.ret_ok w) RAok RA).
    - unfold raZ. rewrite RA, ERA, unsigned_lit_small by lia. lia.
    - exact Q3.
    - exact Q4.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - rewrite Hsp1. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hsp16.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hp0.
    - exact GARR1.
    - exact SRCF1.
    - unfold decode_off_win in *. rewrite Hsp1. lia.
    - exact SFR1.
    - exact (ics_sf_src B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem msT) md5 (k + 0)
        (spZ regs - 152) HJ ltac:(lia) ltac:(lia)).
    - unfold decode_off_win. right. rewrite Hsp1. lia.
    - exact HTW1.
    - exact HMC.
    - exact HFL.
    - unfold CIR_EV, IOSEND_EV in *. lia. }
  cbv beta. intros W5 c5 _ H5. apply decode_cg_post_dcg. exact H5. }
cbv beta.
intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md6 & e & -> & He & HJ5 & HP5 & HFR5 & HPM5 & HK5 & HMO5 & (_ & HGK5)).
assert (Ee : e = 0) by (unfold CIR_EV in He; lia). subst e.
replace (k + 0 + 0) with (k + 0) in HJ5 by lia.
(* the journal at the return *)
pose proof HJ5 as (_ & _ & (memS & HJ5i & _) & _). rewrite !Z.add_0_r in HJ5i.
pose proof HJ5i as (HAR5 & HLE5 & _).
destruct HLE5 as (_ & _ & _ & _ & _ & EF5 & _ & _ & _ & Elo5 & Ehi5 & _).
clear HJ5i memS.
pose proof HK5 as (K51 & _).
(* the frame across the callee *)
destruct (ios_src_ok_acall_g B LAWS ly3 S3 W3 (ms_mem msT) md5 ly5 S5 W5 mem5 md6
  (spZ (ms_regs msT) - CIR_STK) (spZ (ms_regs msT)) (fun _ => False) p (Z.of_nat (length frame))
  HART HAR5 HPM5 HFR5 ltac:(intros cid pos; unfold frame_addr; rewrite EF5, EF2; reflexivity)
  ltac:(rewrite Elo5, Elo2; reflexivity) ltac:(rewrite Ehi5, Ehi2; reflexivity)
  HK5 HGK5 ltac:(intros a _ Hf; exact Hf) ltac:(intros a _ Hf; exact Hf)
  ltac:(unfold decode_off_win in Hoff; rewrite Hsp1; lia) SRCF1 H60) as [HSRC5 KF5].
assert (HGA5 : garr8 segs (mrestrict (w_H W5) mem5) p (map DSpec.bz frame)).
{ apply (ics_garr8_xw (w_H W3) (w_H W5) (ms_mem msT) mem5 p _ GARR1). intros a Ha.
  rewrite length_map in Ha. exact (KF5 a Ha). }
(* the running kept fact *)
assert (HK6 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W5 mem5 (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly3 S3 W memc W3 (ms_mem msT) W5 mem5
    (spZ regs - IOSEND_STK) (spZ regs) (spZ (ms_regs msT) - CIR_STK) (spZ (ms_regs msT))
    (iosend_wr (Z.of_nat (length frame))) (fun _ => False) (fun _ => False)).
  - lia.
  - lia.
  - intros cid pos. unfold frame_addr. rewrite EF2, EFc. reflexivity.
  - intros f Hf. rewrite HFR. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym HPM) Hbm).
  - intros b m i _ _ Hf. exact Hf.
  - intros cid pos a _ _ Hf. exact Hf.
  - exact HKEPT1.
  - exact HK5.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - intros a Hf. destruct Hf. }
(* the saved words, the struct, the world *)
assert (HSV5 : ios_saved W5 mem5 regs).
{ unfold ios_saved in *. rewrite Forall_forall in SAVED1 |- *. intros o Ho. rewrite <- (SAVED1 o Ho).
  assert (Hd : 8 <= fst o <= 72)
    by (unfold IOS_SAVED in Ho; cbn [In] in Ho;
        repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]); destruct Ho).
  apply rdword_ext. intros j Hj.
  rewrite K51 by (rewrite ?Hsp1; lia). reflexivity. }
assert (HSF5 : trans_sframe_at W5 mem5 (spZ regs - 152) p (TC.rf frame)).
{ eapply (ics_sframe_xw W3 W5 (ms_mem msT) mem5); [|exact SFR1].
  intros a Ha. apply K51; [lia | rewrite Hsp1; lia]. }
assert (HTW5 : tw_at TMAP_A (aview segs (w_H W5) mem5) (ios_B0 Bw)).
{ apply (tw_kept TMAP_A _ _ _ HTW1). intros x Hx. exact (HGK5 x (ics_tw_in_G x Hx)). }
(* the registers *)
assert (HR5 : ios_regs regs regs5 p frame (TW.g_fail_next Bw)) by exact (ics_regs_pres _ _ _ _ _ _ RG1 HP5).
pose proof (ics_s811 regs (ms_regs msT) regs5 R241 HP5) as H8115.
assert (HCUR5 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly5 S5 W5 mem5 md6).
{ unfold ios_cur. split; [exact HJ5|]. split; [rewrite HFR5; exact HFR|].
  split; [exact (Permutation_trans HPM5 HPM)|].
  split; [exact (mo_le_trans MT MTL Sc S3 S5 0 0 HMO HMO5) | exact HK6]. }
(* the cut at the return, and the tail *)
rewrite RA, rty_pc.
specialize (KT ly5 S5 W5 mem5 md6 regs5). unfold cfg_at in KT. apply KT.
unfold ios_e2_at.
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) by (unfold IOS_F_OFF; lia).
split; [exact HCUR5|]. split; [exact HSV5|]. split; [exact HR5|]. split; [exact H8115|].
split; [exact HSF5|].
split; [exact (ics_sf_src B STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md6 (k + 0) (spZ regs - 152) HJ5
          ltac:(lia) ltac:(lia))|].
split; [exact HGA5|]. split; [exact HSRC5 | exact HTW5].
Qed.

End rty.
