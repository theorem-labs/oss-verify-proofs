(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module names and numbers changed; 1131 of its 1216 lines of code are new or changed and 993 lines of the source are left out. *)
(* m_rx_seg_annt: two segment lemmas of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v; listing lib/A/Prog/DgnTransportList.v after AF_m_rx). Each is `K (successor cuts) ->
   K (its cut)`: from a machine the cut describes, symbolic runs over the inner G journal (TransportGRunA.v paj_run_x /
   paj_run_to_x) reach a successor cut, whose mrx_at is built with the kit's mrx_at_intro.

   mrx_seg_e0w, the cut E0W (0x84dec .. 0x84e04; model EPI.mrx_e0w). Regions: M.state (s3 + 12) and
   g_cfg.auto_wake (object 50), read-only, holding the world's bytes. `bnez M.state` goes to the cut TICK
   (mrx_e0w leaves the world); `beqz auto_wake` goes to TICK; else the cut WAKE (m_wake_m). Nothing is stored.

   mrx_seg_annt, the cut ANNT (0x84da8 .. 0x84e48; model EPI.mrx_ann_tail, split by annt_model / annt_e0 / annt_e1).
     run 1 (+0x51c .. +0x538)  s1 = &OW, the stores of OW.desk + 1 and OW.desk_off (= s4), a0 = s0 = fa + 30, the call:
                               the world relation at annt_B2 (mrx_tw_step); the frame is apart from the stores
                               (mrx_apart, annt_wr), so its bytes, decode_rd_ok and the read-only view are kept.
     desk_named (+0x538)       a donor-form callee through TransportGCg.v gx_call_cg: garr8 of the body (the frame's
                               suffix from fa + 30), trans_src_ok (the frame's, at the cut's call state, a sub-range),
                               decode_off_win at DNAMED_STK below sp1 - 144 (MRX_STK = 144 + DNAMED_STK). Its post
                               keeps every byte of G (gx_kept: the world relation at annt_B2) and every byte above its
                               window (the saved slots).
     run 2 (+0x53c ..)         a fresh state at the return (annt_entry2): OW.desk_p (a0 = dp) and OW.desk_body
                               stored, then cmd e0: M.foreign = 0, the old M.state (s7) = S_ONLINE: a0 = 3 and the
                               cut E0L, else the cut E0W; cmd e1, off >= 0: M.e1_us = 1, M.foreign = 0, the cut MO;
                               off < 0: M.foreign = 1, OW.foreign + 1, M.state - 1 > 1 (unsigned): the cut TICK, else
                               a0 = 5 and the cut LOST.
   The world at each cut is one TWorld.upd per store (annt_w_e0 / annt_w_mo / annt_w_neg); a field of a region the
   path did not store keeps the chunk it started with (annt_keep4). No instrumented check is on these paths. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f YK1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma annt_vals : VAL (A_OBJ 12) = TA_OW /\ VAL (A_OBJ 50) = TA_g_cfg + 16 /\ VAL (A_OBJ 8) = TA_M /\
  BASE + AF_m_rx = transport_sigma TS_m_rx /\ BASE + AF_desk_named = transport_sigma TS_desk_named.
Proof. vm_compute. repeat split. Qed.

(* ---- E0W ---- *)
Definition e0w_M : YP09.region := YP09.mkRegion (Some 19%nat) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 33 0))].
Definition e0w_aw : YP09.region := YP09.mkRegion (Some (A_OBJ 50)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 34 0))].
Definition e0w_facts : facts :=
  mkFacts [(19%nat, mkAF TA_M TA_M 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_e0w : sstate := mkSS (AF_m_rx + OFF_E0W) sr_atoms [e0w_M; e0w_aw] None e0w_facts.
Definition ANNT_SH : list shent := [].
Definition ANNT_Bx : sv := SOff 32 0.
Definition e0w_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport)
    (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_Cfg_auto_wake 4)]).

(* The entry state of E0W: M.state and g_cfg.auto_wake hold the world's bytes; s3 = &M. *)
Lemma e0w_entry : forall (Wc : world tfibsegs) regs mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H Wc) mem) Bw ->
  YK11.getr regs 19 = w64 TA_M ->
  st_ok_pi tfibsegs VAL (e0w_E regs Bw) ss_e0w
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_E0W))) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw Htw H19.
  destruct annt_vals as (V12 & V50 & V8 & _).
  set (E := e0w_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, e0w_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (E19 : ew E 19 = Z_to_bv 64 TA_M)
    by (unfold E, e0w_E; rewrite (ew_Eimg_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
  assert (B19 : base_val E (Some 19%nat) = TA_M) by (apply VB; [exact E19 | unfold TA_M; lia]).
  assert (U19 : bv_unsigned (ew E 19) = TA_M) by exact B19.
  assert (B50 : base_val E (Some (A_OBJ 50)) = TA_g_cfg + 16)
    by (apply VB; [rewrite (EOB 50%nat ltac:(lia)), V50; reflexivity | unfold TA_g_cfg; lia]).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
    nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_Cfg_auto_wake 4)]
      (Z_to_bv 64 0))
    by (intros j Hj; unfold E, e0w_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R33. pose proof (TWL.u_at_range Bw TW.A_Cfg_auto_wake 4) as R34.
  change (8 * Z.of_nat 4) with 32 in R33, R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_e0w.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold e0w_M, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B19.
      split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TA_M 12 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok Htw TMAP_A_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold e0w_aw, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B50.
      split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (TA_g_cfg + 16) 0 4 (SOff 34 0) (TW.u_at Bw TW.A_Cfg_auto_wake 4));
        [apply DEN; [exact E34 | lia] | exact R34 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 16 4 TMAP_A_ok Htw TMAP_A_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - unfold e0w_M, e0w_aw.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B19, B50.
    unfold TA_M, TA_g_cfg. repeat split; lia.
  - unfold e0w_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, E32, E33, E34.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_Cfg_auto_wake 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* ---- ANNT ---- *)
(* A byte of M's or OW's payload is a byte of G. *)
Lemma annt_inG : forall a, (TA_M <= a < TA_M + 1648) \/ (TA_OW <= a < TA_OW + 304) -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TA_OW, TW.SZ_OW). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* Atoms of run 1: 0 .. 31 the registers at the cut, 32 the shadow base, 33 the 4 bytes of OW.desk. Regions:
   OW.desk (OW + 0xd0) and OW.desk_off (OW + 0xe8), writable bytes of G, based at object 12 (the code's s1). *)
Definition annt_r_desk : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) 0xd0 0xd4 0xd0 0xd4 [YP09.mkChunk 0xd0 (YP09.CVal 4 (SOff 33 0))].
Definition annt_r_off : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0xe8 0xec 0xe8 0xec [].
Definition annt_facts1 : facts :=
  mkFacts [(A_OBJ 12, mkAF TA_OW TA_OW 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_annt : sstate := mkSS (AF_m_rx + OFF_ANNT) sr_atoms [annt_r_desk; annt_r_off] None annt_facts1.
Definition annt_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_desk 4)]).

Lemma annt_entry : forall (Wc : world tfibsegs) regs mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H Wc) mem) Bw ->
  st_ok_pi tfibsegs VAL (annt_E regs Bw) ss_annt
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_ANNT))) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw Htw.
  destruct annt_vals as (V12 & _).
  set (E := annt_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, annt_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B12 : base_val E (Some (A_OBJ 12)) = TA_OW)
    by (apply VB; [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | unfold TA_OW; lia]).
  assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = TA_OW) by exact B12.
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) =
    nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_desk 4)] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, annt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth] in E32, E33.
  pose proof (TWL.u_at_range Bw TW.A_OW_desk 4) as R33.
  change (8 * Z.of_nat 4) with 32 in R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_annt.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold annt_r_desk, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B12.
      split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw); apply annt_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TA_OW 0xd0 4 (SOff 33 0) (TW.u_at Bw TW.A_OW_desk 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 0xd0 4 TMAP_A_ok Htw TMAP_A_OW
        ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold annt_r_off, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B12.
      split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw); apply annt_inG; lia|].
      apply Forall_nil.
  - unfold annt_r_desk, annt_r_off.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B12.
    unfold TA_OW. repeat split; lia.
  - unfold annt_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U12, E32, E33.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_OW_desk 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* After desk_named, at its return address +0x53c: a fresh state. Atoms: 0 .. 31 the registers at the return,
   32 the shadow base, 33 .. 35 the 4 bytes of OW.foreign, M.e1_us and M.foreign. Regions (writable bytes of G):
   OW.foreign (OW + 0xd4), OW.desk_p and OW.desk_body (OW + 0xf0 .. 0x100), based at s1 (atom 9); M.e1_us and
   M.foreign (M + 0x14 .. 0x1c), based at s3 (atom 19). A byte a path does not store keeps its chunk. *)
Definition annt_r_fo : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xd4 0xd8 0xd4 0xd8 [YP09.mkChunk 0xd4 (YP09.CVal 4 (SOff 33 0))].
Definition annt_r_dp : YP09.region := YP09.mkRegion (Some 9%nat) 0xf0 0x100 0xf0 0x100 [].
Definition annt_r_m : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0x14 0x1c 0x14 0x1c
    [YP09.mkChunk 0x14 (YP09.CVal 4 (SOff 34 0)); YP09.mkChunk 0x18 (YP09.CVal 4 (SOff 35 0))].
Definition annt_facts2 : facts :=
  mkFacts [(9%nat, mkAF TA_OW TA_OW 5); (19%nat, mkAF TA_M TA_M 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ANNT_RET : Z := AF_m_rx + 0x53c.
Definition ss_annt2 : sstate := mkSS ANNT_RET sr_atoms [annt_r_fo; annt_r_dp; annt_r_m] None annt_facts2.
Definition annt_E2 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport)
    (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_foreign 4);
                Z_to_bv 64 (TW.u_at Bw TW.A_M_e1_us 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_foreign 4)]).

Lemma annt_entry2 : forall (Wc : world tfibsegs) regs mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H Wc) mem) Bw ->
  YK11.getr regs 9 = w64 TA_OW -> YK11.getr regs 19 = w64 TA_M ->
  st_ok_pi tfibsegs VAL (annt_E2 regs Bw) ss_annt2
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ANNT_RET)) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw Htw H9 H19.
  set (E := annt_E2 regs Bw).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (E9 : ew E 9 = Z_to_bv 64 TA_OW)
    by (unfold E, annt_E2; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E19 : ew E 19 = Z_to_bv 64 TA_M)
    by (unfold E, annt_E2; rewrite (ew_Eimg_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
  assert (B9 : base_val E (Some 9%nat) = TA_OW) by (apply VB; [exact E9 | unfold TA_OW; lia]).
  assert (B19 : base_val E (Some 19%nat) = TA_M) by (apply VB; [exact E19 | unfold TA_M; lia]).
  assert (U9 : bv_unsigned (ew E 9) = TA_OW) by exact B9.
  assert (U19 : bv_unsigned (ew E 19) = TA_M) by exact B19.
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
    nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_foreign 4);
           Z_to_bv 64 (TW.u_at Bw TW.A_M_e1_us 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_foreign 4)] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, annt_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  cbn [Nat.add nth] in E32, E33, E34, E35.
  pose proof (TWL.u_at_range Bw TW.A_OW_foreign 4) as R33.
  pose proof (TWL.u_at_range Bw TW.A_M_e1_us 4) as R34.
  pose proof (TWL.u_at_range Bw TW.A_M_foreign 4) as R35.
  change (8 * Z.of_nat 4) with 32 in R33, R34, R35.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_annt2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold annt_r_fo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw); apply annt_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TA_OW 0xd4 4 (SOff 33 0) (TW.u_at Bw TW.A_OW_foreign 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 0xd4 4 TMAP_A_ok Htw TMAP_A_OW
        ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold annt_r_dp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw); apply annt_inG; lia|].
      apply Forall_nil.
    + unfold annt_r_m, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B19.
      split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS (TA_M + o) G_HARNESS_rw); apply annt_inG; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs E _ TA_M 0x14 4 (SOff 34 0) (TW.u_at Bw TW.A_M_e1_us 4));
          [apply DEN; [exact E34 | lia] | exact R34 | lia |].
        exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 0x14 4 TMAP_A_ok Htw TMAP_A_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val tfibsegs E _ TA_M 0x18 4 (SOff 35 0) (TW.u_at Bw TW.A_M_foreign 4));
          [apply DEN; [exact E35 | lia] | exact R35 | lia |].
        exact (tw_read_val tfibsegs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 0x18 4 TMAP_A_ok Htw TMAP_A_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  - unfold annt_r_fo, annt_r_dp, annt_r_m.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9, B19.
    unfold TA_OW, TA_M. repeat split; lia.
  - unfold annt_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, E32, E33, E34, E35.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_OW_foreign 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_e1_us 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_foreign 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.
End h.

(* ---- the model ---- *)

Lemma annt_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* mrx_e0w's three outcomes. *)
Lemma e0w_model : forall Bw B3, EPI.mrx_e0w Bw = Some (B3, tt) ->
  (TW.M_state Bw <> 0 /\ B3 = Bw) \/
  (TW.M_state Bw = 0 /\ TW.Cfg_auto_wake Bw = 0 /\ B3 = Bw) \/
  (TW.M_state Bw = 0 /\ TW.Cfg_auto_wake Bw <> 0 /\ exists rw, TC.m_wake_m Bw = Some (B3, rw)).
Proof.
intros Bw B3 H. unfold EPI.mrx_e0w, TC.truth, TC.S_IDLE in H.
destruct (Z.eqb_spec (TW.M_state Bw) 0) as [S0|S0]; cbn [andb] in H.
- destruct (Z.eqb_spec (TW.Cfg_auto_wake Bw) 0) as [A0|A0]; cbn [negb] in H.
  + right. left. split; [exact S0|]. split; [exact A0|]. exact (annt_some_inv _ _ H).
  + right. right. split; [exact S0|]. split; [exact A0|].
    destruct (TC.m_wake_m Bw) as [[B7 rw]|] eqn:EW; [|discriminate H].
    exists rw. rewrite (annt_some_inv _ _ H). reflexivity.
- left. split; [exact S0|]. exact (annt_some_inv _ _ H).
Qed.

(* The worlds of the announce tail (EPI.mrx_ann_tail): B2 after OW.desk + 1 and OW.desk_off, B4 after OW.desk_p and
   OW.desk_body, B7 after M.foreign = 1 and OW.foreign + 1 (cmd e1 with off < 0). *)
Definition annt_B2 (Bw : list byte) (off : Z) : list byte :=
  TW.set_OW_desk_off (TW.set_OW_desk Bw (TW.OW_desk Bw + 1)) off.
Definition annt_B4 (fr : TI.tframe) (Bw : list byte) (off dp : Z) : list byte :=
  TW.set_OW_desk_body (TW.set_OW_desk_p (annt_B2 Bw off) dp) (TI.tf_addr fr + 30).
Definition annt_B7 (B4 : list byte) : list byte :=
  TW.set_OW_foreign (TW.set_M_foreign B4 1) (TW.OW_foreign (TW.set_M_foreign B4 1) + 1).

Lemma annt_model : forall fr Bw off B3,
  EPI.mrx_ann_tail timg_A fr Bw off = Some (B3, tt) ->
  TW.OW_desk Bw <> TC.INT_MAX /\
  exists Bd dp, TC.desk_named_m timg_A (annt_B2 Bw off) (EPI.mrx_body fr) = Some (Bd, dp) /\
    (if EPI.mrx_fc fr =? TC.SPEC_CMD_E0 then EPI.mrx_e0 (annt_B4 fr Bw off dp)
     else EPI.mrx_e1 (annt_B4 fr Bw off dp) off) = Some (B3, tt).
Proof.
intros fr Bw off B3 H. unfold EPI.mrx_ann_tail, TC.int_inc in H.
destruct (TW.OW_desk Bw =? TC.INT_MAX) eqn:ID; cbv beta iota in H; [discriminate H|].
destruct (TC.desk_named_m timg_A (TW.set_OW_desk_off (TW.set_OW_desk Bw (TW.OW_desk Bw + 1)) off) (EPI.mrx_body fr))
  as [[Bd dp]|] eqn:DN; cbv beta iota in H; [|discriminate H].
split; [apply Z.eqb_neq; exact ID|]. exists Bd, dp. split; [exact DN | exact H].
Qed.

(* cmd e0: m_lost 3 when M.state is S_ONLINE, then mrx_e0w. *)
Lemma annt_e0 : forall B4 B3 st, TW.M_state (TW.set_M_foreign B4 0) = st -> EPI.mrx_e0 B4 = Some (B3, tt) ->
  (st = 2 /\ exists B6, TC.m_lost_m (TW.set_M_foreign B4 0) 3 = Some (B6, tt) /\ EPI.mrx_e0w B6 = Some (B3, tt)) \/
  (st <> 2 /\ EPI.mrx_e0w (TW.set_M_foreign B4 0) = Some (B3, tt)).
Proof.
intros B4 B3 st Hst H. unfold EPI.mrx_e0, TC.S_ONLINE, TC.R_DESK_OFFLINE in H. rewrite Hst in H.
destruct (Z.eqb_spec st 2) as [E|E]; cbv beta iota in H.
- left. split; [exact E|].
  destruct (TC.m_lost_m (TW.set_M_foreign B4 0) 3) as [[B6 []]|] eqn:L; cbv beta iota in H; [|discriminate H].
  exists B6. split; [first [exact L | reflexivity] | exact H].
- right. split; [exact E | exact H].
Qed.

(* cmd e1: off >= 0, M.e1_us and m_maybe_online; off < 0, the foreign count and m_lost 5 when M.state is S_ONLINE or
   S_WAKING. *)
Lemma annt_e1 : forall B4 off B3, EPI.mrx_e1 B4 off = Some (B3, tt) ->
  (0 <= off /\ TC.m_maybe_online_m (TW.set_M_e1_us (TW.set_M_foreign B4 0) 1) = Some (B3, tt)) \/
  (off < 0 /\ TW.OW_foreign (TW.set_M_foreign B4 1) <> TC.INT_MAX /\
   ((((TW.M_state (annt_B7 B4) =? 2) || (TW.M_state (annt_B7 B4) =? 1)) = true /\
     TC.m_lost_m (annt_B7 B4) 5 = Some (B3, tt)) \/
    (((TW.M_state (annt_B7 B4) =? 2) || (TW.M_state (annt_B7 B4) =? 1)) = false /\ B3 = annt_B7 B4))).
Proof.
intros B4 off B3 H. unfold EPI.mrx_e1, TC.int_inc in H.
destruct (Z.leb_spec 0 off) as [L|L]; cbv beta iota in H.
- left. split; [exact L | exact H].
- right. split; [exact L|].
  destruct (TW.OW_foreign (TW.set_M_foreign B4 1) =? TC.INT_MAX) eqn:IF; cbv beta iota in H; [discriminate H|].
  split; [apply Z.eqb_neq; exact IF|]. fold (annt_B7 B4) in H. unfold TC.S_ONLINE, TC.S_WAKING, TC.R_FOREIGN in H.
  destruct ((TW.M_state (annt_B7 B4) =? 2) || (TW.M_state (annt_B7 B4) =? 1)) eqn:SO; cbv beta iota in H.
  + left. split; [reflexivity | exact H].
  + right. split; [reflexivity | exact (annt_some_inv _ _ H)].
Qed.

(* Reads of the worlds through the stores elsewhere. *)
Lemma annt_st5 : forall fr Bw off dp v, Z.of_nat (length Bw) = 65616 ->
  TW.M_state (TW.set_M_foreign (annt_B4 fr Bw off dp) v) = TW.M_state Bw.
Proof. intros fr Bw off dp v L. unfold annt_B4, annt_B2. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.
Lemma annt_fo5 : forall fr Bw off dp, Z.of_nat (length Bw) = 65616 ->
  TW.OW_foreign (TW.set_M_foreign (annt_B4 fr Bw off dp) 1) = TW.OW_foreign (annt_B2 Bw off).
Proof. intros fr Bw off dp L. unfold annt_B4, annt_B2. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.
Lemma annt_st7 : forall fr Bw off dp, Z.of_nat (length Bw) = 65616 ->
  TW.M_state (annt_B7 (annt_B4 fr Bw off dp)) = TW.M_state Bw.
Proof. intros fr Bw off dp L. unfold annt_B7, annt_B4, annt_B2. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.

(* ---- the machine values ---- *)

(* The 4-byte signed load of an atom holding the unsigned int u. *)
Lemma annt_sext : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma annt_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* garr8 of a suffix, and garr8 at a memory whose view keeps the bytes. *)
Lemma annt_garr8_skipn : forall mem base (l : list Z) k, (k <= length l)%nat ->
  garr8 tfibsegs mem base l -> garr8 tfibsegs mem (base + Z.of_nat k) (skipn k l).
Proof.
intros mem base l k Hk HG. rewrite <- (firstn_skipn k l) in HG. apply (garr8_app tfibsegs) in HG as [_ HG].
rewrite length_firstn in HG. replace (Nat.min k (length l)) with k in HG by lia. exact HG.
Qed.
Lemma annt_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  garr8 tfibsegs (mrestrict H m) base l ->
  (forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HG K j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept tfibsegs H H' m m' (base + Z.of_nat j) 1 _); [|exact Hv].
intros k Hk. apply K. lia.
Qed.

(* The bytes the segment stores are bytes of mrx_wr. *)
Lemma annt_wr : forall a,
  (TA_OW + 208 <= a < TA_OW + 216) \/ (TA_OW + 232 <= a < TA_OW + 236) \/ (TA_OW + 240 <= a < TA_OW + 256) \/
  (TA_M + 20 <= a < TA_M + 28) -> mrx_wr a.
Proof.
intros a H. unfold mrx_wr, twa_fld.
unfold TW.A_OW_desk, TW.A_OW_desk_off, TW.A_OW_foreign, TW.A_OW_desk_p, TW.A_OW_desk_body, TW.A_M_e2_acked,
  TW.A_M_foreign, TW.OFF_OW, TW.OFF_M.
destruct H as [H|[H|[H|H]]].
- destruct (Z_lt_le_dec a (TA_OW + 212)) as [L|L].
  + do 17 right. left. lia.
  + do 18 right. left. lia.
- do 23 right. left. lia.
- destruct (Z_lt_le_dec a (TA_OW + 248)) as [L|L].
  + do 24 right. left. lia.
  + do 25 right. left. lia.
- destruct (Z_lt_le_dec a (TA_M + 24)) as [L|L].
  + do 3 right. left. lia.
  + do 4 right. left. lia.
Qed.

(* ---- the world relation after the stores of the segment ---- *)

(* The windows of the regions after desk_named. *)
Definition annt_w2 (a : Z) : Prop :=
  (TA_OW + 212 <= a < TA_OW + 216) \/ (TA_OW + 240 <= a < TA_OW + 256) \/ (TA_M + 20 <= a < TA_M + 28).

(* A 4-byte field a path did not store still holds the world's bytes. *)
Lemma annt_keep4 : forall rd0 rdF Bw o b n k u,
  tw_at TMAP_A rd0 Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + 4 <= n -> u = TW.u_at Bw (o + k) 4 ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte u 4 j)) ->
  forall x, b + k <= x < b + k + 4 -> rdF x = rd0 x.
Proof.
intros rd0 rdF Bw o b n k u Htw Hin Hk Hkn -> HV x Hx.
replace x with (b + k + Z.of_nat (Z.to_nat (x - (b + k)))) by lia.
rewrite (HV (Z.to_nat (x - (b + k))) ltac:(lia)).
rewrite (tw_read TMAP_A rd0 Bw o b n k 4 (Z.to_nat (x - (b + k))) TMAP_A_ok Htw Hin Hk
  ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) ltac:(lia)).
reflexivity.
Qed.

(* cmd e0: OW.desk_p, OW.desk_body, M.foreign = 0. *)
Lemma annt_w_e0 : forall B2 dp p rd0 rdF,
  tw_at TMAP_A rd0 B2 ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 240 + Z.of_nat j) = Some (YO0f.le_byte dp 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 248 + Z.of_nat j) = Some (YO0f.le_byte p 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 240 <= x < TA_OW + 256) -> ~ (TA_M + 24 <= x < TA_M + 28) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_foreign (TW.set_OW_desk_body (TW.set_OW_desk_p B2 dp) p) 0).
Proof.
intros B2 dp p rd0 rdF Htw VP VB VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_M_foreign, TW.set_OW_desk_body, TW.set_OW_desk_p.
pose proof (mrx_tw_start rdF rd0 B2 Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 240 TW.A_OW_desk_p 8 dp H0 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VP) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 248 TW.A_OW_desk_body 8 p H1 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VB) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 24 TW.A_M_foreign 4 0 H2 TMAP_A_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H3.
apply (mrx_tw_end rdF rd0 _ _ H3). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia].
Qed.

(* cmd e1, off >= 0: OW.desk_p, OW.desk_body, M.foreign = 0, M.e1_us = 1. *)
Lemma annt_w_mo : forall B2 dp p rd0 rdF,
  tw_at TMAP_A rd0 B2 ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 240 + Z.of_nat j) = Some (YO0f.le_byte dp 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 248 + Z.of_nat j) = Some (YO0f.le_byte p 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 20 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 240 <= x < TA_OW + 256) -> ~ (TA_M + 20 <= x < TA_M + 28) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_e1_us (TW.set_M_foreign (TW.set_OW_desk_body (TW.set_OW_desk_p B2 dp) p) 0) 1).
Proof.
intros B2 dp p rd0 rdF Htw VP VB VF VE Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_M_e1_us, TW.set_M_foreign, TW.set_OW_desk_body, TW.set_OW_desk_p.
pose proof (mrx_tw_start rdF rd0 B2 Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 240 TW.A_OW_desk_p 8 dp H0 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VP) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 248 TW.A_OW_desk_body 8 p H1 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VB) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 24 TW.A_M_foreign 4 0 H2 TMAP_A_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 20 TW.A_M_e1_us 4 1 H3 TMAP_A_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VE) as H4.
apply (mrx_tw_end rdF rd0 _ _ H4). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia].
Qed.

(* cmd e1, off < 0: OW.desk_p, OW.desk_body, M.foreign = 1, OW.foreign = fo. *)
Lemma annt_w_neg : forall B2 dp p fo rd0 rdF,
  tw_at TMAP_A rd0 B2 ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 240 + Z.of_nat j) = Some (YO0f.le_byte dp 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TA_OW + 248 + Z.of_nat j) = Some (YO0f.le_byte p 8 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 212 + Z.of_nat j) = Some (YO0f.le_byte fo 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 240 <= x < TA_OW + 256) -> ~ (TA_M + 24 <= x < TA_M + 28) ->
     ~ (TA_OW + 212 <= x < TA_OW + 216) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_OW_foreign (TW.set_M_foreign (TW.set_OW_desk_body (TW.set_OW_desk_p B2 dp) p) 1) fo).
Proof.
intros B2 dp p fo rd0 rdF Htw VP VB VF VO Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_OW_foreign, TW.set_M_foreign, TW.set_OW_desk_body, TW.set_OW_desk_p.
pose proof (mrx_tw_start rdF rd0 B2 Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 240 TW.A_OW_desk_p 8 dp H0 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VP) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 248 TW.A_OW_desk_body 8 p H1 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VB) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 24 TW.A_M_foreign 4 1 H2 TMAP_A_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 212 TW.A_OW_foreign 4 fo H3 TMAP_A_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VO) as H4.
apply (mrx_tw_end rdF rd0 _ _ H4). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* The chunk at offset off of a region, as an index. *)
Fixpoint annt_find (off : Z) (cs : list YP09.chunk) : nat :=
  match cs with
  | [] => 0
  | c :: cs' => if Z.eqb (YP09.c_off c) off then 0 else S (annt_find off cs')
  end.
Lemma annt_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (k : nat) (x : A),
  Forall P l -> nth_error l k = Some x -> P x.
Proof. intros A P l k x HF Hk. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l k Hk). Qed.

(* The bytes of the chunk at offset off of region idx of the state of HS, base rewritten by UB: forall j < width,
   the view at base + off + j is le_byte v width j, for Hden : sv_denot E e = Z_to_bv 64 v. *)
Ltac annt_chunk HS idx off UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF ?ss (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG;
    let cs := eval vm_compute in (YP09.r_chunks (nth idx (ss_mem ss) annt_r_dp)) in
    let c := eval vm_compute in (annt_find off cs) in
    cbn [ms_mem restrict] in RG;
    destruct RG as (_ & _ & _ & HC);
    cbn [YP09.r_base YP09.r_chunks base_val] in HC;
    rewrite UB in HC;
    pose proof (annt_Forall_nth _ _ c _ HC eq_refl) as HC1;
    pose proof (mrx_chunk_rd _ _ _ _ _ _ _ v HC1 Hden ltac:(cbn; lia)) as V;
    clear HC HC1
  end.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac annt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "annt_reg: no match for" T; fail
  end.

(* The windows a run wrote, computed, each case closed by tac. *)
Ltac annt_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run whose regions have no writable byte. *)
Ltac annt_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* After a run: the model generalized, the old machine states dropped. *)
Ltac annt_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* The pc of the current machine state, renamed to a cut's pc. *)
Ltac annt_pc pc :=
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?pcx) _ _) _) _ =>
    replace pcx with pc by (vm_compute; reflexivity) end.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mrx_seg_e0w :
  K (MRX_PC OFF_WAKE) (R_WAKE Bw' r) ->
  K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_E0W) (R_E0W Bw' r).
Proof using All.
intros KW KT. unfold mrx_K. intros Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsaved & Htw & HR).
destruct HR as (B3 & H19 & He0w & Htk & Hr1).
pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (MSV : MRX_STK = 8352) by (vm_compute; reflexivity).
pose proof (e0w_model Bwc B3 He0w) as HM. clear He0w.
set (E0 := e0w_E regs2 Bwc).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, e0w_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn; unfold E0, e0w_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bwc TW.A_M_state 4))
  by (unfold E0, e0w_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_auto_wake 4))
  by (unfold E0, e0w_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
pose proof (TWL.u_at_range Bwc TW.A_M_state 4) as R33. pose proof (TWL.u_at_range Bwc TW.A_Cfg_auto_wake 4) as R34.
change (8 * Z.of_nat 4) with 32 in R33, R34.
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bwc)) by exact (annt_sext E0 33 _ E33 R33).
assert (D34 : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.Cfg_auto_wake Bwc))
  by exact (annt_sext E0 34 _ E34 R34).
pose proof (TWL.s32_range Bwc TW.A_M_state) as S33. pose proof (TWL.s32_range Bwc TW.A_Cfg_auto_wake) as S34.
change (TW.s32_at Bwc TW.A_M_state) with (TW.M_state Bwc) in S33.
change (TW.s32_at Bwc TW.A_Cfg_auto_wake) with (TW.Cfg_auto_wake Bwc) in S34.
pose proof (e0w_entry Wc regs2 mem2 Bwc Htw H19) as HS. fold E0 in HS.
assert (SHOK : sh_ok tfibsegs ANNT_Bx ANNT_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, ANNT_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
(* the end of a run that wrote nothing, at a cut: the common facts of mrx_at *)
assert (CL : forall ms md pc R Bx,
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    (ms_mem ms) md 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a) ->
  YK11.getr (ms_regs ms) 2 = YK11.getr regs2 2 -> YK11.getr (ms_regs ms) 3 = YK11.getr regs2 3 ->
  YK11.getr (ms_regs ms) 4 = YK11.getr regs2 4 ->
  K pc R -> R Wc Bwc ly2 S2 (ms_regs ms) (ms_mem ms) ->
  Bx = Bwc ->
  SRr tfibsegs Wc (mkCfg (@YK11.mkst fx (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (YK11.seg_rom tfibsegs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r)).
{ intros ms md pc R Bx HJx KA Q2 Q3 Q4 KX HRx ->.
  apply (KX Wc Bwc).
  apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc ly2 S2).
  - exact HJx.
  - exact Hfr.
  - exact Hperm.
  - exact Hmo.
  - rewrite Q2. exact Hsp.
  - rewrite Q3. exact Hgp.
  - rewrite Q4. exact Htp.
  - apply (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 Hsaved). intros a Ha. apply KA. lia.
  - apply (tw_kept TMAP_A (aview tfibsegs (w_H Wc) mem2) _ Bwc Htw). intros x Hx.
    pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA. lia.
  - exact HRx. }
replace (MRX_PC OFF_E0W) with (BASE + (AF_m_rx + OFF_E0W)) by (vm_compute; reflexivity).
(* run 1, +0x560: M.state; it stops at `bnez a0`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ annt_awr_ro. }
annt_md. rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(exfalso; lia). }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state <> S_IDLE: the cut TICK, the world unchanged *)
  rewrite D33 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  destruct HM as [[_ HB3] | [[Hs _] | [Hs _]]]; [| exfalso; exact (Hc Hs) | exfalso; exact (Hc Hs)].
  subst B3.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
  { annt_awr_ro. }
  annt_md.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha. rewrite <- (KA1 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(exfalso; lia). }
  clear HF HFr HG.
  annt_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS. annt_pc (MRX_PC OFF_TICK).
  apply (CL ms _ _ _ Bwc HJ KA Q2 Q3 Q4 KT); [|reflexivity].
  unfold R_TICK. split; [exact Htk | exact Hr1].
- (* M.state = S_IDLE: g_cfg.auto_wake *)
  rewrite D33 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  destruct HM as [[Hs _] | HM]; [exfalso; exact (Hs Hc)|]. rename Hc into Hst0.
  (* run 2, +0x564 .. +0x570: `bnez` not taken, auto_wake; it stops at `beqz a0`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { annt_awr_ro. }
  annt_md. rename ms into ms2.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms2) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha. rewrite <- (KA1 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(exfalso; lia). }
  clear HF HFr HG KA1. clear dependent ms1.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* auto_wake = 0: the cut TICK, the world unchanged *)
    rewrite D34 in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (EPI.mrxk_eqb (TW.Cfg_auto_wake Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    destruct HM as [(_ & _ & HB3) | (_ & Ha & _)]; [| exfalso; exact (Ha Hc)].
    subst B3.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
    { annt_awr_ro. }
    annt_md.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
    { intros a Ha. rewrite <- (KA2 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(exfalso; lia). }
    clear HF HFr HG.
    annt_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) Q2
      ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) Q3
      ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) Q4
      ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    pmkst HS. annt_pc (MRX_PC OFF_TICK).
    apply (CL ms _ _ _ Bwc HJ KA Q2 Q3 Q4 KT); [|reflexivity].
    unfold R_TICK. split; [exact Htk | exact Hr1].
  + (* auto_wake <> 0: the cut WAKE *)
    rewrite D34 in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (EPI.mrxk_eqb (TW.Cfg_auto_wake Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    destruct HM as [(_ & Ha & _) | (_ & _ & rw & Hwk)]; [exfalso; exact (Hc Ha)|].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_WAKE).
    { annt_awr_ro. }
    annt_md.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
    { intros a Ha. rewrite <- (KA2 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(exfalso; lia). }
    clear HF HFr HG.
    annt_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) Q2
      ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) Q3
      ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) Q4
      ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    pmkst HS. annt_pc (MRX_PC OFF_WAKE).
    apply (CL ms _ _ _ Bwc HJ KA Q2 Q3 Q4 KW); [|reflexivity].
    unfold R_WAKE. exists B3, rw. split; [exact Hwk|]. split; [exact Htk | exact Hr1].
Qed.

Ltac annt_awr2 UB1 UB2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?UB1, ?UB2 in Ha; right; left; apply annt_inG; unfold TA_M, TA_OW in *; lia ] |]);
  apply awr_ok_x_nil.

(* The write rights of a run whose writable bytes lie in M or OW (bytes of G); UB rewrites a region base. *)
Ltac annt_awr UB :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?UB in Ha; right; left; apply annt_inG; unfold TA_M, TA_OW in *; lia ] |]);
  apply awr_ok_x_nil.

Lemma mrx_seg_annt :
  K (MRX_PC OFF_E0L) (R_E0L Bw' r) ->
  K (MRX_PC OFF_E0W) (R_E0W Bw' r) ->
  K (MRX_PC OFF_MO) (R_MO Bw' r) ->
  K (MRX_PC OFF_LOST) (R_LOST Bw' r) ->
  K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r).
Proof using All.
intros KE0L KE0W KMO KLOST KT. unfold mrx_K. intros Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsaved & Htw & HR).
destruct HR as (off & -> & -> & Hfrs & Hhdr & Hcmd & Hblen & Hoff & Hoff0 & H8 & H19 & H20 & H23 & H25 &
  B3 & Hann & Htk & Hr1).
pose proof HST as (Hspz0 & Hsp16 & Hceil & H46 & H47 & _ & _ & Hgp0 & Htp0 & _ & _ & Hfa0 & Hfan & Hsrc & Hoffw & Hapart &
  Hnev & HAR0).
assert (MSV : MRX_STK = 8352) by (vm_compute; reflexivity).
assert (DSV : DNAMED_STK = 8208) by (vm_compute; reflexivity).
assert (BSV : BASE = 0x81264) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the model *)
assert (LB : Z.of_nat (length Bwc) = 65616)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
destruct (annt_model fr Bwc off B3 Hann) as (HID & Bd & dp & HDNm & Htail). clear Hann.
destruct Hfrs as (Hg8 & Hrd & Hrom). pose proof Hrd as (_ & _ & _ & _ & Hq0 & Hq63).
destruct Hhdr as (Hnr & Het & Hnb).
unfold EPI.mrx_blen, TC.SPEC_ANN_MIN in Hblen.
assert (HLB : 63 <= mlen fr) by lia.
set (E0 := annt_E regs2 Bwc).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, annt_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn; unfold E0, annt_E; apply ew_Eimg_Ereg_nat; exact Hn).
destruct annt_vals as (V12 & _).
assert (U12 : bv_unsigned (ew E0 (A_OBJ 12)) = TA_OW).
{ unfold E0, annt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V12.
  apply unsigned_lit_small. unfold TA_OW. lia. }
assert (U12' : bv_unsigned (ew E0 253%nat) = TA_OW) by exact U12.
pose proof (annt_entry Wc regs2 mem2 Bwc Htw) as HS. fold E0 in HS.
assert (SHOK : sh_ok tfibsegs ANNT_Bx ANNT_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, ANNT_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
replace (MRX_PC OFF_ANNT) with (BASE + (AF_m_rx + OFF_ANNT)) by (vm_compute; reflexivity).
(* run 1, +0x51c .. +0x538: s1 = &OW, OW.desk + 1, OW.desk_off, a0 = s0, `jal desk_named`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ annt_awr U12'. }
annt_md. rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 208 <= a < TA_OW + 212) -> ~ (TA_OW + 232 <= a < TA_OW + 236) ->
  aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 208 <= x < TA_OW + 212) \/ (TA_OW + 232 <= x < TA_OW + 236)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  annt_win Hin Hx ltac:(rewrite ?U12' in Hx; first [left; lia | right; lia]). }
clear HF HFr HG.
(* the bytes the run stored, and the world relation at the call *)
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_desk 4))
  by (unfold E0, annt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
pose proof (TWL.u_at_range Bwc TW.A_OW_desk 4) as R33. change (8 * Z.of_nat 4) with 32 in R33.
assert (DD : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_desk Bwc + 1)).
{ change (sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E0 (SExt true 32 (SOff 33 0))) (sv_denot E0 (SLit 1))).
  rewrite (annt_sext E0 33 _ E33 R33). exact (annt_add_den (TW.OW_desk Bwc) 1). }
assert (DO : sv_denot E0 (SOff 20 0) = Z_to_bv 64 off)
  by (cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H20).
pose proof (st_ok_region_nth E0 _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E0 _ _ 1 _ HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG0, RG1.
destruct RG0 as (_ & _ & _ & HC0). destruct RG1 as (_ & _ & _ & HC1).
cbn [YP09.r_base YP09.r_chunks base_val] in HC0, HC1. rewrite U12' in HC0, HC1.
pose proof (mrx_chunk_rd _ _ _ _ _ _ _ _ (Forall_inv HC0) DD ltac:(cbn; lia)) as VD.
pose proof (mrx_chunk_rd _ _ _ _ _ _ _ _ (Forall_inv HC1) DO ltac:(cbn; lia)) as VO.
clear HC0 HC1.
assert (HW1 : tw_at TMAP_A (aview tfibsegs (w_H Wc) (ms_mem ms1)) (annt_B2 Bwc off)).
{ unfold annt_B2, TW.set_OW_desk_off, TW.set_OW_desk.
  pose proof (mrx_tw_start (aview tfibsegs (w_H Wc) (ms_mem ms1)) (aview tfibsegs (w_H Wc) mem2) Bwc Htw) as H0.
  pose proof (mrx_tw_step _ _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 208 TW.A_OW_desk 4 (TW.OW_desk Bwc + 1) H0 TMAP_A_OW
    eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VD) as H1.
  pose proof (mrx_tw_step _ _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 232 TW.A_OW_desk_off 4 off H1 TMAP_A_OW
    eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VO) as H2.
  apply (mrx_tw_end _ _ _ _ H2). intros x Hx HP. mrx_unP HP.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  cbn [Z.of_nat Pos.of_succ_nat] in *.
  apply KA1; [lia | lia | lia]. }
(* the frame's bytes, kept by the run (mrx_apart) *)
assert (HFK : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr ->
  aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha.
  apply KA1; [lia | intros Hw; apply (Hapart a); [apply annt_wr; lia | exact Ha]
               | intros Hw; apply (Hapart a); [apply annt_wr; lia | exact Ha]]. }
(* desk_named's premises: the body's bytes, placement and window, the read-only view, the model call *)
assert (Hg8b : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms1)) (TI.tf_addr fr + 30) (map DSpec.bz (EPI.mrx_body fr))).
{ unfold EPI.mrx_body. rewrite <- skipn_map.
  apply (annt_garr8_kept (w_H Wc) (w_H Wc) mem2 (ms_mem ms1)).
  - change (TI.tf_addr fr + 30) with (TI.tf_addr fr + Z.of_nat 30).
    apply annt_garr8_skipn; [rewrite length_map; unfold mlen in HLB; lia | exact Hg8].
  - intros a Ha. rewrite length_skipn, length_map in Ha. apply HFK. unfold mlen. lia. }
assert (Hrd1 : decode_rd_ok Wc (ms_mem ms1) (TI.tf_addr fr) (mlen fr)).
{ apply (trans_rd_ok_view Wc Wc mem2 (ms_mem ms1) _ _ Hrd); [exact HFK |].
  intros s Hs. apply KA1; unfold TA_OW in *; lia. }
assert (Hsrc1 : trans_src_ok B lyc Sc Wc (ms_mem ms1) (TI.tf_addr fr) (mlen fr))
  by exact (trans_src_ok_inner B lyc Sc W memc lyc Sc Wc (ms_mem ms1) _ _ (fun bm H => H) (fun f H => H)
    (fun cid pos => eq_refl) eq_refl eq_refl Hrd1 Hsrc).
assert (LBD : Z.of_nat (length (EPI.mrx_body fr)) = mlen fr - 30)
  by (unfold EPI.mrx_body, mlen; rewrite length_skipn; unfold mlen in HLB; lia).
assert (Hsrcb : trans_src_ok B lyc Sc Wc (ms_mem ms1) (TI.tf_addr fr + 30) (Z.of_nat (length (EPI.mrx_body fr))))
  by (apply (trans_src_ok_sub B lyc Sc Wc (ms_mem ms1) (TI.tf_addr fr) (mlen fr)); [exact Hsrc1 | lia | lia | lia]).
assert (Hromb : trans_rom_view_rd Wc (ms_mem ms1)).
{ intros a Ha. rewrite <- (Hrom a Ha). pose proof (trans_ro_rd_bounds a Ha) as Hb. apply KA1; unfold TA_OW; lia. }
(* the registers at the call *)
annt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15204)) R1 ltac:(apply codeptr_val; exact HEI).
annt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) R2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hsp).
annt_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans Hgp Hgp0)).
annt_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans Htp Htp0)).
annt_reg HS (Z_to_bv 5 10) (w64 (TI.tf_addr fr + 30)) R10
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8).
annt_reg HS (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) R8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8).
annt_reg HS (Z_to_bv 5 9) (w64 TA_OW) R9 ltac:(cbn [sv_denot]; rewrite U12', Z.add_0_r; reflexivity).
annt_reg HS (Z_to_bv 5 19) (w64 TA_M) R19
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H19).
annt_reg HS (Z_to_bv 5 20) (w64 off) R20
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H20).
annt_reg HS (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) R23
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H23).
annt_reg HS (Z_to_bv 5 25) (w64 (mfb fr 28)) R25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H25).
assert (Hspz1 : spZ (ms_regs ms1) = sp1 - 144).
{ change (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = sp1 - 144). rewrite R2.
  rewrite unsigned_lit_small by (unfold MRX_FRAME; lia). unfold MRX_FRAME. lia. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx tfibsegs (transport_sigma TS_desk_named) rg mm mdx) Q) end.
(* +0x538: desk_named (fa + 30), a donor-form callee through gx_call_cg *)
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head tfibsegs B MT TG.G_HARNESS MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    (ms_mem ms1) mdw 0 _ (ms_regs ms1) DNAMED_STK DNAMED_EV 0 (fun _ => False)
    (fun regs2 _ _ => YK11.getr regs2 10 = w64 dp /\ Bd = annt_B2 Bwc off) HGX HGNE HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (HDN fx MRX_STK sp1 [] lyc Sc W memS mdc [] lyc Sc Wc (ms_mem ms1) mdw 0 (ms_regs ms1)
      (TI.tf_addr fr + 30) dp (EPI.mrx_body fr) (annt_B2 Bwc off) Bd HJS
      (eq_ind_r YK0s.ret_ok (ret_ok_codeptr_v (PI := PI_transport) 15204 ltac:(lia) eq_refl) R1)
      ltac:(change (4096 <= bv_unsigned (YK11.getr (ms_regs ms1) 1%bv)); rewrite R1;
            rewrite unsigned_lit_small by (rewrite BSV; lia); rewrite BSV; lia)
      R3 R4 R10
      ltac:(rewrite Hspz1; replace (sp1 - 144) with (sp1 + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16)
      ltac:(rewrite Hspz1; lia) ltac:(rewrite Hspz1; lia) ltac:(lia)
      Hg8b Hsrcb ltac:(unfold decode_off_win; rewrite Hspz1, LBD; lia) Hromb HDNm ltac:(unfold DNAMED_EV; lia)). }
  intros W2 c2 _ HP. apply decode_cg_post_dcg. exact HP. }
intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 & [[Q10 HBd] HGK]).
assert (e = 0) by (unfold DNAMED_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
rewrite R1. replace (BASE + 15204) with (BASE + ANNT_RET) by (vm_compute; reflexivity).
(* the facts carried across the call: the world relation (G kept), the saved slots (above its window) *)
assert (HW3 : tw_at TMAP_A (aview tfibsegs (w_H W3) mem3) (annt_B2 Bwc off))
  by exact (tw_kept_GA _ _ _ HW1 (gx_kept_rows tfibsegs TG.G_HARNESS Wc (ms_mem ms1) W3 mem3 HGK)).
destruct HK3 as (K31 & _).
assert (KS3 : forall a, sp1 - 104 <= a < sp1 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha. refine (eq_trans (K31 a ltac:(lia) ltac:(rewrite Hspz1; lia)) _). apply KA1; unfold TA_OW in *; lia. }
assert (Hsaved3 : mrx_saved W3 mem3 sp1 regs0) by exact (mrx_saved_kept Wc W3 mem2 mem3 sp1 regs0 Hsaved KS3).
assert (G2 : YK11.getr regs3 (Z_to_bv 5 2) = Z_to_bv 64 (sp1 - MRX_FRAME))
  by (rewrite (HP3 2 ltac:(unfold acallee_saved; lia)); exact R2).
assert (G3 : YK11.getr regs3 (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite (HP3 3 ltac:(unfold acallee_saved; lia)); exact R3).
assert (G4 : YK11.getr regs3 (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite (HP3 4 ltac:(unfold acallee_saved; lia)); exact R4).
assert (G8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 (TI.tf_addr fr + 30))
  by (rewrite (HP3 8 ltac:(unfold acallee_saved; lia)); exact R8).
assert (G9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 TA_OW) by (rewrite (HP3 9 ltac:(unfold acallee_saved; lia)); exact R9).
assert (G19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 TA_M)
  by (rewrite (HP3 19 ltac:(unfold acallee_saved; lia)); exact R19).
assert (G20 : YK11.getr regs3 (Z_to_bv 5 20) = w64 off)
  by (rewrite (HP3 20 ltac:(unfold acallee_saved; lia)); exact R20).
assert (G23 : YK11.getr regs3 (Z_to_bv 5 23) = w64 (TW.M_state Bwc))
  by (rewrite (HP3 23 ltac:(unfold acallee_saved; lia)); exact R23).
assert (G25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 (mfb fr 28))
  by (rewrite (HP3 25 ltac:(unfold acallee_saved; lia)); exact R25).
clear dependent ms1.
(* the fresh state at +0x53c *)
pose proof (annt_entry2 W3 regs3 mem3 (annt_B2 Bwc off) HW3 G9 G19) as HS.
set (E1 := annt_E2 regs3 (annt_B2 Bwc off)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, annt_E2; apply Eimg_env).
assert (EE1 : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E1 n0 = YK11.getr regs3 r0)
  by (intros n0 r0 Hn0; unfold E1, annt_E2; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (U9 : bv_unsigned (ew E1 9) = TA_OW)
  by (rewrite (EE1 9%nat (Z_to_bv 5 9) eq_refl), G9; apply unsigned_lit_small; unfold TA_OW; lia).
assert (U19 : bv_unsigned (ew E1 19) = TA_M)
  by (rewrite (EE1 19%nat (Z_to_bv 5 19) eq_refl), G19; apply unsigned_lit_small; unfold TA_M; lia).
assert (SHOK1 : sh_ok tfibsegs ANNT_Bx ANNT_SH E1 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, ANNT_SH; apply Forall_nil).
(* run 2, +0x53c .. +0x548: OW.desk_p, OW.desk_body; it stops at `bne s9, a1` (cmd e0?). *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ annt_awr2 U9 U19. }
annt_md. rename ms into ms2.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
  aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
clear HF HFr HG.
(* the end of a run after desk_named, at a cut: the common facts of mrx_at *)
assert (CL2 : forall ms md pc R Bx,
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly3 S3 W3
    (ms_mem ms) md 0 ->
  (forall a, sp1 - 104 <= a < sp1 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a) ->
  YK11.getr (ms_regs ms) 2 = YK11.getr regs3 2 -> YK11.getr (ms_regs ms) 3 = YK11.getr regs3 3 ->
  YK11.getr (ms_regs ms) 4 = YK11.getr regs3 4 ->
  tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms)) Bx ->
  K pc R -> R W3 Bx ly3 S3 (ms_regs ms) (ms_mem ms) ->
  SRr tfibsegs W3 (mkCfg (@YK11.mkst fx (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (YK11.seg_rom tfibsegs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r)).
{ intros ms md pc R Bx HJx KS Q2 Q3 Q4 HWx KX HRx.
  apply (KX W3 Bx).
  apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R W3 Bx ly3 S3).
  - exact HJx.
  - exact Hfr3.
  - exact Hperm3.
  - exact HMO3.
  - rewrite Q2. exact G2.
  - rewrite Q3. exact (eq_trans G3 (eq_sym Hgp0)).
  - rewrite Q4. exact (eq_trans G4 (eq_sym Htp0)).
  - exact (mrx_saved_kept W3 W3 mem3 (ms_mem ms) sp1 regs0 Hsaved3 KS).
  - exact HWx.
  - exact HRx. }
(* the values the code compares and stores *)
assert (Dcmd : sv_denot E1 (SOff 25 0) = Z_to_bv 64 (mfb fr 28))
  by (cbn [sv_denot]; rewrite (EE1 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G25).
assert (Dst : sv_denot E1 (SOff 23 0) = Z_to_bv 64 (TW.M_state Bwc))
  by (cbn [sv_denot]; rewrite (EE1 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G23).
assert (Doff : sv_denot E1 (SOff 20 0) = Z_to_bv 64 off)
  by (cbn [sv_denot]; rewrite (EE1 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G20).
assert (Ddp : sv_denot E1 (SOff 10 0) = Z_to_bv 64 dp)
  by (cbn [sv_denot]; rewrite (EE1 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q10).
assert (Dp : sv_denot E1 (SOff 8 0) = Z_to_bv 64 (TI.tf_addr fr + 30))
  by (cbn [sv_denot]; rewrite (EE1 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G8).
assert (D33 : sv_denot E1 (SOff 33 0) = Z_to_bv 64 (TW.u_at (annt_B2 Bwc off) TW.A_OW_foreign 4)).
{ cbn [sv_denot]. unfold E1, annt_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs3 _ 1). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D34 : sv_denot E1 (SOff 34 0) = Z_to_bv 64 (TW.u_at (annt_B2 Bwc off) TW.A_M_e1_us 4)).
{ cbn [sv_denot]. unfold E1, annt_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs3 _ 2). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (TWL.s32_range Bwc TW.A_M_state) as Sst. change (TW.s32_at Bwc TW.A_M_state) with (TW.M_state Bwc) in Sst.
assert (Rcmd : 224 <= mfb fr 28 <= 225) by (unfold TC.SPEC_CMD_E0, TC.SPEC_CMD_E1 in Hcmd; lia).
change (EPI.mrx_fc fr) with (mfb fr 28) in Htail.
psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
2: { (* cmd = e0: M.foreign = 0, then the cut E0L (M.state = S_ONLINE) or E0W *)
  rewrite Dcmd in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (mfb fr 28) 224 ltac:(lia) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into Hc0.
  replace (mfb fr 28 =? TC.SPEC_CMD_E0) with true in Htail by (symmetry; apply Z.eqb_eq; unfold TC.SPEC_CMD_E0; lia).
  cbv beta iota in Htail.
  pose proof (annt_st5 fr Bwc off dp 0 LB) as HS5.
  (* run 3, +0x548 .. +0x554: `bne` not taken, M.foreign = 0; it stops at `bne s7, a0` *)
  paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
  { annt_awr2 U9 U19. }
  annt_md. rename ms into ms3.
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
    aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KA2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
  clear HF HFr HG KA2. clear dependent ms2.
  psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
  2: { (* M.state = S_ONLINE: a0 = 3, the cut E0L *)
    rewrite Dst in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 2 ltac:(lia) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (annt_e0 _ _ _ HS5 Htail) as [(_ & B6 & HL6 & HE6) | (Hn2 & _)]; [| exfalso; exact (Hn2 Hc)].
    paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_E0L).
    { annt_awr2 U9 U19. }
    annt_md.
    assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
      aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
    { intros a Ha Hn. rewrite <- (KA3 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
    clear HF HFr HG.
    annt_chunk HS 1%nat 240 U9 dp Ddp VP.
    annt_chunk HS 1%nat 248 U9 (TI.tf_addr fr + 30) Dp VB.
    annt_chunk HS 2%nat 24 U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
    annt_chunk HS 2%nat 20 U19 (TW.u_at (annt_B2 Bwc off) TW.A_M_e1_us 4) D34 VE.
    annt_chunk HS 0%nat 212 U9 (TW.u_at (annt_B2 Bwc off) TW.A_OW_foreign 4) D33 VFO.
    assert (HWF : tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms)) (TW.set_M_foreign (annt_B4 fr Bwc off dp) 0)).
    { apply (annt_w_e0 (annt_B2 Bwc off) dp (TI.tf_addr fr + 30) (aview tfibsegs (w_H W3) mem3) _ HW3 VP VB VF).
      intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      assert (Hd : annt_w2 x \/ ~ annt_w2 x) by (unfold annt_w2; lia).
      destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
      unfold annt_w2 in Hw. destruct (Z_lt_le_dec x TA_OW) as [Lx | Lx].
      - exact (annt_keep4 _ _ _ TW.OFF_M TA_M TW.SZ_M 20 _ HW3 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
          eq_refl VE x ltac:(unfold TA_OW, TA_M in *; lia)).
      - exact (annt_keep4 _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 212 _ HW3 TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)
          eq_refl VFO x ltac:(unfold TA_OW, TA_M in *; lia)). }
    annt_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) Q2
      ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) Q3
      ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) Q4
      ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    annt_reg HS (Z_to_bv 5 19) (w64 TA_M) Q19
      ltac:(cbn [sv_denot]; rewrite (EE1 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G19).
    annt_reg HS (Z_to_bv 5 10) (w64 3) Q10' ltac:(reflexivity).
    pmkst HS. annt_pc (MRX_PC OFF_E0L).
    apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold annt_w2, TA_OW, TA_M; lia)) Q2 Q3 Q4 HWF KE0L).
    unfold R_E0L. exists B6, B3. split; [exact Q19|]. split; [exact Q10'|]. split; [exact HL6|].
    split; [exact HE6|]. split; [exact Htk | exact Hr1]. }
  (* M.state <> S_ONLINE: the cut E0W *)
  rewrite Dst in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 2 ltac:(lia) ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  destruct (annt_e0 _ _ _ HS5 Htail) as [(Hon & _) | (_ & HE5)]; [exfalso; exact (Hc Hon)|].
  paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_E0W).
  { annt_awr2 U9 U19. }
  annt_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
    aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KA3 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
  clear HF HFr HG.
  annt_chunk HS 1%nat 240 U9 dp Ddp VP.
  annt_chunk HS 1%nat 248 U9 (TI.tf_addr fr + 30) Dp VB.
  annt_chunk HS 2%nat 24 U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  annt_chunk HS 2%nat 20 U19 (TW.u_at (annt_B2 Bwc off) TW.A_M_e1_us 4) D34 VE.
  annt_chunk HS 0%nat 212 U9 (TW.u_at (annt_B2 Bwc off) TW.A_OW_foreign 4) D33 VFO.
  assert (HWF : tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms)) (TW.set_M_foreign (annt_B4 fr Bwc off dp) 0)).
  { apply (annt_w_e0 (annt_B2 Bwc off) dp (TI.tf_addr fr + 30) (aview tfibsegs (w_H W3) mem3) _ HW3 VP VB VF).
    intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    assert (Hd : annt_w2 x \/ ~ annt_w2 x) by (unfold annt_w2; lia).
    destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
    unfold annt_w2 in Hw. destruct (Z_lt_le_dec x TA_OW) as [Lx | Lx].
    - exact (annt_keep4 _ _ _ TW.OFF_M TA_M TW.SZ_M 20 _ HW3 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
        eq_refl VE x ltac:(unfold TA_OW, TA_M in *; lia)).
    - exact (annt_keep4 _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 212 _ HW3 TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)
        eq_refl VFO x ltac:(unfold TA_OW, TA_M in *; lia)). }
  annt_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 19) (w64 TA_M) Q19
    ltac:(cbn [sv_denot]; rewrite (EE1 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G19).
  pmkst HS. annt_pc (MRX_PC OFF_E0W).
  apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold annt_w2, TA_OW, TA_M; lia)) Q2 Q3 Q4 HWF KE0W).
  unfold R_E0W. exists B3. split; [exact Q19|]. split; [exact HE5|]. split; [exact Htk | exact Hr1]. }
(* cmd <> e0: cmd e1 *)
rewrite Dcmd in Hc. cbn [branch_taken sv_denot] in Hc.
rewrite (EPI.mrxk_eqb (mfb fr 28) 224 ltac:(lia) ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
rename Hc into Hc1.
replace (mfb fr 28 =? TC.SPEC_CMD_E0) with false in Htail by (symmetry; apply Z.eqb_neq; unfold TC.SPEC_CMD_E0; lia).
cbv beta iota in Htail.
(* run 3, +0x548 .. +0x57c: `bne` taken; it stops at `bltz s4` *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ annt_awr2 U9 U19. }
annt_md. rename ms into ms3.
assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
  aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- (KA2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
clear HF HFr HG KA2. clear dependent ms2.
psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
2: { (* off >= 0: M.e1_us = 1, M.foreign = 0, the cut MO *)
  rewrite Doff in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
  destruct (annt_e1 _ _ _ Htail) as [(_ & HMOm) | (Hn & _)]; [| exfalso; lia].
  paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_MO).
  { annt_awr2 U9 U19. }
  annt_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
    aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KA3 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
  clear HF HFr HG.
  annt_chunk HS 1%nat 240 U9 dp Ddp VP.
  annt_chunk HS 1%nat 248 U9 (TI.tf_addr fr + 30) Dp VB.
  annt_chunk HS 2%nat 24 U19 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  annt_chunk HS 2%nat 20 U19 1 (@eq_refl _ (Z_to_bv 64 1)) VE.
  annt_chunk HS 0%nat 212 U9 (TW.u_at (annt_B2 Bwc off) TW.A_OW_foreign 4) D33 VFO.
  assert (HWF : tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms))
    (TW.set_M_e1_us (TW.set_M_foreign (annt_B4 fr Bwc off dp) 0) 1)).
  { apply (annt_w_mo (annt_B2 Bwc off) dp (TI.tf_addr fr + 30) (aview tfibsegs (w_H W3) mem3) _ HW3 VP VB VF VE).
    intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    assert (Hd : annt_w2 x \/ ~ annt_w2 x) by (unfold annt_w2; lia).
    destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
    unfold annt_w2 in Hw.
    exact (annt_keep4 _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 212 _ HW3 TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)
      eq_refl VFO x ltac:(unfold TA_OW, TA_M in *; lia)). }
  annt_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS. annt_pc (MRX_PC OFF_MO).
  apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold annt_w2, TA_OW, TA_M; lia)) Q2 Q3 Q4 HWF KMO).
  unfold R_MO. exists B3. split; [exact HMOm|]. split; [exact Htk | exact Hr1]. }
(* off < 0: M.foreign = 1, OW.foreign + 1 *)
rewrite Doff in Hc. cbn [branch_taken sv_denot] in Hc.
rewrite (EPI.mrxk_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. rename Hc into Hneg.
destruct (annt_e1 _ _ _ Htail) as [(Hp & _) | (_ & HFI & HM7)]; [exfalso; lia|].
(* run 4, +0x57c .. +0x5b4: OW.foreign + 1, M.foreign = 1, a2 = M.state - 1; it stops at `bltu a1, a2` *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ annt_awr2 U9 U19. }
annt_md. rename ms into ms4.
assert (KA4 : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
  aview tfibsegs (w_H W3) (ms_mem ms4) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- (KA3 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
clear HF HFr HG KA3. clear dependent ms3.
(* the test (bltu 1, M.state - 1): M.state is neither S_ONLINE nor S_WAKING *)
assert (Dw : sv_denot E1 (SAluw ALU_ADD (SOff 23 0) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (TW.M_state Bwc)) + -1))).
{ change (sv_denot E1 (SAluw ALU_ADD (SOff 23 0) (SLit (-1))))
    with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E1 (SOff 23 0))) (low32 (sv_denot E1 (SLit (-1)))))).
  rewrite Dst. change (sv_denot E1 (SLit (-1))) with (Z_to_bv 64 (-1)).
  exact (YK1g.aluw_addi_lit (Z_to_bv 64 (TW.M_state Bwc)) (-1)). }
assert (Dfo : sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)) =
  Z_to_bv 64 (TW.OW_foreign (annt_B2 Bwc off) + 1)).
{ assert (E33' : ew E1 33 = Z_to_bv 64 (TW.u_at (annt_B2 Bwc off) TW.A_OW_foreign 4))
    by (unfold E1, annt_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  pose proof (TWL.u_at_range (annt_B2 Bwc off) TW.A_OW_foreign 4) as R33'. change (8 * Z.of_nat 4) with 32 in R33'.
  change (sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E1 (SExt true 32 (SOff 33 0))) (sv_denot E1 (SLit 1))).
  rewrite (annt_sext E1 33 _ E33' R33'). exact (annt_add_den (TW.OW_foreign (annt_B2 Bwc off)) 1). }
rewrite (annt_st7 fr Bwc off dp LB) in HM7.
psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
2: { (* M.state is S_ONLINE or S_WAKING: a0 = 5 (R_FOREIGN), the cut LOST *)
  rewrite Dw in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (EPI.mrx_state12 (TW.M_state Bwc) Sst) in Hc.
  apply negb_false_iff in Hc.
  destruct HM7 as [(_ & HL7) | (Hs & _)]; [| rewrite Hc in Hs; discriminate Hs].
  paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_LOST).
  { annt_awr2 U9 U19. }
  annt_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
    aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KA4 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
  clear HF HFr HG.
  annt_chunk HS 1%nat 240 U9 dp Ddp VP.
  annt_chunk HS 1%nat 248 U9 (TI.tf_addr fr + 30) Dp VB.
  annt_chunk HS 2%nat 24 U19 1 (@eq_refl _ (Z_to_bv 64 1)) VF.
  annt_chunk HS 2%nat 20 U19 (TW.u_at (annt_B2 Bwc off) TW.A_M_e1_us 4) D34 VE.
  annt_chunk HS 0%nat 212 U9 (TW.OW_foreign (annt_B2 Bwc off) + 1) Dfo VO.
  assert (HWF : tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms)) (annt_B7 (annt_B4 fr Bwc off dp))).
  { unfold annt_B7. rewrite (annt_fo5 fr Bwc off dp LB). unfold annt_B4.
    apply (annt_w_neg (annt_B2 Bwc off) dp (TI.tf_addr fr + 30) (TW.OW_foreign (annt_B2 Bwc off) + 1)
      (aview tfibsegs (w_H W3) mem3) _ HW3 VP VB VF VO).
    intros x Hx N1 N2 N3. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    assert (Hd : annt_w2 x \/ ~ annt_w2 x) by (unfold annt_w2; lia).
    destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
    unfold annt_w2 in Hw.
    exact (annt_keep4 _ _ _ TW.OFF_M TA_M TW.SZ_M 20 _ HW3 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
      eq_refl VE x ltac:(unfold TA_OW, TA_M in *; lia)). }
  annt_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  annt_reg HS (Z_to_bv 5 10) (w64 5) Q10' ltac:(reflexivity).
  pmkst HS. annt_pc (MRX_PC OFF_LOST).
  apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold annt_w2, TA_OW, TA_M; lia)) Q2 Q3 Q4 HWF KLOST).
  unfold R_LOST. exists 5, B3. split; [exact Q10'|]. split; [lia|]. split; [exact HL7|].
  split; [exact Htk | exact Hr1]. }
(* M.state is neither: the cut TICK *)
rewrite Dw in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (EPI.mrx_state12 (TW.M_state Bwc) Sst) in Hc.
apply negb_true_iff in Hc.
destruct HM7 as [(Hs & _) | (_ & HB7)]; [rewrite Hc in Hs; discriminate Hs|].
paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_TICK).
{ annt_awr2 U9 U19. }
annt_md.
assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ annt_w2 a ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- (KA4 a Ha Hn). apply (kept_of_frame _ _ _ _ _ annt_w2 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. annt_win Hin Hx ltac:(rewrite ?U9, ?U19 in Hx; unfold annt_w2; lia). }
clear HF HFr HG.
annt_chunk HS 1%nat 240 U9 dp Ddp VP.
annt_chunk HS 1%nat 248 U9 (TI.tf_addr fr + 30) Dp VB.
annt_chunk HS 2%nat 24 U19 1 (@eq_refl _ (Z_to_bv 64 1)) VF.
annt_chunk HS 2%nat 20 U19 (TW.u_at (annt_B2 Bwc off) TW.A_M_e1_us 4) D34 VE.
annt_chunk HS 0%nat 212 U9 (TW.OW_foreign (annt_B2 Bwc off) + 1) Dfo VO.
assert (HWF : tw_at TMAP_A (aview tfibsegs (w_H W3) (ms_mem ms)) (annt_B7 (annt_B4 fr Bwc off dp))).
{ unfold annt_B7. rewrite (annt_fo5 fr Bwc off dp LB). unfold annt_B4.
  apply (annt_w_neg (annt_B2 Bwc off) dp (TI.tf_addr fr + 30) (TW.OW_foreign (annt_B2 Bwc off) + 1)
    (aview tfibsegs (w_H W3) mem3) _ HW3 VP VB VF VO).
  intros x Hx N1 N2 N3. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  assert (Hd : annt_w2 x \/ ~ annt_w2 x) by (unfold annt_w2; lia).
  destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
  unfold annt_w2 in Hw.
  exact (annt_keep4 _ _ _ TW.OFF_M TA_M TW.SZ_M 20 _ HW3 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
    eq_refl VE x ltac:(unfold TA_OW, TA_M in *; lia)). }
annt_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
annt_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
annt_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pmkst HS. annt_pc (MRX_PC OFF_TICK).
apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold annt_w2, TA_OW, TA_M; lia)) Q2 Q3 Q4 HWF KT).
unfold R_TICK. split; [rewrite <- HB7; exact Htk | exact Hr1].
Qed.

End seg.
