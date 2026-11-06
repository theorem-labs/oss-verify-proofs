(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 807 of its 901 lines of code are new or changed and 936 lines of the source are left out. *)
(* m_rx_seg_ann2: two segment lemmas of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v; listing lib/B/Prog/DgnTransportBList.v after AF_m_rx), the tails of cmd e0 and cmd e1
   after the desk fields. Each is `K (successor cuts) -> K (its cut)`: from a machine the cut describes, symbolic runs
   over the inner G journal (TransportGRunB.v paj_run_x / paj_run_to_x) reach a successor cut, whose mrx_at is built
   with the kit's mrx_at_intro.

   mrx_seg_e0, the cut E0 (+0x350 .. +0x36c; model UMR.mr_e0, split by ann2_e0_model): a0 = M.state, M.foreign = 0;
   `bne a0, 2` goes to the cut E0W (the world after the store, whose M.state is the old one, EPI.mrx_e0w); else the
   two stores of the inlined m_lost (M.desk_counter_valid = 0, M.fly_on = 0), a1 = 3 (R_DESK_OFFLINE) and the cut
   E0L (TC.m_lost_m is m_set_m of the world after those stores).
   mrx_seg_e1, the cut E1 (+0x390 .. ; model UMR.mr_e1, split by ann2_e1_model): `bltz s0`; off >= 0: M.e1_us = 1,
   M.foreign = 0, the cut MO; off < 0: a2 = OW.foreign, M.foreign = 1, `blt (OW.foreign + 1), OW.foreign` (the trap
   word +0x3e4, refuted: the model's int_inc of OW.foreign is not None), OW.foreign + 1 stored, `bltu 1, M.state - 1`
   goes to the cut TICK (M.state neither S_ONLINE nor S_WAKING); else M.desk_counter_valid = 0, M.fly_on = 0,
   a1 = 5 (R_FOREIGN) and the cut SET.
   Regions: 4-byte fields of M (based at s1) and of OW (based at s2), writable bytes of G (ann2_inG) except M.state
   (read-only). Each field a path may leave unstored holds the world's 4 bytes as an atom of the valuation ann2_E, so
   after a run it still holds them (ann2_keep4). The world at each cut is one TWorld.upd per store (kit mrx_tw_step,
   the ann2_w lemmas). No instrumented check is on these paths. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_annt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_annt.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the symbolic states ---- *)

(* Atoms 0 .. 31: the registers at the cut; 32 .. 36: the world's 4 bytes of M.e1_us, M.state,
   M.desk_counter_valid, M.fly_on and OW.foreign (unsigned ints). *)
Definition ann2_extra (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw TW.A_M_e1_us 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_M_desk_counter_valid 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_fly_on 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_OW_foreign 4)].

(* The fields: M.e1_us (M + 0x14), M.foreign (M + 0x18), M.state (M + 0xc, read-only), M.desk_counter_valid
   (M + 0x4c), M.fly_on (M + 0x60), based at s1 (atom 9); OW.foreign (OW + 0xd4), based at s2 (atom 18). *)
Definition ann2_r_e1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x14 0x18 0x14 0x18 [YP09.mkChunk 0x14 (YP09.CVal 4 (SOff 32 0))].
Definition ann2_r_fo : YP09.region := YP09.mkRegion (Some 9%nat) 0x18 0x1c 0x18 0x1c [].
Definition ann2_r_st : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc 0x10 0 0 [YP09.mkChunk 0xc (YP09.CVal 4 (SOff 33 0))].
Definition ann2_r_dcv : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x4c 0x50 0x4c 0x50 [YP09.mkChunk 0x4c (YP09.CVal 4 (SOff 34 0))].
Definition ann2_r_fly : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x60 0x64 0x60 0x64 [YP09.mkChunk 0x60 (YP09.CVal 4 (SOff 35 0))].
Definition ann2_r_ofo : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0xd4 0xd8 0xd4 0xd8 [YP09.mkChunk 0xd4 (YP09.CVal 4 (SOff 36 0))].
Definition ann2_facts0 : facts :=
  mkFacts [(9%nat, mkAF TB_M TB_M 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ann2_facts1 : facts :=
  mkFacts [(9%nat, mkAF TB_M TB_M 5); (18%nat, mkAF TB_OW TB_OW 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (36%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_e0 : sstate :=
  mkSS (AF_m_rx + OFF_E0) sr_atoms [ann2_r_st; ann2_r_fo; ann2_r_dcv; ann2_r_fly] None ann2_facts0.
Definition ss_e1 : sstate :=
  mkSS (AF_m_rx + OFF_E1) sr_atoms [ann2_r_e1; ann2_r_fo; ann2_r_st; ann2_r_dcv; ann2_r_fly; ann2_r_ofo] None
    ann2_facts1.
Definition ANN2_SH : list shent := [].
Definition ANN2_Bx : sv := SLit 0.

(* A byte of M's or OW's payload is a byte of G. *)
Lemma ann2_inG : forall a, (TB_M <= a < TB_M + 1648) \/ (TB_OW <= a < TB_OW + 304) -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TB_M, TW.SZ_M). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TB_OW, TW.SZ_OW). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Definition ann2_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (ann2_extra Bw)).

(* The entry state of E0: s1 = &M; M.state, M.desk_counter_valid and M.fly_on hold the world's bytes. *)
Lemma ann2_entry0 : forall (Wc : world tfibsegs) regs mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H Wc) mem) Bw ->
  YK11.getr regs 9 = w64 TB_M ->
  st_ok_pi tfibsegs VAL (ann2_E regs Bw) ss_e0
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_E0))) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw Htw H9.
  set (E := ann2_E regs Bw).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (E9 : ew E 9 = Z_to_bv 64 TB_M)
    by (unfold E, ann2_E; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (B9 : base_val E (Some 9%nat) = TB_M) by (apply VB; [exact E9 | unfold TB_M; lia]).
  assert (U9 : bv_unsigned (ew E 9) = TB_M) by exact B9.
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ann2_extra Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ann2_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth ann2_extra] in E32, E33, E34, E35, E36.
  pose proof (TWL.u_at_range Bw TW.A_M_e1_us 4) as R32. pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R33.
  pose proof (TWL.u_at_range Bw TW.A_M_desk_counter_valid 4) as R34.
  pose proof (TWL.u_at_range Bw TW.A_M_fly_on 4) as R35. pose proof (TWL.u_at_range Bw TW.A_OW_foreign 4) as R36.
  change (8 * Z.of_nat 4) with 32 in R32, R33, R34, R35, R36.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_e0.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold ann2_r_st, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0xc 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0xc 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_fo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_nil.
    + unfold ann2_r_dcv, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0x4c 4 (SOff 34 0) (TW.u_at Bw TW.A_M_desk_counter_valid 4));
        [apply DEN; [exact E34 | lia] | exact R34 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0x4c 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_fly, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0x60 4 (SOff 35 0) (TW.u_at Bw TW.A_M_fly_on 4));
        [apply DEN; [exact E35 | lia] | exact R35 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0x60 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  - unfold ann2_r_st, ann2_r_fo, ann2_r_dcv, ann2_r_fly.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9.
    unfold TB_M. repeat split; lia.
  - unfold ann2_facts0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32, E33, E34, E35, E36.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_e1_us 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_desk_counter_valid 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_fly_on 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_OW_foreign 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* The entry state of E1: s1 = &M, s2 = &OW; M.e1_us, M.state, M.desk_counter_valid, M.fly_on and OW.foreign hold
   the world's bytes. *)
Lemma ann2_entry1 : forall (Wc : world tfibsegs) regs mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H Wc) mem) Bw ->
  YK11.getr regs 9 = w64 TB_M -> YK11.getr regs 18 = w64 TB_OW ->
  st_ok_pi tfibsegs VAL (ann2_E regs Bw) ss_e1
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_E1))) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw Htw H9 H18.
  set (E := ann2_E regs Bw).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (E9 : ew E 9 = Z_to_bv 64 TB_M)
    by (unfold E, ann2_E; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E18 : ew E 18 = Z_to_bv 64 TB_OW)
    by (unfold E, ann2_E; rewrite (ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (B9 : base_val E (Some 9%nat) = TB_M) by (apply VB; [exact E9 | unfold TB_M; lia]).
  assert (B18 : base_val E (Some 18%nat) = TB_OW) by (apply VB; [exact E18 | unfold TB_OW; lia]).
  assert (U9 : bv_unsigned (ew E 9) = TB_M) by exact B9.
  assert (U18 : bv_unsigned (ew E 18) = TB_OW) by exact B18.
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ann2_extra Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ann2_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth ann2_extra] in E32, E33, E34, E35, E36.
  pose proof (TWL.u_at_range Bw TW.A_M_e1_us 4) as R32. pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R33.
  pose proof (TWL.u_at_range Bw TW.A_M_desk_counter_valid 4) as R34.
  pose proof (TWL.u_at_range Bw TW.A_M_fly_on 4) as R35. pose proof (TWL.u_at_range Bw TW.A_OW_foreign 4) as R36.
  change (8 * Z.of_nat 4) with 32 in R32, R33, R34, R35, R36.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_e1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + unfold ann2_r_e1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0x14 4 (SOff 32 0) (TW.u_at Bw TW.A_M_e1_us 4));
        [apply DEN; [exact E32 | lia] | exact R32 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0x14 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_fo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_nil.
    + unfold ann2_r_st, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0xc 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0xc 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_dcv, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0x4c 4 (SOff 34 0) (TW.u_at Bw TW.A_M_desk_counter_valid 4));
        [apply DEN; [exact E34 | lia] | exact R34 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0x4c 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_fly, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_M 0x60 4 (SOff 35 0) (TW.u_at Bw TW.A_M_fly_on 4));
        [apply DEN; [exact E35 | lia] | exact R35 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0x60 4 TMAP_B_ok Htw TMAP_B_M
        ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold ann2_r_ofo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B18.
      split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw);
              apply ann2_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_OW 0xd4 4 (SOff 36 0) (TW.u_at Bw TW.A_OW_foreign 4));
        [apply DEN; [exact E36 | lia] | exact R36 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 0xd4 4 TMAP_B_ok Htw TMAP_B_OW
        ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
  - unfold ann2_r_e1, ann2_r_fo, ann2_r_st, ann2_r_dcv, ann2_r_fly, ann2_r_ofo.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9, B18.
    unfold TB_M, TB_OW. repeat split; lia.
  - unfold ann2_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, E32, E33, E34, E35, E36.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_e1_us 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_desk_counter_valid 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_fly_on 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_OW_foreign 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.
End h.

(* ---- the model ---- *)

(* A world field read as its bytes. *)
Lemma ann2_st_def : forall Bw, TW.M_state Bw = bv_swrap 32 (TW.u_at Bw TW.A_M_state 4).
Proof. intros Bw. reflexivity. Qed.
Lemma ann2_fo_def : forall Bw, TW.OW_foreign Bw = bv_swrap 32 (TW.u_at Bw TW.A_OW_foreign 4).
Proof. intros Bw. reflexivity. Qed.

(* The world after cmd e1's stores with off < 0: M.foreign = 1, OW.foreign + 1. *)
Definition ann2_B6 (Bw : list byte) : list byte :=
  TW.set_OW_foreign (TW.set_M_foreign Bw 1) (TW.OW_foreign Bw + 1).

(* Reads of the worlds through the stores elsewhere. *)
Lemma ann2_st5 : forall Bw v, Z.of_nat (length Bw) = 65616 -> TW.M_state (TW.set_M_foreign Bw v) = TW.M_state Bw.
Proof. intros Bw v L. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.
Lemma ann2_fo1 : forall Bw, Z.of_nat (length Bw) = 65616 -> TW.OW_foreign (TW.set_M_foreign Bw 1) = TW.OW_foreign Bw.
Proof. intros Bw L. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.
Lemma ann2_st6 : forall Bw, Z.of_nat (length Bw) = 65616 -> TW.M_state (ann2_B6 Bw) = TW.M_state Bw.
Proof. intros Bw L. unfold ann2_B6. EPI.mrx_unf. EPI.mrx_rw. reflexivity. Qed.

(* cmd e0 (UMR.mr_e0): M.state S_ONLINE gives the inlined m_lost (m_set_m after its two stores), then mrx_e0w;
   else mrx_e0w of the world after M.foreign = 0. *)
Lemma ann2_e0_model : forall Bw B3, Z.of_nat (length Bw) = 65616 -> UMR.mr_e0 Bw = Some (B3, tt) ->
  (TW.M_state Bw = 2 /\ exists B6,
     TC.m_set_m (TW.set_M_desk_counter_valid (TW.set_M_fly_on (TW.set_M_foreign Bw 0) 0) 0) TC.S_IDLE 3 =
       Some (B6, tt) /\ EPI.mrx_e0w B6 = Some (B3, tt)) \/
  (TW.M_state Bw <> 2 /\ EPI.mrx_e0w (TW.set_M_foreign Bw 0) = Some (B3, tt)).
Proof.
intros Bw B3 L H. unfold UMR.mr_e0 in H. cbv zeta in H.
rewrite (ann2_st5 Bw 0 L) in H. unfold TC.S_ONLINE, TC.m_lost_m, TC.R_DESK_OFFLINE in H.
destruct (Z.eqb_spec (TW.M_state Bw) 2) as [E|E]; cbv beta iota in H.
- left. split; [exact E|].
  destruct (TC.m_set_m (TW.set_M_desk_counter_valid (TW.set_M_fly_on (TW.set_M_foreign Bw 0) 0) 0) TC.S_IDLE 3)
    as [[B6 []]|] eqn:L6; cbv beta iota in H; [|discriminate H].
  exists B6. split; [reflexivity | exact H].
- right. split; [exact E | exact H].
Qed.

(* cmd e1 (UMR.mr_e1): off >= 0, M.e1_us and M.foreign, then m_maybe_online; off < 0, OW.foreign + 1 (not at
   INT_MAX), and the inlined m_lost (m_set_m after its two stores, why = R_FOREIGN) when M.state is S_ONLINE or
   S_WAKING. *)
Lemma ann2_e1_model : forall Bw off B3, Z.of_nat (length Bw) = 65616 -> UMR.mr_e1 off Bw = Some (B3, tt) ->
  (0 <= off /\ TC.m_maybe_online_m (TW.set_M_e1_us (TW.set_M_foreign Bw 0) 1) = Some (B3, tt)) \/
  (off < 0 /\ TW.OW_foreign Bw <> TC.INT_MAX /\
   ((((TW.M_state Bw =? 2) || (TW.M_state Bw =? 1)) = true /\
     TC.m_set_m (TW.set_M_desk_counter_valid (TW.set_M_fly_on (ann2_B6 Bw) 0) 0) TC.S_IDLE 5 = Some (B3, tt)) \/
    (((TW.M_state Bw =? 2) || (TW.M_state Bw =? 1)) = false /\ B3 = ann2_B6 Bw))).
Proof.
intros Bw off B3 L H. unfold UMR.mr_e1, TC.int_inc in H. cbv zeta in H.
destruct (Z.leb_spec 0 off) as [P|N]; cbv beta iota in H.
- left. split; [exact P | exact H].
- right. split; [exact N|].
  rewrite (ann2_fo1 Bw L) in H.
  destruct (TW.OW_foreign Bw =? TC.INT_MAX) eqn:IF; cbv beta iota in H; [discriminate H|].
  split; [apply Z.eqb_neq; exact IF|].
  change (TW.set_OW_foreign (TW.set_M_foreign Bw 1) (TW.OW_foreign Bw + 1)) with (ann2_B6 Bw) in H.
  rewrite (ann2_st6 Bw L) in H. unfold TC.S_ONLINE, TC.S_WAKING, TC.m_lost_m, TC.R_FOREIGN in H.
  destruct ((TW.M_state Bw =? 2) || (TW.M_state Bw =? 1)) eqn:SO; cbv beta iota in H.
  + left. split; [reflexivity | exact H].
  + right. split; [reflexivity | exact (eq_sym (proj1 (mrx_some_inv _ _ _ _ _ _ H)))].
Qed.

(* ---- the world relation after the stores of the segment ---- *)

(* The fields the runs may store. *)
Definition ann2_w0 (a : Z) : Prop :=
  (TB_M + 24 <= a < TB_M + 28) \/ (TB_M + 76 <= a < TB_M + 80) \/ (TB_M + 96 <= a < TB_M + 100).
Definition ann2_w1 (a : Z) : Prop :=
  (TB_M + 20 <= a < TB_M + 28) \/ (TB_M + 76 <= a < TB_M + 80) \/ (TB_M + 96 <= a < TB_M + 100) \/
  (TB_OW + 212 <= a < TB_OW + 216).

(* A 4-byte field a path did not store still holds the world's bytes. *)
Lemma ann2_keep4 : forall rd0 rdF Bw o b n k u,
  tw_at TMAP_B rd0 Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + 4 <= n -> u = TW.u_at Bw (o + k) 4 ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte u 4 j)) ->
  forall x, b + k <= x < b + k + 4 -> rdF x = rd0 x.
Proof.
intros rd0 rdF Bw o b n k u Htw Hin Hk Hkn -> HV x Hx.
replace x with (b + k + Z.of_nat (Z.to_nat (x - (b + k)))) by lia.
rewrite (HV (Z.to_nat (x - (b + k))) ltac:(lia)).
rewrite (tw_read TMAP_B rd0 Bw o b n k 4 (Z.to_nat (x - (b + k))) TMAP_B_ok Htw Hin Hk
  ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) ltac:(lia)).
reflexivity.
Qed.

(* E0W: M.foreign = 0. *)
Lemma ann2_w_e0w : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 24 <= x < TB_M + 28) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_foreign Bw 0).
Proof.
intros Bw rd0 rdF Htw VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold TW.set_M_foreign.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 24 TW.A_M_foreign 4 0 H0 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H1.
apply (mrx_tw_end rdF rd0 _ _ H1). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia].
Qed.

(* E0L: M.foreign = 0, M.fly_on = 0, M.desk_counter_valid = 0. *)
Lemma ann2_w_e0l : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 24 <= x < TB_M + 28) -> ~ (TB_M + 96 <= x < TB_M + 100) ->
     ~ (TB_M + 76 <= x < TB_M + 80) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_desk_counter_valid (TW.set_M_fly_on (TW.set_M_foreign Bw 0) 0) 0).
Proof.
intros Bw rd0 rdF Htw VF VY VD Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.set_M_foreign.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 24 TW.A_M_foreign 4 0 H0 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H1 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VY) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 76 TW.A_M_desk_counter_valid 4 0 H2 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VD) as H3.
apply (mrx_tw_end rdF rd0 _ _ H3). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* MO: M.foreign = 0, M.e1_us = 1. *)
Lemma ann2_w_mo : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 20 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 20 <= x < TB_M + 28) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_e1_us (TW.set_M_foreign Bw 0) 1).
Proof.
intros Bw rd0 rdF Htw VF VE Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold TW.set_M_e1_us, TW.set_M_foreign.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 24 TW.A_M_foreign 4 0 H0 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 20 TW.A_M_e1_us 4 1 H1 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VE) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia].
Qed.

(* TICK (off < 0): M.foreign = 1, OW.foreign = v. *)
Lemma ann2_w_tick : forall Bw v rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 212 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 24 <= x < TB_M + 28) -> ~ (TB_OW + 212 <= x < TB_OW + 216) ->
     rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_OW_foreign (TW.set_M_foreign Bw 1) v).
Proof.
intros Bw v rd0 rdF Htw VF VO Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_OW_foreign, TW.set_M_foreign.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 24 TW.A_M_foreign 4 1 H0 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 212 TW.A_OW_foreign 4 v H1 TMAP_B_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VO) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia].
Qed.

(* SET (off < 0, M.state S_ONLINE or S_WAKING): M.foreign = 1, OW.foreign = v, M.fly_on = 0,
   M.desk_counter_valid = 0. *)
Lemma ann2_w_set : forall Bw v rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 24 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 212 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 24 <= x < TB_M + 28) -> ~ (TB_OW + 212 <= x < TB_OW + 216) ->
     ~ (TB_M + 96 <= x < TB_M + 100) -> ~ (TB_M + 76 <= x < TB_M + 80) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF
    (TW.set_M_desk_counter_valid (TW.set_M_fly_on (TW.set_OW_foreign (TW.set_M_foreign Bw 1) v) 0) 0).
Proof.
intros Bw v rd0 rdF Htw VF VO VY VD Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.set_OW_foreign, TW.set_M_foreign.
pose proof (mrx_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 24 TW.A_M_foreign 4 1 H0 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VF) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 212 TW.A_OW_foreign 4 v H1 TMAP_B_OW eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VO) as H2.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 TW.A_M_fly_on 4 0 H2 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VY) as H3.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 76 TW.A_M_desk_counter_valid 4 0 H3 TMAP_B_M eq_refl
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) VD) as H4.
apply (mrx_tw_end rdF rd0 _ _ H4). intros x Hx HP. mrx_unP HP. cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; [exact Hx | lia | lia | lia | lia].
Qed.

(* ---- tactics ---- *)

(* The bytes of the chunk at offset off of region idx of the state of HS, base rewritten by UB: forall j < width,
   the view at base + off + j is le_byte v width j, for Hden : sv_denot E e = Z_to_bv 64 v. *)
Ltac ann2_chunk HS idx off UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF ?ss (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG;
    let cs := eval vm_compute in (YP09.r_chunks (nth idx (ss_mem ss) ann2_r_fo)) in
    let c := eval vm_compute in (AN.annt_find off cs) in
    cbn [ms_mem restrict] in RG;
    destruct RG as (_ & _ & _ & HC);
    cbn [YP09.r_base YP09.r_chunks base_val] in HC;
    rewrite UB in HC;
    pose proof (AN.annt_Forall_nth _ _ c _ HC eq_refl) as HC1;
    pose proof (mrx_chunk_rd _ _ _ _ _ _ _ v HC1 Hden ltac:(cbn; lia)) as V;
    clear HC HC1
  end.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ann2_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ann2_reg: no match for" T; fail
  end.

(* The windows a run wrote, computed, each case closed by tac. *)
Ltac ann2_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run whose writable bytes lie in M or OW (bytes of G). *)
Ltac ann2_awr U9 U18 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9, ?U18 in Ha;
      apply ann2_inG; unfold TB_M, TB_OW in *; lia |]);
  apply awr_ok_x_nil.

(* After a run: the model generalized. *)
Ltac ann2_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md := fresh "mdw" in set (md := mdx) in *; clearbody md end.

(* The pc of the current machine state, renamed to a cut's pc. *)
Ltac ann2_pc pc :=
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?pcx) _ _) _) _ =>
    replace pcx with pc by (vm_compute; reflexivity) end.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
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

Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mrx_seg_e0 : K (MRX_PC OFF_E0L) (R_E0L Bw' r) -> K (MRX_PC OFF_E0W) (R_E0W Bw' r) ->
  K (MRX_PC OFF_E0) (R_E0 Bw' r).
Proof using All.
intros KL KW. unfold mrx_K. intros Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsaved & Htw & HR).
destruct HR as (B3 & H9 & He0 & Htk & Hr1).
pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (MSV : MRX_STK = 8384) by reflexivity.
assert (LB : Z.of_nat (length Bwc) = 65616)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
set (E0 := ann2_E regs2 Bwc).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ann2_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn0; unfold E0, ann2_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (AG : env_agree 32 (Ereg regs2 (ann2_extra Bwc)) E0)
  by (split; [intros m Hm; unfold E0, ann2_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E0 9 = Z_to_bv 64 TB_M) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (U9 : bv_unsigned (ew E0 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; unfold TB_M; lia).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (ann2_extra Bwc) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ann2_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth ann2_extra] in E33, E34, E35.
pose proof (TWL.u_at_range Bwc TW.A_M_state 4) as R33.
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter_valid 4) as R34.
pose proof (TWL.u_at_range Bwc TW.A_M_fly_on 4) as R35.
change (8 * Z.of_nat 4) with 32 in R33, R34, R35.
assert (DEN : forall n0 v, ew E0 n0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E0 (SOff n0 0) = Z_to_bv 64 v)
  by (intros n0 v Hn0 Hv; cbn [sv_denot]; rewrite Hn0, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bwc))
  by (rewrite (AN.annt_sext E0 33 _ E33 R33), <- ann2_st_def; reflexivity).
assert (D34 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4))
  by (apply DEN; [exact E34 | lia]).
assert (D35 : sv_denot E0 (SOff 35 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_M_fly_on 4))
  by (apply DEN; [exact E35 | lia]).
pose proof (TWL.s32_range Bwc TW.A_M_state) as Sst.
change (TW.s32_at Bwc TW.A_M_state) with (TW.M_state Bwc) in Sst.
pose proof (ann2_entry0 Wc regs2 mem2 Bwc Htw H9) as HS. fold E0 in HS.
assert (SHOK : sh_ok tfibsegs ANN2_Bx ANN2_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, ANN2_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* the end of a run at a cut: the common facts of mrx_at *)
assert (CL : forall ms md pc R Bx,
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2
    Wc (ms_mem ms) md 0 ->
  (forall a, sp1 - 32 <= a < sp1 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a) ->
  aregs_preserved regs2 (ms_regs ms) ->
  tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) Bx ->
  K pc R -> R Wc Bx ly2 S2 (ms_regs ms) (ms_mem ms) ->
  SRr tfibsegs Wc (mkCfg (@YK11.mkst fx (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (YK11.seg_rom tfibsegs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r)).
{ intros ms md pc R Bx HJx KS HP HWx KX HRx.
  apply (KX Wc Bx).
  apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bx ly2 S2).
  - exact HJx.
  - exact Hfr.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) Hsp).
  - exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) Hgp).
  - exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) Htp).
  - intros q Hq. exact (eq_trans (HP q ltac:(unfold acallee_saved; lia)) (Hhi q Hq)).
  - exact (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 Hsaved KS).
  - exact HWx.
  - exact HRx. }
replace (MRX_PC OFF_E0) with (BASE + (AF_m_rx + OFF_E0)) by (vm_compute; reflexivity).
(* run 1, +0x350 .. +0x35c: a0 = M.state, a1 = 2, M.foreign = 0; it stops at `bne a0, a1`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ann2_awr U9 U9. }
ann2_md. rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w0 a ->
  aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ann2_w0 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9 in Hx; unfold ann2_w0; lia). }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state <> S_ONLINE: the cut E0W *)
  rewrite D33 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 2 ltac:(lia) ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  destruct (ann2_e0_model Bwc B3 LB He0) as [(Hon & _) | (_ & HE5)]; [exfalso; exact (Hc Hon)|].
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_E0W).
  { ann2_awr U9 U9. }
  ann2_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w0 a ->
    aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha Hn. rewrite <- (KA1 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ann2_w0 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9 in Hx; unfold ann2_w0; lia). }
  clear HF HFr HG.
  ann2_chunk HS 1%nat 24 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  ann2_chunk HS 2%nat 76 U9 (TW.u_at Bwc TW.A_M_desk_counter_valid 4) D34 VD.
  ann2_chunk HS 3%nat 96 U9 (TW.u_at Bwc TW.A_M_fly_on 4) D35 VY.
  assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) (TW.set_M_foreign Bwc 0)).
  { apply (ann2_w_e0w Bwc (aview tfibsegs (w_H Wc) mem2) _ Htw VF).
    intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    assert (Hd : ann2_w0 x \/ ~ ann2_w0 x) by (unfold ann2_w0; lia).
    destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
    unfold ann2_w0 in Hw. destruct (Z_lt_le_dec x (TB_M + 80)) as [Lx | Lx].
    - exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 76 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
        eq_refl VD x ltac:(unfold TB_M in *; lia)).
    - exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 96 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
        eq_refl VY x ltac:(unfold TB_M in *; lia)). }
  ann2_reg HS (Z_to_bv 5 10) (w64 (TW.M_state (TW.set_M_foreign Bwc 0))) Q10
    ltac:(rewrite D33, (ann2_st5 Bwc 0 LB); reflexivity).
  assert (HP : aregs_preserved regs2 (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wc) E0 _ ms regs2 (ann2_extra Bwc) HS AG);
        vm_compute; reflexivity).
  pmkst HS. ann2_pc (MRX_PC OFF_E0W).
  apply (CL ms _ _ _ _ HJ (fun a Ha => KAF a ltac:(lia) ltac:(unfold ann2_w0, TB_M; lia)) HP HWF KW).
  unfold R_E0W. exists B3. split; [exact Q10|]. split; [exact HE5|]. split; [exact Htk | exact Hr1].
- (* M.state = S_ONLINE: the inlined m_lost's stores, a1 = 3, the cut E0L *)
  rewrite D33 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 2 ltac:(lia) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  destruct (ann2_e0_model Bwc B3 LB He0) as [(_ & B6 & HL6 & HE6) | (Hn2 & _)]; [| exfalso; exact (Hn2 Hc)].
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_E0L).
  { ann2_awr U9 U9. }
  ann2_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w0 a ->
    aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha Hn. rewrite <- (KA1 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ann2_w0 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9 in Hx; unfold ann2_w0; lia). }
  clear HF HFr HG.
  ann2_chunk HS 1%nat 24 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  ann2_chunk HS 2%nat 76 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VD.
  ann2_chunk HS 3%nat 96 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VY.
  assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms))
    (TW.set_M_desk_counter_valid (TW.set_M_fly_on (TW.set_M_foreign Bwc 0) 0) 0)).
  { apply (ann2_w_e0l Bwc (aview tfibsegs (w_H Wc) mem2) _ Htw VF VY VD).
    intros x Hx N1 N2 N3. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    exact (KAF x ltac:(lia) ltac:(unfold ann2_w0; lia)). }
  ann2_reg HS (Z_to_bv 5 11) (w64 3) Q11 ltac:(reflexivity).
  assert (HP : aregs_preserved regs2 (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wc) E0 _ ms regs2 (ann2_extra Bwc) HS AG);
        vm_compute; reflexivity).
  assert (Q9 : YK11.getr (ms_regs ms) 9 = w64 TB_M)
    by exact (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) H9).
  pmkst HS. ann2_pc (MRX_PC OFF_E0L).
  apply (CL ms _ _ _ _ HJ (fun a Ha => KAF a ltac:(lia) ltac:(unfold ann2_w0, TB_M; lia)) HP HWF KL).
  unfold R_E0L. exists B6, B3. split; [exact Q9|]. split; [exact Q11|]. split; [exact HL6|].
  split; [exact HE6|]. split; [exact Htk | exact Hr1].
Qed.

Lemma mrx_seg_e1 : K (MRX_PC OFF_MO) (R_MO Bw' r) -> K (MRX_PC OFF_SET) (R_SET Bw' r) ->
  K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_E1) (R_E1 Bw' r).
Proof using All.
intros KMO KSET KT. unfold mrx_K. intros Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsaved & Htw & HR).
destruct HR as (off & B3 & Hoff & H8 & H9 & H18 & He1 & Htk & Hr1).
pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (MSV : MRX_STK = 8384) by reflexivity.
assert (LB : Z.of_nat (length Bwc) = 65616)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
set (E0 := ann2_E regs2 Bwc).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ann2_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn0; unfold E0, ann2_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (AG : env_agree 32 (Ereg regs2 (ann2_extra Bwc)) E0)
  by (split; [intros m Hm; unfold E0, ann2_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E0 9 = Z_to_bv 64 TB_M) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (U9 : bv_unsigned (ew E0 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; unfold TB_M; lia).
assert (E18 : ew E0 18 = Z_to_bv 64 TB_OW) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (U18 : bv_unsigned (ew E0 18) = TB_OW) by (rewrite E18; apply unsigned_lit_small; unfold TB_OW; lia).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (ann2_extra Bwc) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ann2_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth ann2_extra] in E32, E33, E34, E35, E36.
pose proof (TWL.u_at_range Bwc TW.A_M_e1_us 4) as R32. pose proof (TWL.u_at_range Bwc TW.A_M_state 4) as R33.
pose proof (TWL.u_at_range Bwc TW.A_M_desk_counter_valid 4) as R34.
pose proof (TWL.u_at_range Bwc TW.A_M_fly_on 4) as R35.
pose proof (TWL.u_at_range Bwc TW.A_OW_foreign 4) as R36.
change (8 * Z.of_nat 4) with 32 in R32, R33, R34, R35, R36.
assert (DEN : forall n0 v, ew E0 n0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E0 (SOff n0 0) = Z_to_bv 64 v)
  by (intros n0 v Hn0 Hv; cbn [sv_denot]; rewrite Hn0, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
assert (D32 : sv_denot E0 (SOff 32 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_M_e1_us 4)) by (apply DEN; [exact E32 | lia]).
assert (D34 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_M_desk_counter_valid 4))
  by (apply DEN; [exact E34 | lia]).
assert (D35 : sv_denot E0 (SOff 35 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_M_fly_on 4)) by (apply DEN; [exact E35 | lia]).
assert (D36 : sv_denot E0 (SOff 36 0) = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_foreign 4)) by (apply DEN; [exact E36 | lia]).
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bwc))
  by (rewrite (AN.annt_sext E0 33 _ E33 R33), <- ann2_st_def; reflexivity).
assert (D36f : sv_denot E0 (SExt true 32 (SOff 36 0)) = Z_to_bv 64 (TW.OW_foreign Bwc))
  by (rewrite (AN.annt_sext E0 36 _ E36 R36), <- ann2_fo_def; reflexivity).
assert (Doff : sv_denot E0 (SOff 8 0) = Z_to_bv 64 off)
  by (cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8).
pose proof (TWL.s32_range Bwc TW.A_M_state) as Sst.
change (TW.s32_at Bwc TW.A_M_state) with (TW.M_state Bwc) in Sst.
pose proof (TWL.s32_range Bwc TW.A_OW_foreign) as Sfo.
change (TW.s32_at Bwc TW.A_OW_foreign) with (TW.OW_foreign Bwc) in Sfo.
(* the code's OW.foreign + 1 (addiw) and M.state - 1 (addiw) *)
assert (Da1 : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (TW.OW_foreign Bwc)) + 1))).
{ change (sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)))
    with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E0 (SExt true 32 (SOff 36 0)))) (low32 (sv_denot E0 (SLit 1))))).
  rewrite D36f. change (sv_denot E0 (SLit 1)) with (Z_to_bv 64 1).
  exact (YK1g.aluw_addi_lit (Z_to_bv 64 (TW.OW_foreign Bwc)) 1). }
rewrite UMR.mr_swrap32_lit_add in Da1.
assert (Dw : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))) =
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (TW.M_state Bwc)) + -1))).
{ change (sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))))
    with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E0 (SExt true 32 (SOff 33 0)))) (low32 (sv_denot E0 (SLit (-1)))))).
  rewrite D33. change (sv_denot E0 (SLit (-1))) with (Z_to_bv 64 (-1)).
  exact (YK1g.aluw_addi_lit (Z_to_bv 64 (TW.M_state Bwc)) (-1)). }
pose proof (ann2_entry1 Wc regs2 mem2 Bwc Htw H9 H18) as HS. fold E0 in HS.
assert (SHOK : sh_ok tfibsegs ANN2_Bx ANN2_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, ANN2_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* the end of a run at a cut: the common facts of mrx_at *)
assert (CL : forall ms md pc R Bx,
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2
    Wc (ms_mem ms) md 0 ->
  (forall a, sp1 - 32 <= a < sp1 -> aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a) ->
  aregs_preserved regs2 (ms_regs ms) ->
  tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) Bx ->
  K pc R -> R Wc Bx ly2 S2 (ms_regs ms) (ms_mem ms) ->
  SRr tfibsegs Wc (mkCfg (@YK11.mkst fx (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (YK11.seg_rom tfibsegs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r)).
{ intros ms md pc R Bx HJx KS HP HWx KX HRx.
  apply (KX Wc Bx).
  apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bx ly2 S2).
  - exact HJx.
  - exact Hfr.
  - exact Hperm.
  - exact Hmo.
  - exact (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) Hsp).
  - exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) Hgp).
  - exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) Htp).
  - intros q Hq. exact (eq_trans (HP q ltac:(unfold acallee_saved; lia)) (Hhi q Hq)).
  - exact (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 Hsaved KS).
  - exact HWx.
  - exact HRx. }
replace (MRX_PC OFF_E1) with (BASE + (AF_m_rx + OFF_E1)) by (vm_compute; reflexivity).
(* +0x390: `bltz s0` *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* off < 0 *)
  rewrite Doff in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. rename Hc into Hneg.
  destruct (ann2_e1_model Bwc off B3 LB He1) as [(Hp & _) | (_ & HFI & HM7)]; [exfalso; lia|].
  (* run 1, +0x390 .. +0x3c0: a2 = OW.foreign, a0 = 1, a1 = OW.foreign + 1, M.foreign = 1; it stops at
     `blt a1, a2` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ann2_awr U9 U18. }
  ann2_md. rename ms into ms1.
  assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w1 a ->
    aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ann2_w1 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9, ?U18 in Hx; unfold ann2_w1; lia). }
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* OW.foreign + 1 overflowed: the trap word, refuted by the model *)
    exfalso. rewrite Da1, D36f in Hc. cbn [branch_taken] in Hc.
    rewrite (EPI.mrxk_lts (bv_swrap 32 (TW.OW_foreign Bwc + 1)) (TW.OW_foreign Bwc)
      ltac:(pose proof (UMR.mr_swrap32_range (TW.OW_foreign Bwc + 1)); lia) ltac:(lia)) in Hc.
    rewrite (UMR.mr_inc_trap (TW.OW_foreign Bwc) ltac:(lia)) in Hc.
    apply Z.eqb_eq in Hc. unfold TC.INT_MAX in HFI. exact (HFI Hc).
  + rename Hc into Hblt.
    rewrite (UMR.mr_swrap32_small (TW.OW_foreign Bwc + 1)) in Da1 by (unfold TC.INT_MAX in HFI; lia).
    (* run 2, +0x3c0 .. +0x3d0: a2 = M.state - 1, OW.foreign stored; it stops at `bltu a0, a2` *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ann2_awr U9 U18. }
    ann2_md. rename ms into ms2.
    assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w1 a ->
      aview tfibsegs (w_H Wc) (ms_mem ms2) a = aview tfibsegs (w_H Wc) mem2 a).
    { intros a Ha Hn. rewrite <- (KA1 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ann2_w1 HFr); [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9, ?U18 in Hx; unfold ann2_w1; lia). }
    clear HF HFr HG KA1. clear dependent ms1.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* M.state is neither S_ONLINE nor S_WAKING: the cut TICK *)
      rewrite Dw in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (EPI.mrx_state12 (TW.M_state Bwc) Sst) in Hc.
      apply negb_true_iff in Hc.
      destruct HM7 as [(Hs & _) | (_ & HB7)]; [rewrite Hc in Hs; discriminate Hs|].
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_TICK).
      { ann2_awr U9 U18. }
      ann2_md.
      assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w1 a ->
        aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
      { intros a Ha Hn. rewrite <- (KA2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ann2_w1 HFr); [| exact Ha | exact Hn].
        intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9, ?U18 in Hx; unfold ann2_w1; lia). }
      clear HF HFr HG.
      ann2_chunk HS 0%nat 20 U9 (TW.u_at Bwc TW.A_M_e1_us 4) D32 VE.
      ann2_chunk HS 1%nat 24 U9 1 (@eq_refl _ (Z_to_bv 64 1)) VF.
      ann2_chunk HS 3%nat 76 U9 (TW.u_at Bwc TW.A_M_desk_counter_valid 4) D34 VD.
      ann2_chunk HS 4%nat 96 U9 (TW.u_at Bwc TW.A_M_fly_on 4) D35 VY.
      ann2_chunk HS 5%nat 212 U18 (TW.OW_foreign Bwc + 1) Da1 VO.
      assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) (ann2_B6 Bwc)).
      { unfold ann2_B6. apply (ann2_w_tick Bwc _ (aview tfibsegs (w_H Wc) mem2) _ Htw VF VO).
        intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh.
        unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        assert (Hd : ann2_w1 x \/ ~ ann2_w1 x) by (unfold ann2_w1; lia).
        destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
        unfold ann2_w1 in Hw. destruct (Z_lt_le_dec x (TB_M + 24)) as [L1 | L1].
        - exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 20 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
            eq_refl VE x ltac:(unfold TB_M, TB_OW in *; lia)).
        - destruct (Z_lt_le_dec x (TB_M + 80)) as [L2 | L2].
          + exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 76 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
              eq_refl VD x ltac:(unfold TB_M, TB_OW in *; lia)).
          + exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 96 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
              eq_refl VY x ltac:(unfold TB_M, TB_OW in *; lia)). }
      assert (HP : aregs_preserved regs2 (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wc) E0 _ ms regs2 (ann2_extra Bwc) HS AG);
            vm_compute; reflexivity).
      pmkst HS. ann2_pc (MRX_PC OFF_TICK).
      apply (CL ms _ _ _ _ HJ (fun a Ha => KAF a ltac:(lia) ltac:(unfold ann2_w1, TB_M, TB_OW; lia)) HP HWF KT).
      unfold R_TICK. split; [rewrite <- HB7; exact Htk | exact Hr1].
    * (* M.state is S_ONLINE or S_WAKING: the inlined m_lost's stores, a1 = 5, the cut SET *)
      rewrite Dw in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (EPI.mrx_state12 (TW.M_state Bwc) Sst) in Hc.
      apply negb_false_iff in Hc.
      destruct HM7 as [(_ & HSET) | (Hs & _)]; [| rewrite Hc in Hs; discriminate Hs].
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_SET).
      { ann2_awr U9 U18. }
      ann2_md.
      assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w1 a ->
        aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
      { intros a Ha Hn. rewrite <- (KA2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ann2_w1 HFr); [| exact Ha | exact Hn].
        intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9, ?U18 in Hx; unfold ann2_w1; lia). }
      clear HF HFr HG.
      ann2_chunk HS 0%nat 20 U9 (TW.u_at Bwc TW.A_M_e1_us 4) D32 VE.
      ann2_chunk HS 1%nat 24 U9 1 (@eq_refl _ (Z_to_bv 64 1)) VF.
      ann2_chunk HS 3%nat 76 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VD.
      ann2_chunk HS 4%nat 96 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VY.
      ann2_chunk HS 5%nat 212 U18 (TW.OW_foreign Bwc + 1) Da1 VO.
      assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms))
        (TW.set_M_desk_counter_valid (TW.set_M_fly_on (ann2_B6 Bwc) 0) 0)).
      { unfold ann2_B6. apply (ann2_w_set Bwc _ (aview tfibsegs (w_H Wc) mem2) _ Htw VF VO VY VD).
        intros x Hx N1 N2 N3 N4. pose proof (TMAP_B_hull x Hx) as Hh.
        unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        assert (Hd : ann2_w1 x \/ ~ ann2_w1 x) by (unfold ann2_w1; lia).
        destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
        unfold ann2_w1 in Hw.
        exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 20 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
          eq_refl VE x ltac:(unfold TB_M, TB_OW in *; lia)). }
      ann2_reg HS (Z_to_bv 5 11) (w64 5) Q11 ltac:(reflexivity).
      assert (HP : aregs_preserved regs2 (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wc) E0 _ ms regs2 (ann2_extra Bwc) HS AG);
            vm_compute; reflexivity).
      pmkst HS. ann2_pc (MRX_PC OFF_SET).
      apply (CL ms _ _ _ _ HJ (fun a Ha => KAF a ltac:(lia) ltac:(unfold ann2_w1, TB_M, TB_OW; lia)) HP HWF KSET).
      unfold R_SET. exists 5, B3. split; [exact Q11|]. split; [lia|]. split; [exact HSET|].
      split; [exact Htk | exact Hr1].
- (* off >= 0: M.e1_us = 1, M.foreign = 0, the cut MO *)
  rewrite Doff in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
  destruct (ann2_e1_model Bwc off B3 LB He1) as [(_ & HMOm) | (Hn & _)]; [| exfalso; lia].
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + OFF_MO).
  { ann2_awr U9 U18. }
  ann2_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ ann2_w1 a ->
    aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ann2_w1 HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. ann2_win Hin Hx ltac:(rewrite ?U9, ?U18 in Hx; unfold ann2_w1; lia). }
  clear HF HFr HG.
  ann2_chunk HS 0%nat 20 U9 1 (@eq_refl _ (Z_to_bv 64 1)) VE.
  ann2_chunk HS 1%nat 24 U9 0 (@eq_refl _ (Z_to_bv 64 0)) VF.
  ann2_chunk HS 3%nat 76 U9 (TW.u_at Bwc TW.A_M_desk_counter_valid 4) D34 VD.
  ann2_chunk HS 4%nat 96 U9 (TW.u_at Bwc TW.A_M_fly_on 4) D35 VY.
  ann2_chunk HS 5%nat 212 U18 (TW.u_at Bwc TW.A_OW_foreign 4) D36 VO.
  assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) (TW.set_M_e1_us (TW.set_M_foreign Bwc 0) 1)).
  { apply (ann2_w_mo Bwc (aview tfibsegs (w_H Wc) mem2) _ Htw VF VE).
    intros x Hx N1. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    assert (Hd : ann2_w1 x \/ ~ ann2_w1 x) by (unfold ann2_w1; lia).
    destruct Hd as [Hw | Hw]; [| exact (KAF x ltac:(lia) Hw)].
    unfold ann2_w1 in Hw. destruct (Z_lt_le_dec x (TB_M + 80)) as [L2 | L2].
    - exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 76 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
        eq_refl VD x ltac:(unfold TB_M, TB_OW in *; lia)).
    - destruct (Z_lt_le_dec x (TB_M + 100)) as [L3 | L3].
      + exact (ann2_keep4 _ _ _ TW.OFF_M TB_M TW.SZ_M 96 _ Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)
          eq_refl VY x ltac:(unfold TB_M, TB_OW in *; lia)).
      + exact (ann2_keep4 _ _ _ TW.OFF_OW TB_OW TW.SZ_OW 212 _ Htw TMAP_B_OW ltac:(lia)
          ltac:(unfold TW.SZ_OW; lia) eq_refl VO x ltac:(unfold TB_M, TB_OW in *; lia)). }
  assert (HP : aregs_preserved regs2 (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wc) E0 _ ms regs2 (ann2_extra Bwc) HS AG);
        vm_compute; reflexivity).
  pmkst HS. ann2_pc (MRX_PC OFF_MO).
  apply (CL ms _ _ _ _ HJ (fun a Ha => KAF a ltac:(lia) ltac:(unfold ann2_w1, TB_M, TB_OW; lia)) HP HWF KMO).
  unfold R_MO. exists B3. split; [exact HMOm|]. split; [exact Htk | exact Hr1].
Qed.

End seg.
