(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 581 of its 678 lines of code are new or changed and 933 lines of the source are left out. *)
(* m_rx_seg_annt: one segment lemma of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v; listing lib/B/Prog/DgnTransportBList.v after AF_m_rx). mrx_seg_annt is
   `K E0 -> K E1 -> K ANNT`: from a machine the cut ANNT (0x84f30, +0x314) describes, symbolic runs over the inner G
   journal (TransportGRunB.v paj_run_x / paj_run_to_x) and the call of desk_named reach the cut E0 or E1, whose mrx_at
   is built with the kit's mrx_at_intro. Model: lib/U/Prog/T/m_rx.v mr_ann2 (annt_model).
     run 1 (+0x314 .. +0x324)  s2 = &OW (object 12), a0 = OW.desk, a1 = a0 + 1 (addiw); `blt a1, a0` to the trap
                               word: taken only at OW.desk = INT_MAX, where int_inc is None (refuted).
     run 2 (+0x324 .. +0x334)  a0 = f.body (sp + 48 = fa + 30, the struct's garr8: mrx_sf_body, mrx_sf_ptr), the
                               stores of OW.desk + 1 and OW.desk_off (= s0 = off), `jal desk_named`: the world
                               relation at annt_B2 (mrx_tw_step); both stores are bytes of mrx_wr, so the frame's facts
                               hold at the call (mrx_frs_wr).
     desk_named (+0x334)       a donor-form callee through TransportGCg.v gx_call_cg with desk_named_cg.v's contract:
                               garr8 and trans_src_ok of the body (the frame from fa + 30), decode_off_win at
                               DNAMED_STK (MRX_STK = 112 + HOFF_STK), trans_rom_view_rd, desk_named_m at annt_B2. Its
                               post keeps every byte of G (gx_kept: the world relation at annt_B2) and every byte
                               above its window (the saved slots, the struct); the kit's mrx_pre / mrx_next.
     run 3 (+0x338 .. +0x34c)  a fresh state (annt_entry2): a1 = f.cmd, a2 = f.body, the stores of OW.desk_p (a0 = dp)
                               and OW.desk_body (fa + 30): the world relation at annt_B4 (annt_w4); `bne a1, 0xe0`
                               goes to the cut E1 (+0x390, mr_e1 off), else the cut E0 (+0x350, mr_e0).
   No instrumented check is on these paths; m_rx's sp, gp, tp, s3 .. s11 and the saved slots are kept. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit m_rx_seg_annt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
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
Module AA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_annt.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma annt_vals : VAL (A_OBJ 12) = TB_OW.
Proof. vm_compute. reflexivity. Qed.

(* A byte of OW's payload is a byte of G. *)
Lemma annt_inG : forall a, TB_OW <= a < TB_OW + 304 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists.
exists (TB_OW, TW.SZ_OW). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* Atoms of run 1: 0 .. 31 the registers at the cut, 32 the shadow base, 33 the 4 bytes of OW.desk, 34 f.body (the
   frame's address + 30). Regions: OW.desk (OW + 0xd0) and OW.desk_off (OW + 0xe8), writable bytes of G, based at
   object 12 (the code's s2); f.body (sp + 48), read-only, based at sp. *)
Definition annt_r_desk : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) 0xd0 0xd4 0xd0 0xd4 [YP09.mkChunk 0xd0 (YP09.CVal 4 (SOff 33 0))].
Definition annt_r_off : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0xe8 0xec 0xe8 0xec [].
Definition annt_r_sf : YP09.region :=
  YP09.mkRegion (Some 2%nat) 48 56 0 0 [YP09.mkChunk 48 (YP09.CVal 8 (SOff 34 0))].
Definition annt_facts1 : facts :=
  mkFacts [(A_OBJ 12, mkAF TB_OW TB_OW 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_annt : sstate :=
  mkSS (AF_m_rx + OFF_ANNT) sr_atoms [annt_r_desk; annt_r_off; annt_r_sf] None annt_facts1.
Definition ANNT_SH : list shent := [].
Definition ANNT_Bx : sv := SOff 32 0.
Definition annt_E (regs : bvmap 5 word) (Bw : list byte) (p : Z) : env :=
  Eimg (PI := PI_transportb)
    (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_desk 4); Z_to_bv 64 p]).

Lemma annt_entry : forall (Wc : world tfibsegs) regs mem Bw sp p,
  tw_at TMAP_B (aview tfibsegs (w_H Wc) mem) Bw ->
  YK11.getr regs 2 = Z_to_bv 64 sp -> 2 ^ 46 <= sp -> sp + 112 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= p < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (sp + 48) 8 p ->
  st_ok_pi tfibsegs VAL (annt_E regs Bw p) ss_annt
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_ANNT))) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem Bw sp p Htw H2 Hs1 Hs2 Hs16 Hp V48.
  pose proof annt_vals as V12.
  set (E := annt_E regs Bw p).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, annt_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B12 : base_val E (Some (A_OBJ 12)) = TB_OW)
    by (apply VB; [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | unfold TB_OW; lia]).
  assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = TB_OW) by exact B12.
  assert (E2 : ew E 2 = Z_to_bv 64 sp)
    by (unfold E, annt_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
  assert (B2 : base_val E (Some 2%nat) = sp) by (apply VB; [exact E2 | lia]).
  assert (U2 : bv_unsigned (ew E 2) = sp) by exact B2.
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
    nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_OW_desk 4); Z_to_bv 64 p] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, annt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw TW.A_OW_desk 4) as R33.
  change (8 * Z.of_nat 4) with 32 in R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_annt.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold annt_r_desk, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B12.
      split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw);
              apply annt_inG; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ TB_OW 0xd0 4 (SOff 33 0) (TW.u_at Bw TW.A_OW_desk 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      exact (tw_read_val tfibsegs _ TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 0xd0 4 TMAP_B_ok Htw TMAP_B_OW
        ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
    + unfold annt_r_off, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B12.
      split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw);
              apply annt_inG; lia|].
      apply Forall_nil.
    + unfold annt_r_sf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ sp 48 8 (SOff 34 0) p);
        [apply DEN; [exact E34 | lia] | cbn; lia | lia | exact V48].
  - unfold annt_r_desk, annt_r_off, annt_r_sf.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B12, B2.
    unfold TB_OW. repeat split; lia.
  - unfold annt_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U12, U2, E32, E33.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_OW_desk 4)) by lia.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* After desk_named, at its return address +0x338: a fresh state. Atoms: 0 .. 31 the registers at the return, 32 the
   shadow base, 33 f.cmd, 34 f.body. Regions: OW.desk_p and OW.desk_body (OW + 0xf0 .. 0x100), writable bytes of G,
   based at s2 (atom 18); f.cmd and f.body (sp + 40 .. sp + 56), read-only, based at sp. *)
Definition annt_r_dp : YP09.region := YP09.mkRegion (Some 18%nat) 0xf0 0x100 0xf0 0x100 [].
Definition annt_r_sf2 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 40 56 0 0
    [YP09.mkChunk 40 (YP09.CVal 1 (SOff 33 0)); YP09.mkChunk 48 (YP09.CVal 8 (SOff 34 0))].
Definition annt_facts2 : facts :=
  mkFacts [(18%nat, mkAF TB_OW TB_OW 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 255 0)] [] [].
Definition ANNT_RET : Z := AF_m_rx + 0x338.
Definition ss_annt2 : sstate := mkSS ANNT_RET sr_atoms [annt_r_dp; annt_r_sf2] None annt_facts2.
Definition annt_E2 (regs : bvmap 5 word) (cmd p : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 cmd; Z_to_bv 64 p]).

Lemma annt_entry2 : forall (Wc : world tfibsegs) regs mem sp cmd p,
  YK11.getr regs 18 = w64 TB_OW ->
  YK11.getr regs 2 = Z_to_bv 64 sp -> 2 ^ 46 <= sp -> sp + 112 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= cmd < 256 -> 0 <= p < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (sp + 40) 1 cmd ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (sp + 48) 8 p ->
  st_ok_pi tfibsegs VAL (annt_E2 regs cmd p) ss_annt2
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ANNT_RET)) mem (YK11.seg_rom tfibsegs))).
Proof.
  intros Wc regs mem sp cmd p H18 H2 Hs1 Hs2 Hs16 Hc Hp V40 V48.
  set (E := annt_E2 regs cmd p).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (E18 : ew E 18 = Z_to_bv 64 TB_OW)
    by (unfold E, annt_E2; rewrite (ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E2 : ew E 2 = Z_to_bv 64 sp)
    by (unfold E, annt_E2; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
  assert (B18 : base_val E (Some 18%nat) = TB_OW) by (apply VB; [exact E18 | unfold TB_OW; lia]).
  assert (B2 : base_val E (Some 2%nat) = sp) by (apply VB; [exact E2 | lia]).
  assert (U18 : bv_unsigned (ew E 18) = TB_OW) by exact B18.
  assert (U2 : bv_unsigned (ew E 2) = sp) by exact B2.
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
    nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 cmd; Z_to_bv 64 p] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, annt_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth] in E32, E33, E34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_annt2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold annt_r_dp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B18.
      split; [unfold TB_OW; lia|]. split; [unfold TB_OW; lia|].
      split; [intros o Ho; apply (gx_rw_writable tfibsegs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw);
              apply annt_inG; lia|].
      apply Forall_nil.
    + unfold annt_r_sf2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs E _ sp 40 1 (SOff 33 0) cmd);
          [apply DEN; [exact E33 | lia] | cbn; lia | lia | exact V40].
      * apply (chunk_ok_val tfibsegs E _ sp 48 8 (SOff 34 0) p);
          [apply DEN; [exact E34 | lia] | cbn; lia | lia | exact V48].
  - unfold annt_r_dp, annt_r_sf2.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B18, B2.
    unfold TB_OW. repeat split; lia.
  - unfold annt_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U2, E32, E33.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small cmd) by lia.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.
End h.

(* ---- the model ---- *)

(* The worlds of mr_ann2: B2 after OW.desk + 1 and OW.desk_off, B4 after OW.desk_p and OW.desk_body. *)
Definition annt_B2 (Bw : list byte) (off : Z) : list byte :=
  TW.set_OW_desk_off (TW.set_OW_desk Bw (TW.OW_desk Bw + 1)) off.
Definition annt_B4 (fa : Z) (Bw : list byte) (off dp : Z) : list byte :=
  TW.set_OW_desk_body (TW.set_OW_desk_p (annt_B2 Bw off) dp) (fa + 30).

Lemma annt_model : forall fr n off Bw B3, mrx_ok fr n ->
  UMR.mr_ann2 timg_B fr n off Bw = Some (B3, tt) ->
  TW.OW_desk Bw <> TC.INT_MAX /\
  exists Bd dp, TC.desk_named_m timg_B (annt_B2 Bw off) (skipn 30 (TI.tf_bytes fr)) = Some (Bd, dp) /\
    (if DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0 then UMR.mr_e0 (annt_B4 (TI.tf_addr fr) Bw off dp)
     else UMR.mr_e1 off (annt_B4 (TI.tf_addr fr) Bw off dp)) = Some (B3, tt).
Proof.
intros fr n off Bw B3 Hok H.
destruct (mrx_ok_fields fr n Hok) as (_ & _ & Hb & _).
unfold UMR.mr_ann2, TC.int_inc in H. cbv beta zeta in H. rewrite Hb in H.
change (Z.to_nat 30) with 30%nat in H.
destruct (TW.OW_desk Bw =? TC.INT_MAX) eqn:ID; cbv beta iota in H; [discriminate H|].
lazymatch type of H with context [TC.desk_named_m ?I ?Bx ?bd] =>
  destruct (TC.desk_named_m I Bx bd) as [[Bd dp]|] eqn:DN end; cbv beta iota in H; [|discriminate H].
split; [apply Z.eqb_neq; exact ID|]. exists Bd, dp. split; [exact DN | exact H].
Qed.

(* ---- the machine values ---- *)

(* `addiw a1, a0, 1` after the signed load of OW.desk. *)
Lemma annt_addiw : forall E e x, sv_denot E e = Z_to_bv 64 x ->
  sv_denot E (SAluw ALU_ADD e (SLit 1)) = Z_to_bv 64 (bv_swrap 32 (x + 1)).
Proof.
intros E e x He.
change (sv_denot E (SAluw ALU_ADD e (SLit 1)))
  with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E e)) (low32 (sv_denot E (SLit 1))))).
rewrite He. change (sv_denot E (SLit 1)) with (Z_to_bv 64 1).
rewrite <- (UMR.mr_swrap32_lit_add x 1).
exact (YK1g.aluw_addi_lit (Z_to_bv 64 x) 1).
Qed.

(* garr8 of a suffix. *)
Lemma annt_garr8_skipn : forall mem base (l : list Z) k, (k <= length l)%nat ->
  garr8 tfibsegs mem base l -> garr8 tfibsegs mem (base + Z.of_nat k) (skipn k l).
Proof.
intros mem base l k Hk HG. rewrite <- (firstn_skipn k l) in HG. apply (garr8_app tfibsegs) in HG as [_ HG].
rewrite length_firstn in HG. replace (Nat.min k (length l)) with k in HG by lia. exact HG.
Qed.

(* The bytes run 1 stores (OW.desk, OW.desk_off) are bytes of mrx_wr. *)
Lemma annt_wr : forall a, (TB_OW + 208 <= a < TB_OW + 212) \/ (TB_OW + 232 <= a < TB_OW + 236) -> mrx_wr a.
Proof.
intros a H. unfold mrx_wr, twb_fld. unfold TW.A_OW_desk, TW.A_OW_desk_off, TW.OFF_OW.
destruct H as [H|H].
- do 17 right. left. lia.
- do 23 right. left. lia.
Qed.

(* The world after the stores of OW.desk_p (dp) and OW.desk_body (p) at OW + 240 .. OW + 256, every other byte kept. *)
Lemma annt_w4 : forall (B2 : list byte) dp p (rd0 rdF : Z -> option Z),
  tw_at TMAP_B rd0 B2 ->
  (forall j, (j < 8)%nat -> rdF (TB_OW + 240 + Z.of_nat j) = Some (YO0f.le_byte dp 8 j)) ->
  (forall j, (j < 8)%nat -> rdF (TB_OW + 248 + Z.of_nat j) = Some (YO0f.le_byte p 8 j)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (TB_OW + 240 <= x < TB_OW + 256) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_OW_desk_body (TW.set_OW_desk_p B2 dp) p).
Proof.
intros B2 dp p rd0 rdF Htw VP VB Hk.
unfold TW.set_OW_desk_body, TW.set_OW_desk_p.
pose proof (mrx_tw_start rdF rd0 B2 Htw) as H0.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 240 TW.A_OW_desk_p 8 dp H0 TMAP_B_OW eq_refl
  ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VP) as H1.
pose proof (mrx_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 248 TW.A_OW_desk_body 8 p H1 TMAP_B_OW eq_refl
  ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VB) as H2.
apply (mrx_tw_end rdF rd0 _ _ H2). intros x Hx HP. mrx_unP HP.
pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
cbn [Z.of_nat Pos.of_succ_nat] in *.
apply Hk; lia.
Qed.

(* ---- tactics (image B's; the image-free ones are image A's annt segment's, AA.annt_win / annt_md / annt_pc) ---- *)

(* The bytes of the chunk at offset off of region idx of the state of HS, base rewritten by UB: forall j < width,
   the view at base + off + j is le_byte v width j, for Hden : sv_denot E e = Z_to_bv 64 v. *)
Ltac annt_chunk HS idx off UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF ?ss (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG;
    let cs := eval vm_compute in (YP09.r_chunks (nth idx (ss_mem ss) annt_r_dp)) in
    let c := eval vm_compute in (AA.annt_find off cs) in
    cbn [ms_mem restrict] in RG;
    destruct RG as (_ & _ & _ & HC);
    cbn [YP09.r_base YP09.r_chunks base_val] in HC;
    rewrite UB in HC;
    pose proof (AA.annt_Forall_nth _ _ c _ HC eq_refl) as HC1;
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

(* A register the code did not write: its value is the one at the state's start (EE reads the start registers). *)
Ltac annt_kept1 HS EE :=
  lazymatch goal with |- YK11.getr _ ?rr = ?rhs =>
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = rhs);
      lazymatch e with SOff ?k 0 =>
        cbn [sv_denot]; rewrite (EE k rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = rhs);
      lazymatch e with SOff ?k 0 =>
        cbn [sv_denot]; rewrite (EE k rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
  end end.

(* s3 .. s11 (x19 .. x27) as at the state's start. *)
Ltac annt_hi HS EE :=
  let q := fresh "q" in let Hq := fresh "Hq" in let Hq' := fresh "Hq'" in
  intros q Hq;
  assert (Hq' : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia;
  destruct Hq' as [->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]; annt_kept1 HS EE.

(* The write rights of a run whose writable bytes lie in OW (bytes of G); UB rewrites a region base. *)
Ltac annt_awr UB :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite ?UB in Ha; right; left; apply annt_inG; unfold TB_OW in *; lia ] |]);
  apply awr_ok_x_nil.

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

Lemma mrx_seg_annt :
  K (MRX_PC OFF_E0) (R_E0 Bw' r) -> K (MRX_PC OFF_E1) (R_E1 Bw' r) ->
  K (MRX_PC OFF_ANNT) (R_ANNT B fr n sp1 Bw' r).
Proof using All.
intros KE0 KE1. unfold mrx_K. intros Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsaved & Htw & HR).
destruct HR as (off & Hcur & Hcmd & Hblen & Hoff & Hoff0 & H8 & H9 & B3 & Hann & Htk & Hr1).
destruct Hcur as (Hok & Hfrs & Hsf).
assert (MFV : MRX_FRAME = 112) by reflexivity.
pose proof HST as (Hspz0 & Hsp16 & Hceil & H46 & H47 & Hra0 & Hraz0 & Hgp0 & Htp0 & H10 & H11 & Hfa0 & Hfan & Hfam &
  Hsrc & Hoffw & Hapart & Hnev & HAR0).
assert (MSV : MRX_STK = 8384) by (vm_compute; reflexivity).
assert (DSV : DNAMED_STK = 8208) by (vm_compute; reflexivity).
assert (HSV : HOFF_STK = 8272) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the model *)
destruct (annt_model fr n off Bwc B3 Hok Hann) as (HID & Bd & dp & HDNm & Htail). clear Hann.
destruct (mrx_ok_fields fr n Hok) as (Hdst & Hsrcf & Hbody & H30 & Hbl0 & Hbln & Hcmdr & _).
pose proof Hok as (Hn0 & _).
assert (HLB : 63 <= mlen fr) by (unfold TC.SPEC_ANN_MIN in Hblen; lia).
(* f.body at the cut *)
assert (V48 : val_mem tfibsegs (mrestrict (w_H Wc) mem2) (sp1 - MRX_FRAME + 48) 8 (TI.tf_addr fr + 30)).
{ pose proof (mrx_sf_body _ _ _ _ Hsf) as V. rewrite (mrx_sf_ptr fr n _ Hok), Hbody in V. exact V. }
set (E0 := annt_E regs2 Bwc (TI.tf_addr fr + 30)).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, annt_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn; unfold E0, annt_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U12 : bv_unsigned (ew E0 (A_OBJ 12)) = TB_OW).
{ unfold E0, annt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite annt_vals.
  first [reflexivity | apply unsigned_lit_small; unfold TB_OW; lia]. }
assert (U12' : bv_unsigned (ew E0 253%nat) = TB_OW) by exact U12.
assert (Hspm : (sp1 - MRX_FRAME) mod 16 = 0)
  by (replace (sp1 - MRX_FRAME) with (sp1 + (-7) * 16) by (unfold MRX_FRAME; lia); rewrite Z_mod_plus_full; exact Hsp16).
assert (Hfab : 0 <= TI.tf_addr fr + 30 < 2 ^ 64) by lia.
pose proof (annt_entry Wc regs2 mem2 Bwc (sp1 - MRX_FRAME) (TI.tf_addr fr + 30) Htw Hsp
  ltac:(unfold MRX_FRAME; lia) ltac:(unfold MRX_FRAME; lia) Hspm Hfab V48) as HS.
fold E0 in HS.
assert (SHOK : sh_ok tfibsegs ANNT_Bx ANNT_SH E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok, ANNT_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
rewrite (mrx_pcv OFF_ANNT).
(* run 1, +0x314 .. +0x324: s2 = &OW, a0 = OW.desk, a1 = a0 + 1; it stops at `blt a1, a0`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ annt_awr U12'. }
AA.annt_md. rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 208 <= a < TB_OW + 212) -> ~ (TB_OW + 232 <= a < TB_OW + 236) ->
  aview tfibsegs (w_H Wc) (ms_mem ms1) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 208 <= x < TB_OW + 212) \/ (TB_OW + 232 <= x < TB_OW + 236)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  AA.annt_win Hin Hx ltac:(rewrite ?U12' in Hx; first [left; lia | right; lia]). }
clear HF HFr HG.
(* the values of the test *)
pose proof (TWL.s32_range Bwc TW.A_OW_desk) as Sdesk.
change (TW.s32_at Bwc TW.A_OW_desk) with (TW.OW_desk Bwc) in Sdesk.
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bwc TW.A_OW_desk 4))
  by (unfold E0, annt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TI.tf_addr fr + 30))
  by (unfold E0, annt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
pose proof (TWL.u_at_range Bwc TW.A_OW_desk 4) as R33. change (8 * Z.of_nat 4) with 32 in R33.
assert (D33 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.OW_desk Bwc))
  by exact (AA.annt_sext E0 33 _ E33 R33).
assert (D11 : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_desk Bwc + 1)).
{ rewrite (annt_addiw E0 _ _ D33). rewrite UMR.mr_swrap32_small; [reflexivity|].
  unfold TC.INT_MAX in HID. lia. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
{ (* OW.desk + 1 below OW.desk: OW.desk = INT_MAX, the trap word; the model's int_inc rules it out *)
  exfalso. rewrite D11, D33 in Hc. cbn [branch_taken] in Hc.
  rewrite (EPI.mrxk_lts (TW.OW_desk Bwc + 1) (TW.OW_desk Bwc) ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* run 2, +0x324 .. +0x334: `blt` not taken, a0 = f.body, the stores of OW.desk + 1 and OW.desk_off, `jal
   desk_named`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ annt_awr U12'. }
AA.annt_md.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 208 <= a < TB_OW + 212) -> ~ (TB_OW + 232 <= a < TB_OW + 236) ->
  aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha H1 H2. rewrite <- (KA1 a Ha H1 H2).
  apply (kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 208 <= x < TB_OW + 212) \/ (TB_OW + 232 <= x < TB_OW + 236)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  AA.annt_win Hin Hx ltac:(rewrite ?U12' in Hx; first [left; lia | right; lia]). }
clear HF HFr HG KA1. clear dependent ms1.
(* the registers at the call *)
annt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15540)) R1 ltac:(apply codeptr_val; exact HEI).
annt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) R2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hsp).
annt_reg HS (Z_to_bv 5 3) (YK11.getr regs0 (Z_to_bv 5 3)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
annt_reg HS (Z_to_bv 5 4) (YK11.getr regs0 (Z_to_bv 5 4)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
annt_reg HS (Z_to_bv 5 10) (w64 (TI.tf_addr fr + 30)) R10
  ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
annt_reg HS (Z_to_bv 5 8) (w64 off) R8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8).
annt_reg HS (Z_to_bv 5 9) (w64 TB_M) R9
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H9).
annt_reg HS (Z_to_bv 5 18) (w64 TB_OW) R18 ltac:(cbn [sv_denot]; rewrite U12', Z.add_0_r; reflexivity).
assert (Rhi0 : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q))
  by annt_hi HS EE.
assert (Rhi : mrx_hi regs0 (ms_regs ms)) by (intros q Hq; rewrite (Rhi0 q Hq); exact (Hhi q Hq)).
assert (R3g : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by exact (eq_trans R3 Hgp0).
assert (R4g : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by exact (eq_trans R4 Htp0).
destruct (mrx_pre sp1 (ms_regs ms) 15540 Hsp16 Hceil H47 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (Hret & Hraz & Hspz & Hspm16 & Hwin & Hle).
(* the bytes run 1 and 2 stored, and the world relation at the call *)
assert (DO : sv_denot E0 (SOff 8 0) = Z_to_bv 64 off)
  by (cbn [sv_denot]; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8).
pose proof (st_ok_region_nth E0 _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E0 _ _ 1 _ HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG0, RG1.
destruct RG0 as (_ & _ & _ & HC0). destruct RG1 as (_ & _ & _ & HC1).
cbn [YP09.r_base YP09.r_chunks base_val] in HC0, HC1. rewrite U12' in HC0, HC1.
pose proof (mrx_chunk_rd _ _ _ _ _ _ _ _ (Forall_inv HC0) D11 ltac:(cbn; lia)) as VD.
pose proof (mrx_chunk_rd _ _ _ _ _ _ _ _ (Forall_inv HC1) DO ltac:(cbn; lia)) as VO.
clear HC0 HC1.
assert (HW1 : tw_at TMAP_B (aview tfibsegs (w_H Wc) (ms_mem ms)) (annt_B2 Bwc off)).
{ unfold annt_B2, TW.set_OW_desk_off, TW.set_OW_desk.
  pose proof (mrx_tw_start (aview tfibsegs (w_H Wc) (ms_mem ms)) (aview tfibsegs (w_H Wc) mem2) Bwc Htw) as H0.
  pose proof (mrx_tw_step _ _ _ _ TW.OFF_OW TB_OW TW.SZ_OW 208 TW.A_OW_desk 4 (TW.OW_desk Bwc + 1) H0 TMAP_B_OW
    eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VD) as H1.
  pose proof (mrx_tw_step _ _ _ _ TW.OFF_OW TB_OW TW.SZ_OW 232 TW.A_OW_desk_off 4 off H1 TMAP_B_OW
    eq_refl ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat Pos.of_succ_nat]; lia) VO) as H2.
  apply (mrx_tw_end _ _ _ _ H2). intros x Hx HP. mrx_unP HP.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  cbn [Z.of_nat Pos.of_succ_nat] in *.
  apply KA2; [lia | lia | lia]. }
(* the frame's facts at the call: run 1 and 2 stored only bytes of mrx_wr *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a ->
  aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a).
{ intros a Ha Hw. apply KA2; [exact Ha | intros Hx; apply Hw; apply annt_wr; left; exact Hx
                              | intros Hx; apply Hw; apply annt_wr; right; exact Hx]. }
pose proof (mrx_frs_wr B fr ly2 S2 Wc mem2 (ms_mem ms) Hfrs Hapart ltac:(lia) Hfam KW) as Hfrs1.
destruct Hfrs1 as (Hg8 & Hsrc1 & Hrom1).
(* desk_named's premises: the body's bytes, placement and window, the model call *)
assert (LBD : Z.of_nat (length (skipn 30 (TI.tf_bytes fr))) = mlen fr - 30)
  by (rewrite length_skipn; unfold AK.mlen in *; lia).
assert (Hg8b : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) (TI.tf_addr fr + 30)
  (map DSpec.bz (skipn 30 (TI.tf_bytes fr)))).
{ rewrite <- skipn_map. change (TI.tf_addr fr + 30) with (TI.tf_addr fr + Z.of_nat 30).
  apply annt_garr8_skipn; [rewrite length_map; unfold AK.mlen in HLB; lia | exact Hg8]. }
assert (Hsrcb : trans_src_ok B ly2 S2 Wc (ms_mem ms) (TI.tf_addr fr + 30)
  (Z.of_nat (length (skipn 30 (TI.tf_bytes fr))))).
{ eapply trans_src_ok_sub; [exact Hsrc1 | lia | lia | lia]. }
assert (Hoffb : decode_off_win (ms_regs ms) DNAMED_STK (TI.tf_addr fr + 30)
  (Z.of_nat (length (skipn 30 (TI.tf_bytes fr))))).
{ unfold decode_off_win. rewrite Hspz, LBD. lia. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx tfibsegs (transportb_sigma TB_desk_named) rg mm mdx) Q) end.
(* +0x334: desk_named (fa + 30), a donor-form callee through gx_call_cg *)
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head tfibsegs B MT TG.G_HARNESS_B MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    (ms_mem ms) mdw0 0 _ (ms_regs ms) DNAMED_STK DNAMED_EV 0 (fun _ => False)
    (fun regs3 _ _ => YK11.getr regs3 10 = w64 dp /\ Bd = annt_B2 Bwc off) HGX HGNE HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (HDN fx MRX_STK sp1 [] lyc Sc W memS mdc [] ly2 S2 Wc (ms_mem ms) mdw0 0 (ms_regs ms)
      (TI.tf_addr fr + 30) dp (skipn 30 (TI.tf_bytes fr)) (annt_B2 Bwc off) Bd HJS
      Hret Hraz R3g R4g R10 Hspm16 ltac:(lia) Hle ltac:(lia)
      Hg8b Hsrcb Hoffb Hrom1 HDNm ltac:(unfold DNAMED_EV; lia)). }
  intros W2 c2 _ HP. apply decode_cg_post_dcg. exact HP. }
intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 & [[Q10 HBd] HGK]).
assert (e = 0) by (unfold DNAMED_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
rewrite R1. replace (BASE + 15540) with (BASE + ANNT_RET) by (vm_compute; reflexivity).
(* the facts carried across the call: the world relation (G kept), the struct and the saved slots (above its window) *)
assert (HW3 : tw_at TMAP_B (aview tfibsegs (w_H W3) mem3) (annt_B2 Bwc off))
  by exact (tw_kept_GB _ _ _ HW1 (gx_kept_rows tfibsegs TG.G_HARNESS_B Wc (ms_mem ms) W3 mem3 HGK)).
destruct HK3 as (K31 & _).
assert (KS3 : forall a, sp1 - MRX_FRAME <= a < sp1 ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H Wc) (ms_mem ms) a).
{ intros a Ha. apply K31; [lia | rewrite Hspz; lia]. }
assert (Hsaved1 : mrx_saved Wc (ms_mem ms) sp1 regs0).
{ apply (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 Hsaved). intros a Ha. apply KA2; unfold TB_OW; lia. }
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W3 (ms_mem ms) mem3 (ms_regs ms) regs3 S2 S3 ly2 ly3 DNAMED_STK
  ltac:(lia) ltac:(lia) Hspz Hsaved1 (fun a Ha => KS3 a ltac:(lia)) HP3 R2 R3 R4 Rhi Hfr Hfr3 Hperm Hperm3 Hmo HMO3)
  as (Hsaved3 & G2 & G3 & G4 & Ghi & Hfr3' & Hperm3' & Hmo3').
assert (Hsf1 : mrx_sf Wc (ms_mem ms) sp1 fr n).
{ apply (mrx_sf_kept Wc Wc mem2 (ms_mem ms) sp1 fr n Hsf). intros a Ha. apply KA2; unfold TB_OW; lia. }
assert (Hsf3 : mrx_sf W3 mem3 sp1 fr n).
{ apply (mrx_sf_kept Wc W3 (ms_mem ms) mem3 sp1 fr n Hsf1). intros a Ha. apply KS3. lia. }
pose proof (mrx_sf_cmd _ _ _ _ Hsf3) as V40'.
assert (V48' : val_mem tfibsegs (mrestrict (w_H W3) mem3) (sp1 - MRX_FRAME + 48) 8 (TI.tf_addr fr + 30)).
{ pose proof (mrx_sf_body _ _ _ _ Hsf3) as V. rewrite (mrx_sf_ptr fr n _ Hok), Hbody in V. exact V. }
assert (G8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 off)
  by (rewrite (HP3 8 ltac:(unfold acallee_saved; lia)); exact R8).
assert (G9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 TB_M)
  by (rewrite (HP3 9 ltac:(unfold acallee_saved; lia)); exact R9).
assert (G18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 TB_OW)
  by (rewrite (HP3 18 ltac:(unfold acallee_saved; lia)); exact R18).
clear dependent ms.
(* the fresh state at +0x338 *)
pose proof (annt_entry2 W3 regs3 mem3 (sp1 - MRX_FRAME) (DSpec.sf_cmd (mrx_f fr n)) (TI.tf_addr fr + 30)
  G18 G2 ltac:(lia) ltac:(lia) Hspm ltac:(lia) Hfab V40' V48') as HS.
set (E1 := annt_E2 regs3 (DSpec.sf_cmd (mrx_f fr n)) (TI.tf_addr fr + 30)) in HS.
assert (HEIx : img_env VAL A_LIM E1) by (unfold E1, annt_E2; apply Eimg_env).
assert (EE1 : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E1 n0 = YK11.getr regs3 r0)
  by (intros n0 r0 Hk0; unfold E1, annt_E2; apply ew_Eimg_Ereg_nat; exact Hk0).
assert (U18 : bv_unsigned (ew E1 18) = TB_OW)
  by (rewrite (EE1 18%nat (Z_to_bv 5 18) eq_refl), G18; apply unsigned_lit_small; unfold TB_OW; lia).
assert (SHOK1 : sh_ok tfibsegs ANNT_Bx ANNT_SH E1 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, ANNT_SH; apply Forall_nil).
(* the end of a run after desk_named, at a cut: the common facts of mrx_at *)
assert (CL2 : forall msx md pc R Bx,
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly3 S3 W3
    (ms_mem msx) md 0 ->
  (forall a, sp1 - 32 <= a < sp1 -> aview tfibsegs (w_H W3) (ms_mem msx) a = aview tfibsegs (w_H W3) mem3 a) ->
  YK11.getr (ms_regs msx) (Z_to_bv 5 2) = YK11.getr regs3 (Z_to_bv 5 2) ->
  YK11.getr (ms_regs msx) (Z_to_bv 5 3) = YK11.getr regs3 (Z_to_bv 5 3) ->
  YK11.getr (ms_regs msx) (Z_to_bv 5 4) = YK11.getr regs3 (Z_to_bv 5 4) ->
  (forall q, 19 <= q <= 27 -> YK11.getr (ms_regs msx) (Z_to_bv 5 q) = YK11.getr regs3 (Z_to_bv 5 q)) ->
  tw_at TMAP_B (aview tfibsegs (w_H W3) (ms_mem msx)) Bx ->
  K pc R -> R W3 Bx ly3 S3 (ms_regs msx) (ms_mem msx) ->
  SRr tfibsegs W3 (mkCfg (@YK11.mkst fx (ms_regs msx) (Z_to_bv 64 pc) (ms_mem msx) (YK11.seg_rom tfibsegs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r)).
{ intros msx md pc R Bx HJx KS Q2 Q3 Q4 QH HWx KX HRx.
  apply (KX W3 Bx).
  apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R W3 Bx ly3 S3).
  - exact HJx.
  - exact Hfr3'.
  - exact Hperm3'.
  - exact Hmo3'.
  - exact (eq_trans Q2 G2).
  - exact (eq_trans Q3 G3).
  - exact (eq_trans Q4 G4).
  - intros q Hq. exact (eq_trans (QH q Hq) (Ghi q Hq)).
  - exact (mrx_saved_kept W3 W3 mem3 (ms_mem msx) sp1 regs0 Hsaved3 KS).
  - exact HWx.
  - exact HRx. }
(* the values the code compares and stores *)
assert (E33' : ew E1 33 = Z_to_bv 64 (DSpec.sf_cmd (mrx_f fr n)))
  by (unfold E1, annt_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34' : ew E1 34 = Z_to_bv 64 (TI.tf_addr fr + 30))
  by (unfold E1, annt_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (Dcmd : sv_denot E1 (SOff 33 0) = Z_to_bv 64 (DSpec.sf_cmd (mrx_f fr n)))
  by (cbn [sv_denot]; rewrite E33', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Ddp : sv_denot E1 (SOff 10 0) = Z_to_bv 64 dp)
  by (cbn [sv_denot]; rewrite (EE1 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q10).
assert (Dp : sv_denot E1 (SOff 34 0) = Z_to_bv 64 (TI.tf_addr fr + 30))
  by (cbn [sv_denot]; rewrite E34', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* run 3, +0x338 .. +0x34c: f.cmd, f.body, OW.desk_p, OW.desk_body; it stops at `bne a1, a3` (cmd e0?). *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ annt_awr U18. }
AA.annt_md. rename ms into ms2.
assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 240 <= a < TB_OW + 256) ->
  aview tfibsegs (w_H W3) (ms_mem ms2) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 240 <= x < TB_OW + 256) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta. AA.annt_win Hin Hx ltac:(rewrite ?U18 in Hx; lia). }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
{ (* cmd <> e0: cmd e1, the cut E1 *)
  rewrite Dcmd in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (DSpec.sf_cmd (mrx_f fr n)) 224 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  replace (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) with false in Htail
    by (symmetry; apply Z.eqb_neq; unfold TC.SPEC_CMD_E0; lia).
  cbv beta iota in Htail.
  paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_E1).
  { annt_awr U18. }
  AA.annt_md.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 240 <= a < TB_OW + 256) ->
    aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KA3 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 240 <= x < TB_OW + 256) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. cbv beta. AA.annt_win Hin Hx ltac:(rewrite ?U18 in Hx; lia). }
  clear HF HFr HG.
  annt_chunk HS 0%nat 240 U18 dp Ddp VP.
  annt_chunk HS 0%nat 248 U18 (TI.tf_addr fr + 30) Dp VB.
  assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H W3) (ms_mem ms)) (annt_B4 (TI.tf_addr fr) Bwc off dp))
    by (unfold annt_B4; exact (annt_w4 _ _ _ _ _ HW3 VP VB KAF)).
  assert (Q2 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = YK11.getr regs3 (Z_to_bv 5 2)) by annt_kept1 HS EE1.
  assert (Q3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = YK11.getr regs3 (Z_to_bv 5 3)) by annt_kept1 HS EE1.
  assert (Q4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = YK11.getr regs3 (Z_to_bv 5 4)) by annt_kept1 HS EE1.
  assert (Q8 : YK11.getr (ms_regs ms) (Z_to_bv 5 8) = YK11.getr regs3 (Z_to_bv 5 8)) by annt_kept1 HS EE1.
  assert (Q9 : YK11.getr (ms_regs ms) (Z_to_bv 5 9) = YK11.getr regs3 (Z_to_bv 5 9)) by annt_kept1 HS EE1.
  assert (Q18 : YK11.getr (ms_regs ms) (Z_to_bv 5 18) = YK11.getr regs3 (Z_to_bv 5 18)) by annt_kept1 HS EE1.
  assert (QH : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs3 (Z_to_bv 5 q))
    by annt_hi HS EE1.
  pmkst HS. AA.annt_pc (MRX_PC OFF_E1).
  apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold TB_OW; lia)) Q2 Q3 Q4 QH HWF KE1).
  unfold R_E1. exists off, B3. split; [exact Hoff|]. split; [exact (eq_trans Q8 G8)|].
  split; [exact (eq_trans Q9 G9)|]. split; [exact (eq_trans Q18 G18)|].
  split; [exact Htail|]. split; [exact Htk | exact Hr1]. }
(* cmd = e0: the cut E0 *)
rewrite Dcmd in Hc. cbn [branch_taken sv_denot] in Hc.
rewrite (EPI.mrxk_eqb (DSpec.sf_cmd (mrx_f fr n)) 224 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc.
replace (DSpec.sf_cmd (mrx_f fr n) =? TC.SPEC_CMD_E0) with true in Htail
  by (symmetry; apply Z.eqb_eq; unfold TC.SPEC_CMD_E0; lia).
cbv beta iota in Htail.
paj_run_to_tok RUNTO HS HJ3 SHOK1 YC4b.Bspan (AF_m_rx + OFF_E0).
{ annt_awr U18. }
AA.annt_md.
assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_OW + 240 <= a < TB_OW + 256) ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- (KA3 a Ha Hn).
  apply (kept_of_frame _ _ _ _ _ (fun x => TB_OW + 240 <= x < TB_OW + 256) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta. AA.annt_win Hin Hx ltac:(rewrite ?U18 in Hx; lia). }
clear HF HFr HG.
annt_chunk HS 0%nat 240 U18 dp Ddp VP.
annt_chunk HS 0%nat 248 U18 (TI.tf_addr fr + 30) Dp VB.
assert (HWF : tw_at TMAP_B (aview tfibsegs (w_H W3) (ms_mem ms)) (annt_B4 (TI.tf_addr fr) Bwc off dp))
  by (unfold annt_B4; exact (annt_w4 _ _ _ _ _ HW3 VP VB KAF)).
assert (Q2 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = YK11.getr regs3 (Z_to_bv 5 2)) by annt_kept1 HS EE1.
assert (Q3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = YK11.getr regs3 (Z_to_bv 5 3)) by annt_kept1 HS EE1.
assert (Q4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = YK11.getr regs3 (Z_to_bv 5 4)) by annt_kept1 HS EE1.
assert (Q9 : YK11.getr (ms_regs ms) (Z_to_bv 5 9) = YK11.getr regs3 (Z_to_bv 5 9)) by annt_kept1 HS EE1.
assert (QH : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs3 (Z_to_bv 5 q))
  by annt_hi HS EE1.
pmkst HS. AA.annt_pc (MRX_PC OFF_E0).
apply (CL2 ms _ _ _ _ HJ3 (fun a Ha => KAF a ltac:(lia) ltac:(unfold TB_OW; lia)) Q2 Q3 Q4 QH HWF KE0).
unfold R_E0. exists B3. split; [exact (eq_trans Q9 G9)|]. split; [exact Htail|]. split; [exact Htk | exact Hr1].
Qed.
End seg.
