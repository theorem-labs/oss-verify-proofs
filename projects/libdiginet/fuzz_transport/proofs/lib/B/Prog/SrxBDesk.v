(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 496 of its 563 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SrxBDeskKit.v; 554 of its 631 lines of code are new or changed and 486 lines of the source are left out. *)
(* SrxBDesk: Theorem srxb_desk_ok : forall fx rc B MT, @srxb_desk_stmt fx rc B MT (lib/B/Prog/SrxBCut.v), the desk
   piece of the walk of diginet_session_rx on fuzz_transport.asan-ubsan (0x87784 = transportb_sigma
   TB_diginet_session_rx, AF_diginet_session_rx = 0x64e4 of lib/B/Prog/DgnTransportBList.v), from the desk cut (+0x2e4,
   0x87a68) to the learn cut (+0x330), the closed cut (+0x374) and the ignored cut (+0x1d4). The code is image A's
   (lib/A/Prog/SrxDesk.v) 12 bytes later and the proof is that file's at image B's names. The runs are the
   position-abstract token runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x, inside the caller's G
   journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []):
     run 1  +0x2e4 .. +0x2f8  s8 = s + 116 (g_s.desk_known), a2 = its shadow byte's address, the checked 1-byte load
                              of that shadow byte (0 by trans_srx_cells, so `bne` is not taken) and the 4-byte load
                              of desk_known into a0;
     +0x2fc                   `beq a0, zero` on the sign-extended desk_known: 0 runs one instruction to the learn
                              cut (the model's S_desk_known Bw =? 0 of :278); else
     run 2  +0x300 .. +0x308  a1 = s + 120 (g_s.desk_mac), a2 = 6, a0 = s7 = f + 6, up to the bcmp call;
     +0x30c                   the bcmp wrapper (YG0d.v abcmp_realizes through TransportGCg.v gx_call_leaf and YCbq.v
                              aj_bcmp_at: SrxBDeskKit.v srxbdk_bcmp): its result is 0 exactly when the six bytes
                              agree, which is the model's memeq of :279 (srxbdk_bcmp_memeq: the bytes at f + 6 are
                              fr_src b, the bytes at s + 120 are S_desk_mac Bw);
     +0x310                   `beq a0, zero`: equal runs one instruction to the closed cut with the world Bw and the
                              path srxb_pre_acc Bw b Bw; else
     run 3  +0x314 .. +0x324  a1 = s + 18184, its shadow byte (0 by trans_srx_cells), `beq` taken to the ignored cut
                              with a0 = 0, the result DIGINET_OK (the model's srxb_m_desk).
   The error paths of this range are unreached: __asan_report_load4 at +0x4e4 (0x87c68; the block at +0x4d4 is not
   entered, the shadow byte of s + 116 being 0) and __asan_report_load8 at +0x32c (0x87ab0; the shadow byte of
   s + 18184 is 0). The range has no UBSan trap branch. Neither run nor the bcmp wrapper writes a byte outside the
   wrapper's own stack window below the realigned sp, so SrxBDeskKit.v srxbdk_move carries every fact of the desk
   cut to each of the three cuts. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit SrxBCut SrxBDeskKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The two pcs inside the piece: the test of :278 (+0x2fc) and the test of :279 after the bcmp call (+0x310). *)
Definition SRXBD_C1 : Z := AF_diginet_session_rx + 0x2fc.
Definition SRXBD_C2 : Z := AF_diginet_session_rx + 0x310.
Definition SRXBD_C3 : Z := AF_diginet_session_rx + 0x314.
Lemma srxbd_pcs : SRXB_DESK = 26568 /\ SRXBD_C1 = 26592 /\ SRXBD_C2 = 26612 /\ SRXBD_C3 = 26616 /\
  SRXB_LEARN = 26644 /\ SRXB_CLOSED = 26712 /\ SRXB_IGN = 26296.
Proof. repeat split; reflexivity. Qed.

(* run 1: the 4 bytes of g_s.desk_known read into atom 33, and the shadow entry of [s + 112, s + 128), the group
   of 8 shadow bytes of [g_s + 64, g_s + 128) that holds the shadow byte of s + 116. *)
Definition srxbd_rg_dk : YP09.region :=
  YP09.mkRegion (Some 20%nat) 116 120 0 0 [YP09.mkChunk 116 (YP09.CVal 4 (SOff 33 0))].
Definition srxbd_facts1 : facts :=
  mkFacts [(20%nat, mkAF SRX_S SRX_S 6); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_srxbd1 : sstate := mkSS SRXB_DESK sr_atoms [srxbd_rg_dk] None srxbd_facts1.
Definition SRXBD_SH1 : list shent := [mkSHE 20 112 128].
(* the state at +0x310, with the shadow entry of g_s.stats.rx_ignored's group *)
Definition srxbd_facts2 : facts :=
  mkFacts [(21%nat, mkAF (SRX_S + 18152) (SRX_S + 18152) 3); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbd2 : sstate := mkSS SRXBD_C2 sr_atoms [] None srxbd_facts2.
Definition SRXBD_SH2 : list shent := [mkSHE 21 32 40].
Definition SRXBD_Bx : sv := SOff 27 0.
Definition SRXBD_B0 : Z * Z := (0, 0).

(* `beq a0, zero` on a sign-extended 4-byte field. *)
Lemma srxbd_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma srxbd_dk_range : forall Bw, - 2 ^ 31 <= TW.S_desk_known Bw < 2 ^ 31.
Proof.
intros Bw. pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_S_desk_known 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_S_desk_known 4)) with (TW.S_desk_known Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* `lw a0, 0(s8)`: the sign-extended 4-byte load of g_s.desk_known. *)
Lemma srxbd_sext : forall E Bw, ew E 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 116) 4) ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.S_desk_known Bw).
Proof.
intros E Bw H. pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 116) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuations: the 32 registers, the shadow base (atom 32) and the 4 bytes of g_s.desk_known (atom 33). *)
Definition srxbd_E (regs2 : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 116) 4)]).
Definition srxbd_E0 (regs2 : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [w64 SHADOW_OFF]).

Lemma srxbd_ew : forall regs2 Bw n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (srxbd_E regs2 Bw) n = YK11.getr regs2 r.
Proof. intros regs2 Bw n r Hn. unfold srxbd_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma srxbd_ew0 : forall regs2 n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (srxbd_E0 regs2) n = YK11.getr regs2 r.
Proof. intros regs2 n r Hn. unfold srxbd_E0. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma srxbd_ew32 : forall regs2 Bw, ew (srxbd_E regs2 Bw) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
intros regs2 Bw. unfold srxbd_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0).
Qed.
Lemma srxbd_ew33 : forall regs2 Bw, ew (srxbd_E regs2 Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 116) 4).
Proof.
intros regs2 Bw. unfold srxbd_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 1).
Qed.
Lemma srxbd_env : forall regs2 Bw, img_env VAL A_LIM (srxbd_E regs2 Bw).
Proof. intros regs2 Bw. unfold srxbd_E. apply Eimg_env. Qed.
Lemma srxbd_env0 : forall regs2, img_env VAL A_LIM (srxbd_E0 regs2).
Proof. intros regs2. unfold srxbd_E0. apply Eimg_env. Qed.

(* The state of run 1, at +0x2e4. *)
Lemma srxbd_entry1 : forall ly S (W : world segs) regs2 mem md Bw,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs2 20 = w64 SRX_S -> YK11.getr regs2 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbd_E regs2 Bw) ss_srxbd1
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_DESK)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBD_Bx SRXBD_SH1 (srxbd_E regs2 Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs2 mem md Bw HSC HAR Htw R20 R27.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (srxbd_E regs2 Bw) 20) = SRX_S)
  by (rewrite (srxbd_ew regs2 Bw 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (srxbd_E regs2 Bw) 27) = SHADOW_OFF)
  by (rewrite (srxbd_ew regs2 Bw 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 116) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (srxbd_E regs2 Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 116) 4)
  by (rewrite (srxbd_ew33 regs2 Bw); apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (srxbd_E regs2 Bw) 32) = SHADOW_OFF)
  by (rewrite (srxbd_ew32 regs2 Bw); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbd1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold srxbd_rg_dk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ SRX_S 116 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 116) 4));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 116 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold srxbd_rg_dk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold srxbd_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U27, U33.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (srxbd_E regs2 Bw) SRXBD_Bx = SHADOW_OFF).
  { unfold U, SRXBD_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBD_SH1. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBD_Bx 20 (SRX_S + 112) 16 SRX_S 112 128
    (srxbdk_gs_ra B ly S W mem md (SRX_S + 112) 16 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The state at +0x310 (after the bcmp call) and at any pc with no region: the branch states. *)
Lemma srxbd_entry2 : forall ly S (W : world segs) regs3 mem md,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs3 21 = w64 (SRX_S + 18152) -> YK11.getr regs3 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbd_E0 regs3) ss_srxbd2
    (restrict (w_H W) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + SRXBD_C2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBD_Bx SRXBD_SH2 (srxbd_E0 regs3) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs3 mem md HSC HAR R21 R27.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (U21 : bv_unsigned (ew (srxbd_E0 regs3) 21) = SRX_S + 18152)
  by (rewrite (srxbd_ew0 regs3 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (srxbd_E0 regs3) 27) = SHADOW_OFF)
  by (rewrite (srxbd_ew0 regs3 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbd2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  + unfold srxbd_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21, U27.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (srxbd_E0 regs3) SRXBD_Bx = SHADOW_OFF).
  { unfold U, SRXBD_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBD_SH2. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBD_Bx 21 (SRX_S + 18184) 8 (SRX_S + 18152) 32 40
    (srxbdk_gs_ra B ly S W mem md (SRX_S + 18184) 8 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma srxbd_entry0 : forall (W : world segs) regs2 mem pc,
  st_ok_pi segs VAL (srxbd_E0 regs2) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* The piece                                                           *)
(* ------------------------------------------------------------------ *)

Lemma srxbd_holds : @srxb_desk_stmt fx rc B MT.
Proof.
unfold srxb_desk_stmt. intros IGN LEARN CLOSED.
unfold srxb_desk_at. intros HLAWS HCALLS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HRDF HFB Htw H0 HMAC HREGS.
pose proof HLAWS as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRON & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & ABCMP & _).
pose proof HFIX as (_ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hm & _ & _
  & _ & _ & Hinv & _).
destruct (srxbdk_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
  as (HAR & Hce0 & Hlo & Hhi & Hsp0a & H47 & Hsp16 & (Hs1a & Hs1b) & Hs1m & HF4 & HF64 & HFc & HFe).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) & R23).
pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hstk : SRX_STK = 9184) by reflexivity.
assert (Hfbs : SRXB_FBYTES = 128) by reflexivity.
assert (Hsf : SRX_F = 32) by reflexivity.
assert (Hffs : FRAME_F_SIZE = 64) by reflexivity.
assert (CS : SRX_S = 6157888) by reflexivity.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1, +0x2e4 .. +0x2f8: s8 = s + 116, the checked 4-byte load of g_s.desk_known *)
destruct (srxbd_entry1 ly2 S2 W2 regs2 mem2 md2 Bw HSC HAR2 Htw R20 R27) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (srxbd_E regs2 Bw)) by apply srxbd_env.
pose proof HJ2 as HJ.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXBD_C1.
{ srxbdk_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (srxbd_E regs2 Bw) n = YK11.getr regs2 rr)
  by (intros n rr Hn; exact (srxbd_ew regs2 Bw n rr Hn)).
srxbdk_kreg HS EE regs2 (2%bv : bv 5) 2%nat R2 X2.
srxbdk_kreg HS EE regs2 (3%bv : bv 5) 3%nat R3 X3.
srxbdk_kreg HS EE regs2 (4%bv : bv 5) 4%nat R4 X4.
srxbdk_kreg HS EE regs2 (8%bv : bv 5) 8%nat R8 X8.
srxbdk_kreg HS EE regs2 (9%bv : bv 5) 9%nat R9 X9.
srxbdk_kreg HS EE regs2 (18%bv : bv 5) 18%nat R18 X18.
srxbdk_kreg HS EE regs2 (19%bv : bv 5) 19%nat R19 X19.
srxbdk_kreg HS EE regs2 (20%bv : bv 5) 20%nat R20 X20.
srxbdk_kreg HS EE regs2 (21%bv : bv 5) 21%nat R21 X21.
srxbdk_kreg HS EE regs2 (22%bv : bv 5) 22%nat R22 X22.
srxbdk_kreg HS EE regs2 (23%bv : bv 5) 23%nat R23 X23.
srxbdk_kreg HS EE regs2 (25%bv : bv 5) 25%nat R25 X25.
srxbdk_kreg HS EE regs2 (26%bv : bv 5) 26%nat R26 X26.
srxbdk_kreg HS EE regs2 (27%bv : bv 5) 27%nat R27 X27.
srxbdk_reg HS (24%bv : bv 5) (w64 (SRX_S + 116)) X24
  ltac:(rewrite denot_lit_U; f_equal;
        rewrite (U_atom_off (srxbd_E regs2 Bw) 20%nat SRX_S 116
          ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20)) by lia; reflexivity).
assert (DSH : (SRX_S + 116) / 8 = 769750) by (vm_compute; reflexivity).
srxbdk_reg HS (12%bv : bv 5) (w64 (SHADOW_OFF + (SRX_S + 116) / 8)) X12
  ltac:(exact (srxbdk_denot_shadow (srxbd_E regs2 Bw) 20%nat 27%nat SRX_S 116 SHADOW_OFF
          ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20)
          ltac:(rewrite (EE 27%nat 27%bv eq_refl); exact R27)
          ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
          ltac:(unfold SHADOW_OFF; lia))).
srxbdk_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_desk_known Bw)) X10
  ltac:(exact (srxbd_sext (srxbd_E regs2 Bw) Bw (srxbd_ew33 regs2 Bw))).
(* run 1 wrote no byte *)
assert (KGx : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a) /\
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)).
{ apply (srxbdk_kept_run W2 _ _ mem2 (ms_mem ms) HFr); [|exact HG].
  intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr];
    [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
  destruct Hr. }
destruct KGx as [KD1 GR1].
clear HF HFr HG. rename ms into msA.
assert (HtwA : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msA)) Bw)
  by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw | intros x _; exact (KD1 x)]).
destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e (ms_mem msA) _ (fun _ : Z => False)
  HLAWS HFIX HCUR HRD HRDF HFB H0 HJ ltac:(intros a HZ; destruct HZ)
  ltac:(intros a _ _; exact (KD1 a)) GR1) as (CURA & RDA & RDFA & FBA).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
(* +0x2fc: `beq a0, zero` on the sign-extended desk_known *)
pmkst HS.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXBD_C1)) mm rom) mdx) Q) end.
clear HS SHOK HEI.
pose proof (srxbd_entry0 W2 (ms_regs msA) (ms_mem msA) SRXBD_C1) as HS.
assert (HEI : img_env VAL A_LIM (srxbd_E0 (ms_regs msA))) by apply srxbd_env0.
assert (SHOK : sh_ok segs SRXBD_Bx (@nil shent) (srxbd_E0 (ms_regs msA)) (mrestrict (w_H W2) (ms_mem msA)))
  by constructor.
assert (D10 : sv_denot (srxbd_E0 (ms_regs msA)) (SOff 10 0) = Z_to_bv 64 (TW.S_desk_known Bw))
  by (cbn [sv_denot]; rewrite (srxbd_ew0 (ms_regs msA) 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
      exact X10).
psrr_branch_tok RUN BR HS SHOK SRXBD_B0.
- (* desk_known = 0: one instruction to the learn cut *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbd_E0 (ms_regs msA)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (srxbd_eqb0 _ (srxbd_dk_range Bw)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SRXBD_B0 SRXB_LEARN.
  { srxbdk_awr_rs. apply awr_ok_x_nil. }
  assert (EE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
    ew (srxbd_E0 (ms_regs msA)) n = YK11.getr (ms_regs msA) rr)
    by (intros n rr Hn; exact (srxbd_ew0 (ms_regs msA) n rr Hn)).
  srxbdk_kreg HS EE0 (ms_regs msA) (2%bv : bv 5) 2%nat X2 Y2.
  srxbdk_kreg HS EE0 (ms_regs msA) (3%bv : bv 5) 3%nat X3 Y3.
  srxbdk_kreg HS EE0 (ms_regs msA) (4%bv : bv 5) 4%nat X4 Y4.
  srxbdk_kreg HS EE0 (ms_regs msA) (8%bv : bv 5) 8%nat X8 Y8.
  srxbdk_kreg HS EE0 (ms_regs msA) (9%bv : bv 5) 9%nat X9 Y9.
  srxbdk_kreg HS EE0 (ms_regs msA) (12%bv : bv 5) 12%nat X12 Y12.
  srxbdk_kreg HS EE0 (ms_regs msA) (18%bv : bv 5) 18%nat X18 Y18.
  srxbdk_kreg HS EE0 (ms_regs msA) (19%bv : bv 5) 19%nat X19 Y19.
  srxbdk_kreg HS EE0 (ms_regs msA) (20%bv : bv 5) 20%nat X20 Y20.
  srxbdk_kreg HS EE0 (ms_regs msA) (21%bv : bv 5) 21%nat X21 Y21.
  srxbdk_kreg HS EE0 (ms_regs msA) (22%bv : bv 5) 22%nat X22 Y22.
  srxbdk_kreg HS EE0 (ms_regs msA) (23%bv : bv 5) 23%nat X23 Y23.
  srxbdk_kreg HS EE0 (ms_regs msA) (24%bv : bv 5) 24%nat X24 Y24.
  srxbdk_kreg HS EE0 (ms_regs msA) (25%bv : bv 5) 25%nat X25 Y25.
  srxbdk_kreg HS EE0 (ms_regs msA) (26%bv : bv 5) 26%nat X26 Y26.
  srxbdk_kreg HS EE0 (ms_regs msA) (27%bv : bv 5) 27%nat X27 Y27.
  assert (KGx : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) (ms_mem msA) a) /\
    (forall a, apresent (w_H W2) (ms_mem msA) a -> apresent (w_H W2) (ms_mem ms) a)).
  { apply (srxbdk_kept_run W2 _ _ (ms_mem msA) (ms_mem ms) HFr); [|exact HG].
    intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
    repeat (destruct Hr as [Hr | Hr];
      [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
    destruct Hr. }
  destruct KGx as [KD2 GR2].
  clear HF HFr HG. rename ms into msB.
  assert (HtwB : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msB)) Bw)
    by (apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msA))); [exact HtwA | intros x _; exact (KD2 x)]).
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msA) _ e (ms_mem msB) _ (fun _ : Z => False)
    HLAWS HFIX CURA RDA RDFA FBA H0 HJ ltac:(intros a HZ; destruct HZ)
    ltac:(intros a _ _; exact (KD2 a)) GR2) as (CURB & RDB & RDFB & FBB).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_LEARN)) mm rom) mdx) Q) end.
  apply (LEARN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 (ms_mem msB) _ e (ms_regs msB) HFIX CURB RDB RDFB FBB HtwB H0 HMAC Hc).
  unfold srxb_regs_learn, srxb_regs_desk, srxb_regs_base, srxb_regs_core.
  refine (conj (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25 (conj Y26 Y27)))))))))) (conj Y21 Y22)) Y23) (conj Y24 Y12)).
  + exact Y3.
  + exact Y4.
- (* desk_known <> 0: run 2 and the bcmp call *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbd_E0 (ms_regs msA)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (srxbd_eqb0 _ (srxbd_dk_range Bw)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK SRXBD_B0.
  { srxbdk_awr_rs. apply awr_ok_x_nil. }
  assert (EE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
    ew (srxbd_E0 (ms_regs msA)) n = YK11.getr (ms_regs msA) rr)
    by (intros n rr Hn; exact (srxbd_ew0 (ms_regs msA) n rr Hn)).
  srxbdk_kreg HS EE0 (ms_regs msA) (3%bv : bv 5) 3%nat X3 Y3.
  srxbdk_kreg HS EE0 (ms_regs msA) (4%bv : bv 5) 4%nat X4 Y4.
  srxbdk_kreg HS EE0 (ms_regs msA) (8%bv : bv 5) 8%nat X8 Y8.
  srxbdk_kreg HS EE0 (ms_regs msA) (9%bv : bv 5) 9%nat X9 Y9.
  srxbdk_kreg HS EE0 (ms_regs msA) (18%bv : bv 5) 18%nat X18 Y18.
  srxbdk_kreg HS EE0 (ms_regs msA) (19%bv : bv 5) 19%nat X19 Y19.
  srxbdk_kreg HS EE0 (ms_regs msA) (20%bv : bv 5) 20%nat X20 Y20.
  srxbdk_kreg HS EE0 (ms_regs msA) (21%bv : bv 5) 21%nat X21 Y21.
  srxbdk_kreg HS EE0 (ms_regs msA) (22%bv : bv 5) 22%nat X22 Y22.
  srxbdk_kreg HS EE0 (ms_regs msA) (23%bv : bv 5) 23%nat X23 Y23.
  srxbdk_kreg HS EE0 (ms_regs msA) (24%bv : bv 5) 24%nat X24 Y24.
  srxbdk_kreg HS EE0 (ms_regs msA) (25%bv : bv 5) 25%nat X25 Y25.
  srxbdk_kreg HS EE0 (ms_regs msA) (26%bv : bv 5) 26%nat X26 Y26.
  srxbdk_kreg HS EE0 (ms_regs msA) (27%bv : bv 5) 27%nat X27 Y27.
  srxbdk_reg HS (2%bv : bv 5) (w64 sp1) Y2
    ltac:(cbn [sv_denot]; rewrite (EE0 2%nat 2%bv eq_refl), X2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  srxbdk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26612)) Y1 ltac:(apply codeptr_val; exact HEI).
  srxbdk_reg HS (10%bv : bv 5) (w64 (F + SRX_F + 6)) Y10
    ltac:(cbn [sv_denot]; rewrite (EE0 23%nat 23%bv eq_refl), X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  srxbdk_reg HS (11%bv : bv 5) (w64 (SRX_S + 120)) Y11
    ltac:(rewrite denot_lit_U; f_equal;
          rewrite (U_atom_off (srxbd_E0 (ms_regs msA)) 20%nat SRX_S 120
            ltac:(rewrite (EE0 20%nat 20%bv eq_refl); exact X20)) by lia; reflexivity).
  srxbdk_reg HS (12%bv : bv 5) (w64 6) Y12b ltac:(cbn [sv_denot]; reflexivity).
  assert (KGx : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) (ms_mem msA) a) /\
    (forall a, apresent (w_H W2) (ms_mem msA) a -> apresent (w_H W2) (ms_mem ms) a)).
  { apply (srxbdk_kept_run W2 _ _ (ms_mem msA) (ms_mem ms) HFr); [|exact HG].
    intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
    repeat (destruct Hr as [Hr | Hr];
      [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
    destruct Hr. }
  destruct KGx as [KD2 GR2].
  clear HF HFr HG. rename ms into msB.
  assert (HtwB : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msB)) Bw)
    by (apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msA))); [exact HtwA | intros x _; exact (KD2 x)]).
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msA) _ e (ms_mem msB) _ (fun _ : Z => False)
    HLAWS HFIX CURA RDA RDFA FBA H0 HJ ltac:(intros a HZ; destruct HZ)
    ltac:(intros a _ _; exact (KD2 a)) GR2) as (CURB & RDB & RDFB & FBB).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  (* the bcmp call at +0x30c *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
      (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
  assert (Hsp1b : spZ (ms_regs msB) = sp0 + (sp1 - sp0))
    by (unfold spZ; rewrite Y2; rewrite unsigned_lit_small by lia; lia).
  destruct RDFB as (RDFv & RDFa & RDFh & RDFm & RDF0 & RDF63).
  assert (D1 : (SRX_S + 120) / 64 * 64 = SRX_S + 64) by (vm_compute; reflexivity).
  assert (D2 : (SRX_S + 120 + 6 - 1) / 64 * 64 = SRX_S + 64) by (vm_compute; reflexivity).
  destruct (decode_zshadow_ra B ly2 S2 W2 (ms_mem msB) _ SRX_S (SRX_S + TW.SZ_g_s) (SRX_S + 120) 6 HARB
    (proj1 HSC) ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as [RAy HULLy].
  eapply SRr_bind.
  { apply (srxbdk_bcmp B STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 (ms_mem msB) _ (k + e)
      (ms_regs msB) (F + SRX_F + 6) (SRX_S + 120) 6 (sp1 - sp0) (Z_to_bv 64 (BASE + 26612))
      LAWS (ABCMP fx) HJ Y10 Y11 Y12b).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp1b.
    - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32. rewrite Hs1m, Z.add_0_r in D32.
      pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16. rewrite Hsp0a, Z.add_0_r in D16.
      replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult.
    - lia.
    - lia.
    - rewrite Y3. exact Hgp.
    - rewrite Y4. exact Htp.
    - exact Y1.
    - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - intros a Ha. split; [apply RDFv; lia|]. rewrite Hsp1b. lia.
    - intros a Ha. split.
      + exact (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw
          (srxbdk_inG a ltac:(unfold TW.SZ_g_s; lia)) (w_H W2) (ms_mem msB)).
      + rewrite Hsp1b. lia.
    - intros a Ha. lia.
    - intros a Ha. lia.
    - unfold amem_range in RDFm |- *. destruct RDFm as [Hmr | Hmr]; [left | right]; lia.
    - left. unfold kLowMemEnd. lia.
    - exact (range_addressable_sub _ _ (F + SRX_F) FRAME_F_SIZE (F + SRX_F + 6) 6 RDFa ltac:(lia) ltac:(lia)).
    - intros _. exact (trans_hull_sub _ (F + SRX_F) FRAME_F_SIZE (F + SRX_F + 6) 6 RDFh ltac:(lia) ltac:(lia)).
    - exact RAy.
    - intros _. exact HULLy. }
  cbv beta. intros Wq cq _ (-> & regs3 & mem3 & md3 & -> & HJ3 & v & HP3 & Hres3 & Hcmp3 & Heff3 & Hpres3).
  (* what the wrapper kept: every byte outside its window below sp1 *)
  assert (KD3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1 + 32) ->
    aview segs (w_H W2) mem3 a = aview segs (w_H W2) (ms_mem msB) a).
  { intros a Ha Hn. apply Heff3; [exact Ha|]. lia. }
  assert (HtwC : tw_at TMAP_B (aview segs (w_H W2) mem3) Bw).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msB))); [exact HtwB|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KD3; lia. }
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msB) _ e mem3 md3 (fun a : Z => sp1 - 2 * ESTACK <= a < sp1 + 32)
    HLAWS HFIX CURB RDB (conj RDFv (conj RDFa (conj RDFh (conj RDFm (conj RDF0 RDF63))))) FBB H0 HJ3
    ltac:(intros a HZ; left; exact HZ) ltac:(intros a Ha Hn; exact (KD3 a Ha Hn)) Hpres3)
    as (CURC & RDC & RDFC & FBC).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARC.
  (* the wrapper's result is the model's memeq of :279 *)
  assert (HMEQ : v = w64 0 <-> TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true).
  { rewrite Hcmp3. exact (srxbdk_bcmp_memeq W2 (ms_mem msB) F buf b fj Bw H0 FBB HtwB). }
  assert (HPRES : aregs_preserved (ms_regs msB) regs3) by exact HP3.
  assert (Z2 : YK11.getr regs3 2 = w64 sp1)
    by (transitivity (YK11.getr (ms_regs msB) 2);
        [exact (HPRES 2 ltac:(unfold acallee_saved; lia)) | exact Y2]).
  assert (Z8 : YK11.getr regs3 8 = w64 (spZ regs))
    by (transitivity (YK11.getr (ms_regs msB) 8);
        [exact (HPRES 8 ltac:(unfold acallee_saved; lia)) | exact Y8]).
  assert (Z9 : YK11.getr regs3 9 = w64 sp1)
    by (transitivity (YK11.getr (ms_regs msB) 9);
        [exact (HPRES 9 ltac:(unfold acallee_saved; lia)) | exact Y9]).
  assert (Z18 : YK11.getr regs3 18 = w64 F)
    by (transitivity (YK11.getr (ms_regs msB) 18);
        [exact (HPRES 18 ltac:(unfold acallee_saved; lia)) | exact Y18]).
  assert (Z19 : YK11.getr regs3 19 = w64 now)
    by (transitivity (YK11.getr (ms_regs msB) 19);
        [exact (HPRES 19 ltac:(unfold acallee_saved; lia)) | exact Y19]).
  assert (Z20 : YK11.getr regs3 20 = w64 SRX_S)
    by (transitivity (YK11.getr (ms_regs msB) 20);
        [exact (HPRES 20 ltac:(unfold acallee_saved; lia)) | exact Y20]).
  assert (Z21 : YK11.getr regs3 21 = w64 (SRX_S + 18152))
    by (transitivity (YK11.getr (ms_regs msB) 21);
        [exact (HPRES 21 ltac:(unfold acallee_saved; lia)) | exact Y21]).
  assert (Z22 : YK11.getr regs3 22 = w64 (F + SRX_F))
    by (transitivity (YK11.getr (ms_regs msB) 22);
        [exact (HPRES 22 ltac:(unfold acallee_saved; lia)) | exact Y22]).
  assert (Z25 : YK11.getr regs3 25 = w64 (SHADOW_OFF + F / 8))
    by (transitivity (YK11.getr (ms_regs msB) 25);
        [exact (HPRES 25 ltac:(unfold acallee_saved; lia)) | exact Y25]).
  assert (Z26 : YK11.getr regs3 26 = w64 F)
    by (transitivity (YK11.getr (ms_regs msB) 26);
        [exact (HPRES 26 ltac:(unfold acallee_saved; lia)) | exact Y26]).
  assert (Z27 : YK11.getr regs3 27 = w64 SHADOW_OFF)
    by (transitivity (YK11.getr (ms_regs msB) 27);
        [exact (HPRES 27 ltac:(unfold acallee_saved; lia)) | exact Y27]).
  assert (Z3 : YK11.getr regs3 3 = w64 (as_gp B))
    by (transitivity (YK11.getr (ms_regs msB) 3);
        [exact (HPRES 3 ltac:(unfold acallee_saved; lia)) | rewrite Y3; exact Hgp]).
  assert (Z4 : YK11.getr regs3 4 = w64 (as_tp B))
    by (transitivity (YK11.getr (ms_regs msB) 4);
        [exact (HPRES 4 ltac:(unfold acallee_saved; lia)) | rewrite Y4; exact Htp]).
  (* +0x310: `beq a0, zero` on the wrapper's result *)
  destruct (srxbd_entry2 ly2 S2 W2 regs3 mem3 md3 HSC HARC Z21 Z27) as [HS2 SHOK2].
  clear HS SHOK HEI.
  rename HS2 into HS. rename SHOK2 into SHOK.
  assert (HEI : img_env VAL A_LIM (srxbd_E0 regs3)) by apply srxbd_env0.
  assert (D10b : sv_denot (srxbd_E0 regs3) (SOff 10 0) = v)
    by (cbn [sv_denot]; rewrite (srxbd_ew0 regs3 10%nat 10%bv eq_refl), Hres3, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* the MACs agree: one instruction to the closed cut *)
    cbn [branch_taken] in Hc0. rewrite D10b in Hc0.
    change (sv_denot (srxbd_E0 regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc0.
    assert (Hv0 : v = w64 0) by (apply bv_eq; unfold bv_eqb in Hc0; apply Z.eqb_eq in Hc0; exact Hc0).
    paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan SRXB_CLOSED.
    { srxbdk_awr_rs. apply awr_ok_x_nil. }
    assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
      ew (srxbd_E0 regs3) n = YK11.getr regs3 rr)
      by (intros n rr Hn; exact (srxbd_ew0 regs3 n rr Hn)).
    srxbdk_kreg HS EE3 regs3 (2%bv : bv 5) 2%nat Z2 V2.
    srxbdk_kreg HS EE3 regs3 (3%bv : bv 5) 3%nat Z3 V3.
    srxbdk_kreg HS EE3 regs3 (4%bv : bv 5) 4%nat Z4 V4.
    srxbdk_kreg HS EE3 regs3 (8%bv : bv 5) 8%nat Z8 V8.
    srxbdk_kreg HS EE3 regs3 (9%bv : bv 5) 9%nat Z9 V9.
    srxbdk_kreg HS EE3 regs3 (18%bv : bv 5) 18%nat Z18 V18.
    srxbdk_kreg HS EE3 regs3 (19%bv : bv 5) 19%nat Z19 V19.
    srxbdk_kreg HS EE3 regs3 (20%bv : bv 5) 20%nat Z20 V20.
    srxbdk_kreg HS EE3 regs3 (21%bv : bv 5) 21%nat Z21 V21.
    srxbdk_kreg HS EE3 regs3 (22%bv : bv 5) 22%nat Z22 V22.
    srxbdk_kreg HS EE3 regs3 (25%bv : bv 5) 25%nat Z25 V25.
    srxbdk_kreg HS EE3 regs3 (26%bv : bv 5) 26%nat Z26 V26.
    srxbdk_kreg HS EE3 regs3 (27%bv : bv 5) 27%nat Z27 V27.
    assert (KGx : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem3 a) /\
      (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms) a)).
    { apply (srxbdk_kept_run W2 _ _ mem3 (ms_mem ms) HFr); [|exact HG].
      intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
      repeat (destruct Hr as [Hr | Hr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
      destruct Hr. }
    destruct KGx as [KD4 GR4].
    clear HF HFr HG. rename ms into msD.
    assert (HtwD : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msD)) Bw)
      by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem3)); [exact HtwC | intros x _; exact (KD4 x)]).
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 mem3 md3 e (ms_mem msD) _ (fun _ : Z => False)
      HLAWS HFIX CURC RDC RDFC FBC H0 HJ3 ltac:(intros a HZ; destruct HZ)
      ltac:(intros a _ _; exact (KD4 a)) GR4) as (CURD & RDD & RDFD & FBD).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_CLOSED)) mm rom) mdx) Q) end.
    apply (CLOSED HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bw
      pos sp1 F ly2 S2 W2 (ms_mem msD) _ e (ms_regs msD) HFIX CURD RDD RDFD FBD HtwD Hfn Hinv).
    * split; [exact H0|]. split; [exact HMAC|]. left.
      split; [exact Hc | split; [exact (proj1 HMEQ Hv0) | reflexivity]].
    * unfold srxb_regs_base, srxb_regs_core.
      refine (conj (conj V2 (conj _ (conj _ (conj V8 (conj V9 (conj V18 (conj V19 (conj V20 (conj V25 (conj V26 V27)))))))))) (conj V21 V22)).
      { rewrite V3. symmetry. exact Hgp. }
      { rewrite V4. symmetry. exact Htp. }
  + (* the MACs differ: run 3 to the ignored cut *)
    cbn [branch_taken] in Hc0. rewrite D10b in Hc0.
    change (sv_denot (srxbd_E0 regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc0.
    assert (Hvn : v <> w64 0)
      by (intros HH; rewrite HH in Hc0; unfold bv_eqb in Hc0; rewrite Z.eqb_refl in Hc0; discriminate Hc0).
    assert (HQ : TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = false).
    { destruct (TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw)) eqn:EQ; [|reflexivity].
      exfalso. exact (Hvn (proj2 HMEQ eq_refl)). }
    pose proof (srxb_m_desk timg_B TF Bw b now H0 HMAC Hc HQ) as HMD.
    rewrite Hm in HMD.
    destruct (srxb_some_inv Bw' (srx_ign Bw) r DLib.DIGINET_OK HMD) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan SRXB_IGN.
    { srxbdk_awr_rs. apply awr_ok_x_nil. }
    assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
      ew (srxbd_E0 regs3) n = YK11.getr regs3 rr)
      by (intros n rr Hn; exact (srxbd_ew0 regs3 n rr Hn)).
    srxbdk_kreg HS EE3 regs3 (2%bv : bv 5) 2%nat Z2 V2.
    srxbdk_kreg HS EE3 regs3 (3%bv : bv 5) 3%nat Z3 V3.
    srxbdk_kreg HS EE3 regs3 (4%bv : bv 5) 4%nat Z4 V4.
    srxbdk_kreg HS EE3 regs3 (8%bv : bv 5) 8%nat Z8 V8.
    srxbdk_kreg HS EE3 regs3 (9%bv : bv 5) 9%nat Z9 V9.
    srxbdk_kreg HS EE3 regs3 (18%bv : bv 5) 18%nat Z18 V18.
    srxbdk_kreg HS EE3 regs3 (19%bv : bv 5) 19%nat Z19 V19.
    srxbdk_kreg HS EE3 regs3 (20%bv : bv 5) 20%nat Z20 V20.
    srxbdk_kreg HS EE3 regs3 (21%bv : bv 5) 21%nat Z21 V21.
    srxbdk_kreg HS EE3 regs3 (22%bv : bv 5) 22%nat Z22 V22.
    srxbdk_kreg HS EE3 regs3 (25%bv : bv 5) 25%nat Z25 V25.
    srxbdk_kreg HS EE3 regs3 (26%bv : bv 5) 26%nat Z26 V26.
    srxbdk_kreg HS EE3 regs3 (27%bv : bv 5) 27%nat Z27 V27.
    srxbdk_reg HS (10%bv : bv 5) (w64 0) V10 ltac:(cbn [sv_denot]; reflexivity).
    srxbdk_reg HS (11%bv : bv 5) (w64 SRXB_RXIGN) V11
      ltac:(rewrite denot_lit_U; f_equal;
            rewrite (U_atom_off (srxbd_E0 regs3) 21%nat (SRX_S + 18152) 32
              ltac:(rewrite (EE3 21%nat 21%bv eq_refl); exact Z21)) by lia;
            unfold SRXB_RXIGN; lia).
    assert (KGx : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem3 a) /\
      (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms) a)).
    { apply (srxbdk_kept_run W2 _ _ mem3 (ms_mem ms) HFr); [|exact HG].
      intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
      repeat (destruct Hr as [Hr | Hr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
      destruct Hr. }
    destruct KGx as [KD4 GR4].
    clear HF HFr HG. rename ms into msD.
    assert (HtwD : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msD)) Bw)
      by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem3)); [exact HtwC | intros x _; exact (KD4 x)]).
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 mem3 md3 e (ms_mem msD) _ (fun _ : Z => False)
      HLAWS HFIX CURC RDC RDFC FBC H0 HJ3 ltac:(intros a HZ; destruct HZ)
      ltac:(intros a _ _; exact (KD4 a)) GR4) as (CURD & RDD & RDFD & FBD).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_IGN)) mm rom) mdx) Q) end.
    apply (IGN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bw
      pos sp1 F ly2 S2 W2 (ms_mem msD) _ e (ms_regs msD) HFIX CURD HtwD Hfn EBw).
    unfold srxb_regs_ign, srxb_regs_base, srxb_regs_core.
    refine (conj (conj (conj V2 (conj _ (conj _ (conj V8 (conj V9 (conj V18 (conj V19 (conj V20 (conj V25 (conj V26 V27)))))))))) (conj V21 V22)) (conj _ V11)).
    * rewrite V3. symmetry. exact Hgp.
    * rewrite V4. symmetry. exact Htp.
    * rewrite V10, Er. reflexivity.
Qed.

End d.

(* The desk piece of the image-B walk of diginet_session_rx (SrxBCut.v srxb_desk_stmt), at every machine, run
   ceiling, record and meter. *)
Theorem srxb_desk_ok : forall fx rc B MT, @srxb_desk_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxbd_holds fx rc B MT). Qed.
