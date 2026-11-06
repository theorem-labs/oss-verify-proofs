(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names, addresses and numbers changed; 177 of its 853 lines of code are new or changed and 534 lines of the source are left out. *)
(* TickBRetx: the retransmit piece of diginet_session_tick's image-B G-form walk, tick_retx : tick_retx_stmt
   (TickCutB.v), code +0x34c .. +0x440 (0x893e8 .. 0x894dc) and +0x594 .. +0x5bc (0x89630 .. 0x89658) of
   fuzz_transport.asan-ubsan. Run 1 (PaRun token engine) from the retx cut stores retries + 1 at s + 1748, the two retry
   bytes at s + 242 / s + 243 (the UBSan pointer-overflow checks at +0x364 and +0x388 not taken: s + 216 is the literal
   0x5df718), now at s + 1752 and stats.tx_retransmits + 1 at s + 18232, loads the inflight length, g_s.io.ctx and
   g_s.io.send, saves s + 18144 in s9, and stops at `jalr a4` (+0x424), which calls io_send through the premise
   transport_io_send_cg at TI.ti_io_send timg_B (the same G journal; the call's kept facts fold with
   TransportGCg.v dk_kept_trans_nf_g). Run 2 from the return (+0x428): on a result of 0 it adds 1 to stats.tx_frames at
   s + 18192 (+0x594 .. +0x5bc) and reaches the tail cut; on -EIO it sets s10 = r and reaches the epilogue cut
   (io_send's result is 0 or -EIO: TModel/TIoSendFail.v io_send_m_ret). The model, the run states' definitions and the
   byte facts are TickBRetx_ent.v's; the run states are proved at their machine states here (rx_entry1, rx_entry2z,
   rx_entry2n), with the kept facts of a step whose written bytes lie in G (rx_kept_G, TransportGFrame.v
   dk_kept_step_gw); the shared B kit is TickBKit.v (sn_chunk_valB, sn_winB, sn_regB, slh_inGB, tkb_iosend_G). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0a YO0c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
io_send_cg set_state_cg take_cg send_data_cg diginet_session_tick_cg TickCutB TickBKit TickBRetx_ent.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TIoSendFail TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TIF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoSendFail.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the run's entry states and the kept facts ---- *)

Section rx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition rx_E1 (regs : bvmap 5 word) (Bw : list byte) (now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (rx_vals1 Bw now)).
(* The valuation of run 2: the registers at the return, then stats.tx_frames of io_send's world (atom 32). *)
Definition rx_E2 (regs : bvmap 5 word) (B1 : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8)]).

(* g_s's shadow byte of the granule at T is 0 at every AR state. *)
Lemma rx_zsh : forall ly S (W : world segs) mem md T X, trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s -> T mod 8 = 0 -> FCells.shadow_addr T = X ->
  val_mem segs (mrestrict (w_H W) mem) X 1 0.
Proof.
  intros ly S W mem md T X HSC HAR H1 H2 H3 <-. apply rx_vm0.
  exact (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR H3 H1 H2 HSC).
Qed.

Lemma rx_entry1_0 : forall ly S (W : world segs) regs mem md Bw now spv,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (spv + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  st_ok_pi segs VAL (rx_E1 regs Bw now) (mkSS TICK_RETX sr_atoms RX_REGS1 None RX_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_RETX)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw now spv HSC HAR Htw R9 Hsp Hsp32 Hnw Hnr.
  assert (CS : TICK_S = 6157888) by reflexivity.
  set (E := rx_E1 regs Bw now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, rx_E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = spv)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (rx_vals1 Bw now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, rx_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth rx_vals1] in E32, E33, E34, E35, E36.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 64) 8) as R33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 72) 8) as R34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1736) 8) as R35.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18232) 8) as R36.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R33, R34, R35, R36.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (GW : forall o, TICK_S <= o < TICK_S + TW.SZ_g_s -> writable_at segs (mrestrict (w_H W) mem) o)
    by (intros o Ho; exact (gx_rw_writable segs TG.G_HARNESS_B o G_HARNESS_B_rw (slh_inGB o Ho) _)).
  assert (TWR : forall k (m : nat), 0 <= k -> k + Z.of_nat m <= TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (TICK_S + k) m (TW.u_at Bw (TW.OFF_g_s + k) m))
    by (intros k m Hk Hkm;
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s k m TMAP_B_ok Htw TMAP_B_g_s Hk Hkm)).
  assert (ZS : forall T X, TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s -> T mod 8 = 0 -> FCells.shadow_addr T = X ->
    val_mem segs (mrestrict (w_H W) mem) X 1 0)
    by (intros T X H1 H2 H3 H4; exact (rx_zsh ly S W mem md T X HSC HAR H1 H2 H3 H4)).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks RX_R_now RX_R_io RX_R_fb RX_R_ifl
        RX_R_txr RX_R_sh64 RX_R_sh242 RX_R_sh1736 RX_R_sh18232 base_val]; rewrite ?U9.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ spv 56 8 (SOff 32 0) now); [apply DEN; [exact E32 | exact Hnr] | exact Hnr | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem (spv + 56) now Hnw).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 64) 8 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 64) 8));
          [apply DEN; [exact E33 | exact R33] | exact R33 | lia |].
        rewrite Z.add_0_l. exact (TWR 64 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 72) 8 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 72) 8));
          [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
        rewrite Z.add_0_l. exact (TWR 72 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply GW. unfold TW.SZ_g_s. lia.
    + split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply GW. unfold TW.SZ_g_s. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E _ 0 (TICK_S + 1736) 8 (SOff 35 0) (TW.u_at Bw (TW.OFF_g_s + 1736) 8));
          [apply DEN; [exact E35 | exact R35] | exact R35 | lia |].
        rewrite Z.add_0_l. exact (TWR 1736 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply GW. unfold TW.SZ_g_s. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val segs E _ 0 (TICK_S + 18232) 8 (SOff 36 0) (TW.u_at Bw (TW.OFF_g_s + 18232) 8));
          [apply DEN; [exact E36 | exact R36] | exact R36 | lia |].
        rewrite Z.add_0_l. exact (TWR 18232 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + unfold RX_SH64. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E _ 0 2148220624 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (ZS (TICK_S + 64) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
      * apply (chunk_ok_val segs E _ 0 (2148220624 + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (ZS (TICK_S + 72) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
    + unfold RX_SH242. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ 0 2148220646 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
      exact (ZS (TICK_S + 240) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
    + unfold RX_SH1736. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val segs E _ 0 2148220833 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (ZS (TICK_S + 1736) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
      * apply (chunk_ok_val segs E _ 0 (2148220833 + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (ZS (TICK_S + 1744) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
      * apply (chunk_ok_val segs E _ 0 (2148220833 + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (ZS (TICK_S + 1752) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
    + unfold RX_SH18232. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ 0 2148222895 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
      exact (ZS (TICK_S + 18232) _ ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(reflexivity) ltac:(reflexivity)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, RX_REGS1, RX_R_now, RX_R_io, RX_R_fb, RX_R_ifl, RX_R_txr, RX_R_sh64, RX_R_sh242, RX_R_sh1736,
      RX_R_sh18232.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold RX_SH64, RX_SH242, RX_SH1736, RX_SH18232. repeat split; first [exact I | lia].
  - unfold RX_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma rx_entry1 : forall ly S (W : world segs) regs mem md Bw now spv,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (spv + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  YK11.getr regs 13 = w64 (SHADOW_OFF + (TICK_S + 1752) / 8) ->
  YK11.getr regs 14 = w64 (SHADOW_OFF + (TICK_S + 1748) / 8) ->
  YK11.getr regs 17 = w64 (TICK_S + 18144) -> YK11.getr regs 20 = w64 TICK_S ->
  YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (rx_E1 regs Bw now) ss_rx1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_RETX)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw now spv HSC HAR Htw R9 Hsp Hsp32 Hnw Hnr R13 R14 R17 R20 R24.
  rewrite restrict_mkst_fx.
  pose proof (rx_entry1_0 ly S W regs mem md Bw now spv HSC HAR Htw R9 Hsp Hsp32 Hnw Hnr) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 13) (SHADOW_OFF + (TICK_S + 1752) / 8) H0 R13 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 14) (SHADOW_OFF + (TICK_S + 1748) / 8) H1 R14 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 17) (TICK_S + 18144) H2 R17 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H3 R20 eq_refl) as H4.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H4 R24 eq_refl) as H5.
  exact H5.
Qed.

(* t0 and t1 at s1 + 48 / s1 + 40, read back after io_send. *)
Lemma rx_t01_ok : forall E (W : world segs) mem spv,
  bv_unsigned (ew E 9) = spv -> 2 ^ 46 <= spv <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (spv + 48) = Some (TICK_S + 212) ->
  rdword (aview segs (w_H W) mem) (spv + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8) ->
  region_ok segs E (mrestrict (w_H W) mem) RX_R_t01.
Proof.
  intros E W mem spv U9 Hsp H48 H40. unfold region_ok, RX_R_t01.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val segs E _ spv 40 8 (SLit (SHADOW_OFF + (TICK_S + 212) / 8)) (SHADOW_OFF + (TICK_S + 212) / 8));
      [reflexivity | split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem (spv + 40) _ H40).
  - apply (chunk_ok_val segs E _ spv 48 8 (SLit (TICK_S + 212)) (TICK_S + 212));
      [reflexivity | split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem (spv + 48) _ H48).
Qed.

Lemma rx_entry2z : forall ly S (W : world segs) regs mem md B1 spv,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) B1 ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (spv + 48) = Some (TICK_S + 212) ->
  rdword (aview segs (w_H W) mem) (spv + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8) ->
  YK11.getr regs 10 = Z_to_bv 64 0 -> YK11.getr regs 25 = w64 (TICK_S + 18144) ->
  YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (rx_E2 regs B1) ss_rx2z
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RX_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md B1 spv HSC HAR Htw R9 Hsp Hsp32 H48 H40 R10 R25 R24.
  assert (CS : TICK_S = 6157888) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := rx_E2 regs B1).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, rx_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = spv)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8))
    by (unfold E, rx_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range B1 (TW.OFF_g_s + 18192) 8) as R32. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
  assert (H0 : st_ok_pi segs VAL E (mkSS RX_RET sr_atoms [RX_R_t01; RX_R_txf; RX_R_sh18192] None RX_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RX_RET)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [exact (rx_t01_ok E W mem spv U9 Hsp H48 H40)|].
      constructor; [|constructor; [|constructor]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks RX_R_txf RX_R_sh18192 base_val].
      + split; [lia|]. split; [lia|]. split.
        * intros o Ho. exact (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw
            (slh_inGB (0 + o) ltac:(unfold TW.SZ_g_s; lia)) _).
        * constructor; [|constructor].
          apply (chunk_ok_val segs E _ 0 (TICK_S + 18192) 8 (SOff 32 0) (TW.u_at B1 (TW.OFF_g_s + 18192) 8));
            [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by exact R32; reflexivity | exact R32 | lia |].
          rewrite Z.add_0_l.
          exact (tw_read_val segs _ TMAP_B B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 TMAP_B_ok Htw TMAP_B_g_s
            ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      + unfold RX_SH18192. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ 0 2148222890 1 (SLit 0) 0); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
        exact (rx_zsh ly S W mem md (TICK_S + 18192) _ HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
          ltac:(reflexivity) ltac:(reflexivity)).
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, RX_R_t01, RX_R_txf, RX_R_sh18192.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold RX_SH18192. repeat split; first [exact I | lia].
    - unfold RX_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) 0 H0 R10 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (TICK_S + 18144) H1 R25 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H2 R24 eq_refl) as H3.
  exact H3.
Qed.

Lemma rx_entry2n : forall (W : world segs) regs mem B1 spv,
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (spv + 48) = Some (TICK_S + 212) ->
  rdword (aview segs (w_H W) mem) (spv + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8) ->
  YK11.getr regs 10 = Z_to_bv 64 (- 5) -> YK11.getr regs 25 = w64 (TICK_S + 18144) ->
  YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (rx_E2 regs B1) ss_rx2n
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RX_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem B1 spv R9 Hsp Hsp32 H48 H40 R10 R25 R24.
  rewrite restrict_mkst_fx.
  set (E := rx_E2 regs B1).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, rx_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = spv)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (H0 : st_ok_pi segs VAL E (mkSS RX_RET sr_atoms [RX_R_t01] None RX_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RX_RET)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [exact (rx_t01_ok E W mem spv U9 Hsp H48 H40) | constructor].
    - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
    - unfold RX_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) (- 5) H0 R10 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (TICK_S + 18144) H1 R25 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H2 R24 eq_refl) as H3.
  exact H3.
Qed.

(* trans_sh_any of a sub-range (the empty one included: its hull lies in the range's hull). *)
Lemma rx_sh_any_sub : forall q n q' n', trans_sh_any B q n -> q <= q' -> q' + n' <= q + n -> trans_sh_any B q' n'.
Proof.
  intros q n q' n' H H1 H2 ly S W mem md HAR. destruct (H ly S W mem md HAR) as [Ha Hh].
  split; [intros x Hx; apply Ha; lia | exact (trans_hull_sub _ q n q' n' Hh H1 H2)].
Qed.

(* A step whose changed bytes are all bytes of G keeps what the call keeps (TransportGFrame.v dk_kept_step_gw; a byte
   of G is an image byte below kLowMemEnd, so it is no block, frame or shadow byte and lies below the ceiling). *)
Lemma rx_kept_G : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) memX memY slo shi (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= slo ->
  (forall a, Zs a -> inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memY slo shi Eo.
Proof.
  intros lyc Sc W memc mdc W1 memX memY slo shi Eo Zs LAWS HG HAR Hslo HZ KP Hkp Hgr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W1 memX memY slo shi Eo Zs
    HAR KP Hkp Hgr).
  - intros a Ha Hc. exfalso. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG (HZ a Ha)) as Hl.
    unfold kLowMemEnd in *. lia.
  - intros b m i Hb Hi Ha. exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    destruct (HG _ (HZ _ Ha)) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) Hi').
  - intros a Ha Hi HnG _ _. exfalso. exact (HnG (HZ a Ha)).
  - intros cid pos a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
    destruct (HG _ (HZ a Ha)) as [Hi _].
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG (HZ a Ha)) as Hl.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr Hi).
    + pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* ---- the walk ---- *)

Lemma rx_holds : @tick_retx_stmt fx rc B MT.
Proof.
unfold tick_retx_stmt. intros TAIL EPI. unfold tick_retx_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGN).
pose proof CALLEES as (_ & _ & HIO & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & HRI & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnow1) & Hbl & HGK & Htw1) &
  Ht01 & Hinf & Hrx).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24) & R7 & R13 & R14 & R17).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TCA.TICK_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof (@YM05.alloc_ceiling_val rc) as [[CEIL _] _].
assert (CS : TICK_S = 6157888) by reflexivity.
assert (HTS : TICK_STK = 8896) by reflexivity.
assert (HIS : IOSEND_STK = 8512) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (rr := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HSPB : alloc_ceiling + 176 <= sp1 - IOSEND_STK /\ sp1 + 192 <= spZ regs /\ spZ regs <= 2 ^ 47) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr lyc TICK_CID pos) in *.
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  exact (trans_g_img x (slh_inGB x Hx2)). }
(* the model's facts on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (rx_model TF Bw now Bw' r Hrx) as (HLEN & HSEND & B1 & r0 & HIOM & HBR).
pose proof (rx_w_len Bw now HLB) as HLX.
assert (ELEN : TW.S_inflight_len (rx_w Bw now) = TW.u_at Bw (TW.OFF_g_s + 1736) 8).
{ unfold TW.S_inflight_len, TW.A_S_inflight_len.
  apply rx_w_rd; [exact HLB | | | |]; unfold TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
assert (EIOS : TW.S_io_send (rx_w Bw now) = TW.u_at Bw (TW.OFF_g_s + 72) 8).
{ unfold TW.S_io_send, TW.A_S_io_send.
  apply rx_w_rd; [exact HLB | | | |]; unfold TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1736) 8) as RN. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RN.
set (n := TW.S_inflight_len (rx_w Bw now)) in *.
set (frame := TW.sub (rx_w Bw now) TW.A_S_inflight_frame (Z.to_nat n)) in *.
assert (Hn0 : 0 <= n <= 1514) by (rewrite ELEN in *; lia).
assert (LENF : Z.of_nat (length frame) = n).
{ unfold frame. rewrite TWL.length_sub; [lia | unfold TW.A_S_inflight_frame, TW.OFF_g_s; lia |].
  rewrite HLX. unfold TW.A_S_inflight_frame, TW.OFF_g_s, TW.W_LEN. lia. }
(* run 1, +0x34c .. +0x424: retransmit's stores (the two pointer-overflow checks decided on s + 216), the loads of
   the length, ctx and send, s9 = s + 18144, up to `jalr a4` *)
pose proof (rx_entry1 lyc S2 W regs2 mem2 md2 Bw now sp1 HTC HAR2 Htw1 R9 ltac:(lia) (proj2 Hsp1) Hnow1 Hnow
  R13 R14 R17 R20 R24) as HS.
set (E0 := rx_E1 regs2 Bw now) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rx_E1; apply Eimg_env).
assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
  by (intros nn rr Hn; unfold E0, rx_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (rx_vals1 Bw now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, rx_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth rx_vals1] in E32, E34, E35, E36.
assert (SHOK : sh_ok segs RX_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ1 SHOK RX_B0.
{ rx_awr. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ rx_Z1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ rx_Z1 HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_winB Hiw Hx ltac:(unfold rx_Z1; rewrite CS; first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS3.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS4.
cbn [ms_mem restrict] in RS2, RS3, RS4.
clear HF HFr HG.
(* the bytes run 1 stored *)
pose proof (sn_chunk_valB E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158131 1 (SOff 7 1) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V243.
pose proof (sn_chunk_valB E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158130 1 (SAluw ALU_SRL (SOff 7 1) (SLit 8)) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V242.
pose proof (sn_chunk_valB E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6159636 4 (SOff 7 1) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V1748.
pose proof (sn_chunk_valB E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6159640 8 (SOff 32 0) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V1752.
pose proof (sn_chunk_valB E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6176120 8 (SOff 36 1) RS4
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V18232.
cbn [base_val] in V243, V242, V1748, V1752, V18232.
set (X := (bv_swrap 32 (TW.S_inflight_retries Bw) mod 2 ^ 64 + 1) mod 2 ^ 64).
assert (U7 : bv_unsigned (ew E0 7) = bv_swrap 32 (TW.S_inflight_retries Bw) mod 2 ^ 64)
  by (rewrite (EE 7%nat 7%bv eq_refl), R7; unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
assert (D71 : bv_unsigned (sv_denot E0 (SOff 7 1)) = X)
  by (cbn [sv_denot]; rewrite Z_to_bv_unsigned, U7; reflexivity).
assert (HX : 0 <= X < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (HXq : X mod 2 ^ 32 = rx_q Bw) by exact (rx_t2_lo (TW.S_inflight_retries Bw)).
assert (D242 : bv_unsigned (sv_denot E0 (SAluw ALU_SRL (SOff 7 1) (SLit 8))) = YO0a.srlw X 8).
{ cbn [sv_denot]. rewrite YO0c.srlw_rr_unsigned. fold (sv_denot E0 (SOff 7 1)). rewrite D71. reflexivity. }
assert (D32 : bv_unsigned (sv_denot E0 (SOff 32 0)) = now)
  by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, Z_to_bv_unsigned; apply bv_wrap_small; exact Hnow).
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18232) 8) as RT. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RT.
assert (D36 : bv_unsigned (sv_denot E0 (SOff 36 1)) = TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8 + 1)).
{ cbn [sv_denot]. rewrite E36, Z_to_bv_unsigned, Z_to_bv_unsigned. unfold TS0.u64.
  rewrite (bv_wrap_small 64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8)) by exact RT. reflexivity. }
rewrite D71 in V243, V1748. rewrite D242 in V242. rewrite D32 in V1752. rewrite D36 in V18232.
assert (S1 : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms) (TB_g_s + 1748 + Z.of_nat j) = Some (YO0f.le_byte (rx_q Bw) 4 j)).
{ intros j Hj. rewrite (rx_le_byte_cong (rx_q Bw) (X mod 2 ^ (8 * Z.of_N 4)) 4 j).
  - exact (rx_vm_view _ _ _ 4 _ j V1748 Hj).
  - change (8 * Z.of_nat 4) with 32. change (8 * Z.of_N 4) with 32. rewrite Zmod_mod, HXq.
    unfold rx_q, DSpec.u32. apply Zmod_mod. }
assert (S2b : forall j, (j < 1)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_s + 242 + Z.of_nat j) =
  Some (YO0f.le_byte (DSpec.u8 (Z.shiftr (DSpec.u16 (rx_q Bw)) 8)) 1 j)).
{ intros j Hj. rewrite (rx_le_byte_cong _ (YO0a.srlw X 8 mod 2 ^ (8 * Z.of_N 1)) 1 j).
  - exact (rx_vm_view _ _ _ 1 _ j V242 Hj).
  - change (8 * Z.of_nat 1) with 8. change (8 * Z.of_N 1) with 8. rewrite Zmod_mod.
    symmetry. exact (rx_hi_byte X (rx_q Bw) HX HXq). }
assert (S3b : forall j, (j < 1)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_s + 243 + Z.of_nat j) =
  Some (YO0f.le_byte (DSpec.u8 (DSpec.u16 (rx_q Bw))) 1 j)).
{ intros j Hj. rewrite (rx_le_byte_cong _ (X mod 2 ^ (8 * Z.of_N 1)) 1 j).
  - exact (rx_vm_view _ _ _ 1 _ j V243 Hj).
  - change (8 * Z.of_nat 1) with 8. change (8 * Z.of_N 1) with 8. rewrite Zmod_mod.
    symmetry. exact (rx_lo_byte X (rx_q Bw) HXq). }
assert (S4 : forall j, (j < 8)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_s + 1752 + Z.of_nat j) =
  Some (YO0f.le_byte now 8 j)).
{ intros j Hj. rewrite (rx_le_byte_cong now (now mod 2 ^ (8 * Z.of_N 8)) 8 j).
  - exact (rx_vm_view _ _ _ 8 _ j V1752 Hj).
  - change (8 * Z.of_nat 8) with 64. change (8 * Z.of_N 8) with 64. rewrite Zmod_mod. reflexivity. }
assert (S5 : forall j, (j < 8)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_s + 18232 + Z.of_nat j) =
  Some (YO0f.le_byte (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8 + 1)) 8 j)).
{ intros j Hj. rewrite (rx_le_byte_cong _ (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8 + 1) mod 2 ^ (8 * Z.of_N 8)) 8 j).
  - exact (rx_vm_view _ _ _ 8 _ j V18232 Hj).
  - change (8 * Z.of_nat 8) with 64. change (8 * Z.of_N 8) with 64. rewrite Zmod_mod. reflexivity. }
(* the world the call hands io_send *)
assert (TWX : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (rx_w Bw now)).
{ rewrite (rx_w_eq Bw now HLB).
  apply (rx_tw_end TMAP_B (aview segs (w_H W) mem2) _ _ rx_P5).
  - apply (rx_tw_step TMAP_B (aview segs (w_H W) mem2) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 18232 8 _ rx_P4 rx_P5 TMAP_B_ok);
      [| exact TMAP_B_g_s | lia | unfold TW.SZ_g_s; cbn; lia | intros x; reflexivity | exact S5].
    apply (rx_tw_step TMAP_B (aview segs (w_H W) mem2) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1752 8 _ rx_P3 rx_P4 TMAP_B_ok);
      [| exact TMAP_B_g_s | lia | unfold TW.SZ_g_s; cbn; lia | intros x; reflexivity | exact S4].
    apply (rx_tw_step TMAP_B (aview segs (w_H W) mem2) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 243 1 _ rx_P2 rx_P3 TMAP_B_ok);
      [| exact TMAP_B_g_s | lia | unfold TW.SZ_g_s; cbn; lia | intros x; reflexivity | exact S3b].
    apply (rx_tw_step TMAP_B (aview segs (w_H W) mem2) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 242 1 _ rx_P1 rx_P2 TMAP_B_ok);
      [| exact TMAP_B_g_s | lia | unfold TW.SZ_g_s; cbn; lia | intros x; reflexivity | exact S2b].
    apply (rx_tw_step TMAP_B (aview segs (w_H W) mem2) _ _ TW.OFF_g_s TB_g_s TW.SZ_g_s 1748 4 _ (fun _ => false) rx_P1
      TMAP_B_ok); [| exact TMAP_B_g_s | lia | unfold TW.SZ_g_s; cbn; lia | intros x; reflexivity | exact S1].
    exact (rx_tw_start _ _ _ _ Htw1).
  - intros x Hx HP. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR1; [lia | exact (rx_P5_out x HP)]. }
(* what the call kept, from its entry to the call of io_send *)
assert (KC1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms) (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (rx_kept_G lyc Sc W memc mdc W mem2 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw) rx_Z1 LAWS HGX
    HARc ltac:(lia)); [| exact HK | exact KR1 | exact GA1].
  intros a Ha. apply slh_inGB. unfold rx_Z1, TW.SZ_g_s in *. lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
(* the registers at `jalr a4` *)
assert (E34' : ew E0 34 = Z_to_bv 64 (TI.ti_io_send timg_B)) by (rewrite E34, <- EIOS, HSEND; reflexivity).
sn_regB HS (Z_to_bv 5 14) (Z_to_bv 64 (TI.ti_io_send timg_B)) T14
  ltac:(cbn [sv_denot]; rewrite E34', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_regB HS (Z_to_bv 5 11) (w64 (TICK_S + 216)) T11 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 12) (w64 (Z.of_nat (length frame))) T12
  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, LENF, ELEN; reflexivity).
sn_regB HS (Z_to_bv 5 25) (w64 (TICK_S + 18144)) T25 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 2) (w64 sp1) T2 ltac:(rx_atom EE 2%nat R2).
sn_regB HS (Z_to_bv 5 3) (w64 (as_gp B)) T3 ltac:(rx_atom EE 3%nat (eq_trans R3 Hgp)).
sn_regB HS (Z_to_bv 5 4) (w64 (as_tp B)) T4 ltac:(rx_atom EE 4%nat (eq_trans R4 Htp)).
sn_regB HS (Z_to_bv 5 8) (w64 (spZ regs)) T8 ltac:(rx_atom EE 8%nat R8).
sn_regB HS (Z_to_bv 5 9) (w64 sp1) T9 ltac:(rx_atom EE 9%nat R9).
sn_regB HS (Z_to_bv 5 18) (w64 F) T18 ltac:(rx_atom EE 18%nat R18).
sn_regB HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) T19 ltac:(rx_atom EE 19%nat R19).
sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) T20 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 21) (w64 (SHADOW_OFF + (TICK_S + 112) / 8)) T21 ltac:(rx_atom EE 21%nat R21).
sn_regB HS (Z_to_bv 5 22) (w64 (SHADOW_OFF + F / 8 + 20)) T22 ltac:(rx_atom EE 22%nat R22).
sn_regB HS (Z_to_bv 5 23) (w64 (TICK_S + 112)) T23 ltac:(rx_atom EE 23%nat R23).
sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 27) (w64 F) T27 ltac:(rx_atom EE 27%nat R27).
(* the facts io_send asks of its frame g_s.inflight_frame *)
assert (CA : TB_g_s = 6157888) by reflexivity.
assert (TSA : trans_sh_any B (TICK_S + 216) (Z.of_nat (length frame))).
{ apply (rx_sh_any_sub (TICK_S + 216) 1514); [| lia | lia].
  exact (trans_sh_any_zshadow B TICK_S (TICK_S + TW.SZ_g_s) (TICK_S + 216) 1514 HTC ltac:(lia)
    ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)). }
assert (RDOK : decode_rd_ok W (ms_mem ms) (TICK_S + 216) (Z.of_nat (length frame))).
{ destruct (TSA lyc S2 W (ms_mem ms) md1 HAR1) as [Ha Hh].
  split; [| split; [exact Ha | split; [exact Hh | split; [unfold amem_range, kLowMemEnd; lia | split; lia]]]].
  intros a Hai. apply (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw). apply slh_inGB. unfold TW.SZ_g_s. lia. }
(* trans_src_ok: DgnTransportBCg.v trans_src_ok_G_range (g_s's payload holds the frame) *)
assert (TSRC : trans_src_ok B lyc S2 W (ms_mem ms) (TICK_S + 216) (Z.of_nat (length frame)))
  by exact (trans_src_ok_G_range B lyc S2 W (ms_mem ms) (TICK_S + 216) (Z.of_nat (length frame)) TB_g_s TW.SZ_g_s
    (TMAP_B_in_G _ _ _ TMAP_B_g_s) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) TSA RDOK).
assert (GARR : garr8 segs (mrestrict (w_H W) (ms_mem ms)) (TICK_S + 216) (map DSpec.bz frame)).
{ exact (tw_garr8 segs (mrestrict (w_H W) (ms_mem ms)) TMAP_B (rx_w Bw now) TW.OFF_g_s TB_g_s TW.SZ_g_s 216
    (Z.to_nat n) TMAP_B_ok TWX TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)). }
assert (GFX : TW.g_fail_next (rx_w Bw now) <= 1).
{ unfold TW.g_fail_next. rewrite rx_w_rd; [exact Hgf | exact HLB | | | |]; unfold TW.OFF_g_fail_next, TW.OFF_g_s;
    cbn [Z.of_nat Pos.of_succ_nat]; lia. }
destruct (rx_w_inv Bw now HLB HRI) as (INV1 & INV4).
assert (ROMX : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite <- (Hrom a Ha). pose proof KC1 as (_ & _ & K3 & _).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia. }
(* +0x424: `jalr a4`, a4 = io_send *)
assert (P4 : 0 <= TI.ti_io_send timg_B < 2 ^ 64) by (rewrite (proj1 io_send_at); lia).
assert (P5 : TI.ti_io_send timg_B mod 2 = 0) by (rewrite (proj1 io_send_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W E0 _ _ _ _ 0x700e7 (1%bv : bv 5) (14%bv : bv 5)
  (TI.ti_io_send timg_B) HEI HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T14 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_send timg_B) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (33312 + 4) = 0x894c4) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (33312 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall rr : bv 5, bv_unsigned rr <> 1 -> YK11.getr regsC rr = YK11.getr (ms_regs ms) rr)
  by (intros rr Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (TICK_S + 216)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (RC12 : YK11.getr regsC 12%bv = w64 (Z.of_nat (length frame)))
  by (rewrite RCK by (vm_compute; discriminate); exact T12).
assert (USPC : spZ regsC = sp1)
  by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; clear - HSPB CEIL HIS; lia).
assert (J1 : @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
  ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms) mdC (k + 0))
  by (apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ1).
assert (RA1 : YK0s.ret_ok (YK11.getr regsC 1)).
{ rewrite RC1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]. }
assert (RA2 : 4096 <= raZ regsC) by (unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia).
assert (SP16 : spZ regsC mod 16 = 0).
{ rewrite USPC. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. destruct Hsp1 as (_ & M1).
  rewrite M1, Z.add_0_r in D1. rewrite D1. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
assert (SPLO : sp0 - STK <= spZ regsC - IOSEND_STK) by (rewrite USPC; clear - Hlo HTS HIS Hsp1; lia).
assert (SPHI : spZ regsC <= sp0) by (rewrite USPC; clear - Hhi Hsp1; lia).
assert (OFFW : decode_off_win regsC IOSEND_STK (TICK_S + 216) (Z.of_nat (length frame)))
  by (unfold decode_off_win; rewrite USPC; left; clear - HSPB CEIL CS LENF Hn0; lia).
assert (IFA : iosend_frame_at (TICK_S + 216) (Z.of_nat (length frame)))
  by (right; unfold TW.SZ_g_s; clear - CS CA LENF Hn0; lia).
assert (EVX : st_nev S + (k + 0) + IOSEND_EV <= EV_MAX) by (unfold TICK_EV, IOSEND_EV in *; clear - Hev; lia).
assert (HP0 : 0 < TICK_S + 216) by (rewrite CS; lia).
eapply SRr_bind.
{ exact (HIO fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms) mdC (k + 0) regsC
    (TICK_S + 216) r0 frame (rx_w Bw now) B1 J1 RA1 RA2 RC3 RC4 RC11 RC12 SP16 SPLO SPHI HP0 GARR TSRC OFFW IFA
    GFX ROMX TWX HIOM INV1 INV4 EVX). }
intros W3 c3 _ HPOST.
unfold transport_io_send_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & R3_10 & Htw3).
assert (He30 : e3 = 0) by (unfold IOSEND_EV in He3; clear - He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _).
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
destruct (dkg_nf_sep segs B LAWS transportb_segs_low lyc Sc S2 W mem2 md2 TICK_CID pos F FL HAR2 Hfrs Hbl EF eq_refl
  FFL) as (N1 & N2 & N3 & N4).
assert (HNF : Z.of_nat (length frame) <= TC.SPEC_MAX_FRAME)
  by (change TC.SPEC_MAX_FRAME with 1514; clear - LENF Hn0; lia).
(* what the call kept, from its entry to io_send's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc lyc S2 W memc W (ms_mem ms) W3 mem3
    (spZ regs - TICK_STK) (spZ regs) (spZ regsC - IOSEND_STK) (spZ regsC) (tick_wr Bw)
    (iosend_wr (Z.of_nat (length frame))) (dkg_nf TICK_CID F FL)).
  - clear - Hlo Hslo Hceil Hstk0. lia.
  - clear - HSPB. lia.
  - intros c p. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - exact N1.
  - exact N3.
  - exact KC1.
  - exact HK3.
  - rewrite USPC. clear - Hsp1 HTS HIS. lia.
  - rewrite USPC. clear - Hsp1. lia.
  - intros a Ha. left. do 16 right. left.
    exact (rx_iosend_wr (Z.of_nat (length frame)) a HNF Ha). }
pose proof HK3 as (K31 & _ & _ & K34 & _).
rewrite USPC in K31.
assert (KSTK3 : forall a, sp1 <= a < 2 ^ 64 -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite K31 by (clear - Ha HSPB CEIL HIS; lia). apply KR1; [clear - Ha HSPB CEIL HIS; lia|].
  unfold rx_Z1. clear - Ha HSPB CEIL HIS CS. lia. }
assert (KFL3 : forall i, 0 <= i < 8 -> aview segs (w_H W3) mem3 (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
{ intros i Hi. rewrite (K34 TICK_CID pos (F + 2040 + i) Hin).
  - pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
    apply KR1; [clear - Hi HF0 HFc CLT; lia|]. unfold rx_Z1. clear - Hi HFG CS. unfold TW.SZ_g_s in *. lia.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048.
    clear - Hi. lia.
  - intros Hw. apply (N2 (F + 2040 + i)); [left; change (fs_frame_bytes TICK_CID) with 2048; clear - Hi; lia|].
    exact (trans_g_img _ (tkb_iosend_G _ _ HNF Hw)). }
assert (T48 : rdword (aview segs (w_H W3) mem3) (sp1 + 48) = Some (TICK_S + 212)).
{ rewrite <- (proj1 Ht01). apply rdword_ext. intros i Hi. apply KSTK3. clear - Hi HSPB CEIL HIS. lia. }
assert (T40 : rdword (aview segs (w_H W3) mem3) (sp1 + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8)).
{ rewrite <- (proj2 Ht01). apply rdword_ext. intros i Hi. apply KSTK3. clear - Hi HSPB CEIL HIS. lia. }
assert (CH : forall nn, acallee_saved nn -> bv_unsigned (Z_to_bv 5 nn) <> 1 ->
  YK11.getr regs3 (Z_to_bv 5 nn) = YK11.getr (ms_regs ms) (Z_to_bv 5 nn))
  by (intros nn Hn H1; rewrite (HP3 nn Hn); exact (RCK _ H1)).
assert (Q9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1)
  by (rewrite (CH 9 ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate)); exact T9).
assert (Q25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 (TICK_S + 18144))
  by (rewrite (CH 25 ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate)); exact T25).
assert (Q24 : YK11.getr regs3 (Z_to_bv 5 24) = w64 SHADOW_OFF)
  by (rewrite (CH 24 ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate)); exact T24).
assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold TCA.TICK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; clear; lia|]). destruct Ho. }
pose proof (TOK.io_send_m_keep _ _ _ _ _ HLX HIOM) as KEEP.
pose proof KEEP as (HLB1 & _).
pose proof (TIF.io_send_m_fail_next _ _ _ _ _ HIOM HLX) as GF1.
rewrite RC1. change (Z_to_bv 64 (BASE + (33312 + 4))) with (Z_to_bv 64 (BASE + RX_RET)).
rename ms into msA.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
(* the callee-saved registers after io_send are those of run 1's end *)
assert (CHT : forall nn v, acallee_saved nn -> bv_unsigned (Z_to_bv 5 nn) <> 1 ->
  YK11.getr (ms_regs msA) (Z_to_bv 5 nn) = v -> YK11.getr regs3 (Z_to_bv 5 nn) = v)
  by (intros nn v Hn H1 Hv; rewrite (CH nn Hn H1); exact Hv).
assert (G1 : TW.g_fail_next B1 <= 1) by (rewrite GF1; clear; lia).
destruct HBR as [(Er0 & HT) | (Er0 & EB1 & Er)].
- (* io_send returned 0: +0x428 `beqz a0` taken, +0x594 .. +0x5bc stats.tx_frames + 1, the tail cut *)
  subst r0.
  pose proof (rx_entry2z ly3 S3 W3 regs3 mem3 md4 B1 sp1 HTC HAR3 Htw3 Q9 ltac:(clear - HSPB CEIL HIS; lia)
    (proj2 Hsp1) T48 T40 R3_10 Q25 Q24) as HS2.
  set (E2 := rx_E2 regs3 B1) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, rx_E2; apply Eimg_env).
  assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = YK11.getr regs3 rr)
    by (intros nn rr Hn; unfold E2, rx_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8))
    by (unfold E2, rx_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (SHOK2 : sh_ok segs RX_Bx (@nil shent) E2 (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_to_tok RUNTO HS2 HJ3 SHOK2 RX_B0 TICK_TAIL.
  { rx_awr. }
  set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TICK_S + 18192 <= a < TICK_S + 18200) ->
    aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TICK_S + 18192 <= x < TICK_S + 18200) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta. sn_winB Hiw Hx ltac:(rewrite CS; clear - Hx; lia). }
  assert (GA2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RT1. cbn [ms_mem restrict] in RT1.
  pose proof (sn_chunk_valB E2 (w_H W3) (ms_mem ms) _ _ _ _ _ _ 6176080 8 (SOff 32 1) RT1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(clear; lia)) as VTF.
  cbn [base_val] in VTF.
  clear HF HFr HG.
  pose proof (TWL.u_at_range B1 (TW.OFF_g_s + 18192) 8) as RTF. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RTF.
  assert (D2 : bv_unsigned (sv_denot E2 (SOff 32 1)) = TS0.u64 (TW.S_stats_tx_frames B1 + 1)).
  { cbn [sv_denot]. rewrite E2_32, Z_to_bv_unsigned, Z_to_bv_unsigned. unfold TS0.u64, TW.S_stats_tx_frames.
    rewrite (bv_wrap_small 64 (TW.u_at B1 (TW.OFF_g_s + 18192) 8)) by exact RTF. reflexivity. }
  rewrite D2 in VTF.
  set (B0 := TW.set_S_stats_tx_frames B1 (TS0.u64 (TW.S_stats_tx_frames B1 + 1))).
  assert (TWF : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms)) B0).
  { unfold B0, TW.set_S_stats_tx_frames. replace TW.A_S_stats_tx_frames with (TW.OFF_g_s + 18192) by reflexivity.
    apply (tw_write TMAP_B (aview segs (w_H W3) mem3) _ B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 18192 8 _ TMAP_B_ok Htw3
      TMAP_B_g_s); [clear; lia | unfold TW.SZ_g_s; cbn; clear; lia | |].
    - intros j Hj. rewrite (rx_le_byte_cong _ (TS0.u64 (TW.S_stats_tx_frames B1 + 1) mod 2 ^ (8 * Z.of_N 8)) 8 j).
      + exact (rx_vm_view _ _ _ 8 _ j VTF Hj).
      + change (8 * Z.of_nat 8) with 64. change (8 * Z.of_N 8) with 64. rewrite Zmod_mod. reflexivity.
    - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KR2; [clear - Hh; lia|]. intros Hc. apply Hn. cbn [Z.of_nat Pos.of_succ_nat]. unfold TICK_S in Hc.
      clear - Hc. lia. }
  assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (rx_kept_G lyc Sc W memc mdc W3 mem3 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)
      (fun x => TICK_S + 18192 <= x < TICK_S + 18200) LAWS HGX HARc ltac:(clear - Hlo Hslo Hceil Hstk0; lia));
      [| exact KC3 | exact KR2 | exact GA2].
    intros a Ha. apply slh_inGB. unfold TW.SZ_g_s. clear - Ha. lia. }
  assert (KSTK : forall a, sp1 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W) mem2 a).
  { intros a Ha. rewrite KR2 by (clear - Ha HSPB CEIL HIS CS; lia). exact (KSTK3 a Ha). }
  assert (KFL : forall i, 0 <= i < 8 ->
    aview segs (w_H W3) (ms_mem ms) (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
  { intros i Hi. pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
    rewrite KR2 by (clear - Hi HF0 HFc CLT HFG CS; unfold TW.SZ_g_s in *; lia). exact (KFL3 i Hi). }
  assert (GRD : TW.S_inflight B0 = TW.S_inflight Bw).
  { unfold B0, TW.S_inflight, TW.set_S_stats_tx_frames, TW.s32_at.
    rewrite rx_rd_put; [| exact HLB1 | clear; rx_off | clear; rx_off | clear; unfold TW.A_S_inflight; rx_off
      | clear; unfold TW.A_S_inflight; rx_off].
    rewrite (TOK.tok_u_at _ _ _ 4 KEEP); [| clear; unfold TW.A_S_inflight, TW.OFF_g_s; lia |].
    - unfold TW.A_S_inflight. rewrite rx_w_rd; [reflexivity | exact HLB | | | |]; clear; unfold TW.OFF_g_s;
        cbn [Z.of_nat Pos.of_succ_nat]; lia.
    - intros j Hj. clear - Hj. unfold TOK.tok_wr, TW.A_S_inflight, TW.OFF_M, TW.SZ_M, TW.OFF_g_cmd, TW.OFF_g_q,
        TW.SZ_g_q, TW.OFF_g_fail_next, TW.OFF_g_last_counter, TW.OFF_g_nq, TW.SZ_g_nq, TW.A_GOT_e2, TW.A_GOT_acks,
        TW.OFF_GOT, TW.A_S_stats_tx_frames, TW.OFF_g_s in *. cbn [Z.of_nat Pos.of_succ_nat] in Hj. lia. }
  pmkst HS2.
  sn_regB HS2 (Z_to_bv 5 5) (w64 (TICK_S + 212)) U5 ltac:(reflexivity).
  sn_regB HS2 (Z_to_bv 5 6) (w64 (SHADOW_OFF + (TICK_S + 212) / 8)) U6 ltac:(reflexivity).
  sn_regB HS2 (Z_to_bv 5 17) (w64 (TICK_S + 18144)) U17 ltac:(reflexivity).
  sn_regB HS2 (Z_to_bv 5 20) (w64 TICK_S) U20
    ltac:(rx_atom EE2 20%nat (CHT 20 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T20)).
  sn_regB HS2 (Z_to_bv 5 24) (w64 SHADOW_OFF) U24 ltac:(reflexivity).
  sn_regB HS2 (Z_to_bv 5 2) (w64 sp1) U2
    ltac:(rx_atom EE2 2%nat (CHT 2 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T2)).
  sn_regB HS2 (Z_to_bv 5 3) (w64 (as_gp B)) U3
    ltac:(rx_atom EE2 3%nat (CHT 3 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T3)).
  sn_regB HS2 (Z_to_bv 5 4) (w64 (as_tp B)) U4
    ltac:(rx_atom EE2 4%nat (CHT 4 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T4)).
  sn_regB HS2 (Z_to_bv 5 8) (w64 (spZ regs)) U8
    ltac:(rx_atom EE2 8%nat (CHT 8 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T8)).
  sn_regB HS2 (Z_to_bv 5 9) (w64 sp1) U9
    ltac:(rx_atom EE2 9%nat (CHT 9 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T9)).
  sn_regB HS2 (Z_to_bv 5 18) (w64 F) U18
    ltac:(rx_atom EE2 18%nat (CHT 18 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T18)).
  sn_regB HS2 (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) U19
    ltac:(rx_atom EE2 19%nat (CHT 19 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T19)).
  sn_regB HS2 (Z_to_bv 5 21) (w64 (SHADOW_OFF + (TICK_S + 112) / 8)) U21
    ltac:(rx_atom EE2 21%nat (CHT 21 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T21)).
  sn_regB HS2 (Z_to_bv 5 22) (w64 (SHADOW_OFF + F / 8 + 20)) U22
    ltac:(rx_atom EE2 22%nat (CHT 22 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T22)).
  sn_regB HS2 (Z_to_bv 5 23) (w64 (TICK_S + 112)) U23
    ltac:(rx_atom EE2 23%nat (CHT 23 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T23)).
  sn_regB HS2 (Z_to_bv 5 27) (w64 F) U27
    ltac:(rx_atom EE2 27%nat (CHT 27 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T27)).
  change (Z_to_bv 64 (BASE + 33724)) with (Z_to_bv 64 (BASE + TICK_TAIL)).
  apply (TAIL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0
    ly3 S3 W3 (ms_mem ms) md5 0 (ms_regs ms) HFIX).
  + refine (conj (conj (conj _ (conj _ (conj Hfrs3 (conj _ (conj ELF3c (conj _ (conj KC4 (conj _ _)))))))) _)
      (conj TWF (conj _ (conj HT _)))).
    * replace (k + 0) with (k + 0 + 0) by (clear; lia). exact HJ3.
    * unfold TICK_EV. clear. lia.
    * rewrite <- Hbl. exact Hperm3.
    * exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. clear - Hob Hi HSPB CEIL HIS. lia.
    * unfold TCA.TICK_FBYTES. change (flag_addr lyc TICK_CID pos) with FL. rewrite <- HFLw.
      replace (F + 2048 - 8) with (F + 2040) by (clear; lia).
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
    * rewrite <- Hnow1. apply rdword_ext. intros i Hi. apply KSTK. clear - Hi HSPB CEIL HIS. lia.
    * unfold B0, TW.g_fail_next, TW.set_S_stats_tx_frames.
      rewrite rx_rd_put; [| exact HLB1 | rx_off | rx_off | unfold TW.OFF_g_fail_next; clear; lia |
        unfold TW.OFF_g_fail_next; rx_off].
      exact G1.
    * intros H0. exfalso. apply Hinf. rewrite <- GRD. exact H0.
  + refine (conj (conj (conj U2 (conj _ (conj _ (conj U8 (conj U9 (conj U18 U27))))))
      (conj U19 (conj U20 (conj U21 (conj U22 (conj U23 U24)))))) (conj U5 (conj U6 U17))).
    * exact (eq_trans U3 (eq_sym Hgp)).
    * exact (eq_trans U4 (eq_sym Htp)).
- (* io_send returned -EIO: +0x428 .. +0x440, s10 = r, the epilogue cut *)
  subst r0. subst Bw'. subst r.
  pose proof (rx_entry2n W3 regs3 mem3 B1 sp1 Q9 ltac:(clear - HSPB CEIL HIS; lia) (proj2 Hsp1) T48 T40 R3_10 Q25 Q24)
    as HS2.
  set (E2 := rx_E2 regs3 B1) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, rx_E2; apply Eimg_env).
  assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = YK11.getr regs3 rr)
    by (intros nn rr Hn; unfold E2, rx_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (SHOK2 : sh_ok segs RX_Bx (@nil shent) E2 (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_to_tok RUNTO HS2 HJ3 SHOK2 RX_B0 TICK_EPI.
  { rx_awr. }
  set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hiw Hx. cbv beta. sn_winB Hiw Hx ltac:(clear - Hx; lia). }
  assert (GA2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (rx_kept_G lyc Sc W memc mdc W3 mem3 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)
      (fun _ => False) LAWS HGX HARc ltac:(clear - Hlo Hslo Hceil Hstk0; lia));
      [intros a [] | exact KC3 | intros a Ha _; exact (KR2 a Ha) | exact GA2]. }
  assert (KSTK : forall a, sp1 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W) mem2 a).
  { intros a Ha. rewrite KR2 by (clear - Ha HSPB CEIL HIS; lia). exact (KSTK3 a Ha). }
  assert (KFL : forall i, 0 <= i < 8 ->
    aview segs (w_H W3) (ms_mem ms) (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
  { intros i Hi. pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
    rewrite KR2 by (clear - Hi HF0 HFc CLT; lia). exact (KFL3 i Hi). }
  pmkst HS2.
  sn_regB HS2 (Z_to_bv 5 26) (w64 (- 5)) U26 ltac:(apply bv_eq; reflexivity).
  sn_regB HS2 (Z_to_bv 5 2) (w64 sp1) U2
    ltac:(rx_atom EE2 2%nat (CHT 2 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T2)).
  sn_regB HS2 (Z_to_bv 5 3) (w64 (as_gp B)) U3
    ltac:(rx_atom EE2 3%nat (CHT 3 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T3)).
  sn_regB HS2 (Z_to_bv 5 4) (w64 (as_tp B)) U4
    ltac:(rx_atom EE2 4%nat (CHT 4 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T4)).
  sn_regB HS2 (Z_to_bv 5 8) (w64 (spZ regs)) U8
    ltac:(rx_atom EE2 8%nat (CHT 8 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T8)).
  sn_regB HS2 (Z_to_bv 5 9) (w64 sp1) U9
    ltac:(rx_atom EE2 9%nat (CHT 9 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T9)).
  sn_regB HS2 (Z_to_bv 5 18) (w64 F) U18
    ltac:(rx_atom EE2 18%nat (CHT 18 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T18)).
  sn_regB HS2 (Z_to_bv 5 27) (w64 F) U27
    ltac:(rx_atom EE2 27%nat (CHT 27 _ ltac:(clear; hnf; lia) ltac:(vm_compute; discriminate) T27)).
  change (Z_to_bv 64 (BASE + 33796)) with (Z_to_bv 64 (BASE + TICK_EPI)).
  apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now (- 5) TF Bw B1 pos sp1 F
    ly3 S3 W3 (ms_mem ms) md5 0 (ms_regs ms) HFIX).
  + refine (conj (conj _ (conj _ (conj Hfrs3 (conj _ (conj ELF3c (conj _ (conj KC4 (conj _ _)))))))) (conj _ G1)).
    * replace (k + 0) with (k + 0 + 0) by (clear; lia). exact HJ3.
    * unfold TICK_EV. clear. lia.
    * rewrite <- Hbl. exact Hperm3.
    * exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. clear - Hob Hi HSPB CEIL HIS. lia.
    * unfold TCA.TICK_FBYTES. change (flag_addr lyc TICK_CID pos) with FL. rewrite <- HFLw.
      replace (F + 2048 - 8) with (F + 2040) by (clear; lia).
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
    * apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact Htw3|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KR2. clear - Hh. lia.
  + split; [|exact U26].
    refine (conj U2 (conj _ (conj _ (conj U8 (conj U9 (conj U18 U27)))))).
    * exact (eq_trans U3 (eq_sym Hgp)).
    * exact (eq_trans U4 (eq_sym Htp)).
Qed.
End rx.

(* The retransmit piece of the walk of diginet_session_tick (TickCutB.v tick_retx_stmt), at every machine, run
   ceiling, record and meter. *)
Theorem tick_retx : forall fx rc B MT, @tick_retx_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@rx_holds fx rc B MT). Qed.

Print Assumptions tick_retx.
