(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths and module names changed; 362 of its 444 lines of code are new or changed and 1128 lines of the source are left out. *)
(* TickBQueue_hd: the first segment of the queue piece of diginet_session_tick's image-B walk (fuzz_transport.asan-ubsan
   0x8909c), tq_hd : tick_epi_at -> tq_body_at -> tick_queue_at (TickCutB.v; TickBQueue_kit.v), code +0x698 .. +0x710,
   +0x604 and +0x7a8 (0x89734 .. 0x897ac, 0x896a0, 0x89844):
     +0x698 .. +0x6ac  the checked 4-byte load of queued (s + 18144, a7), `beqz`: 0 goes to +0x604 (s10 = 0) and on to
                       the epilogue cut (the model returns DIGINET_OK at B0);
     +0x6b0 .. +0x6d0  a4 = s + 208, s5 = its shadow address, the checked load of display_sent, s7 = s + 200, the store
                       of a4 at s1 + 48 (read only on an error path), `beqz`: 0 goes to +0x7a8 (s10 = 1) and on to +0x7ac
                       (tq_body_at with allow = 1);
     +0x6d4 .. +0x710  the checked loads of last_display_us (through s7) and cfg.display_gap_us, now from s1 + 56, s10 =
                       the display test (gap <= now - last, unsigned), `j` to +0x7ac (tq_body_at with allow = tq_allow B0
                       now).
   The run is from a state with three regions: the window words at s1 + 48 (stored) and s1 + 56 (now), the four g_s
   fields it reads and their four shadow bytes (g_s's zero shadow, trans_tick_cells). The only store is the window word
   at s1 + 48: tick_cur is carried by TickBQueue_kit.v tq_cur_step. Image A's template: lib/A/Prog/TickQueue_hd.v.
   rule 24: proves no function (one segment of the walk of diginet_session_tick; the walk is composed at TickCutB.v
   tick_holds_of). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f YK0e.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_tick_cg TickCutB TickBKit TickBQueue_kit TickBQueue_tk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
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
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module YK0e := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK0e.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The state at +0x698: the window (now, atom 32, at s1 + 56; s1 + 48 writable), the g_s fields queued (atom 33),
   display_sent (atom 34, as its 4 unsigned bytes), last_display_us (atom 35), cfg.display_gap_us (atom 36), and the
   four shadow bytes; a7, s4, s8 pinned. *)
Definition TQ_Q_W : YP09.region := YP09.mkRegion (Some 9%nat) 48 64 48 56 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0))].
Definition TQ_Q_G : YP09.region := YP09.mkRegion None (TICK_S + 48) (TICK_S + 18148) 0 0
  [YP09.mkChunk (TICK_S + 48) (YP09.CVal 4 (SOff 36 0)); YP09.mkChunk (TICK_S + 200) (YP09.CVal 8 (SOff 35 0));
   YP09.mkChunk (TICK_S + 208) (YP09.CVal 4 (SOff 34 0)); YP09.mkChunk (TICK_S + 18144) (YP09.CVal 4 (SOff 33 0))].
Definition TQ_Q_SH : YP09.region := YP09.mkRegion None (TQ_SHG + 6) (TQ_SHG + 2269) 0 0
  [YP09.mkChunk (TQ_SHG + 6) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TQ_SHG + 25) (YP09.CVal 1 (SLit 0));
   YP09.mkChunk (TQ_SHG + 26) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TQ_SHG + 2268) (YP09.CVal 1 (SLit 0))].
Definition TQ_Q_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 17) (SLit (TICK_S + 18144))) (Z_to_bv 5 20) (SLit TICK_S))
    (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tq_q : sstate := mkSS TICK_QUEUE TQ_Q_REGS [TQ_Q_W; TQ_Q_G; TQ_Q_SH] None TQ_TK_FACTS.

(* The sign-extended 4-byte load of a 4-byte value. *)
Lemma tq_sext_sw : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The display test the code computes (+0x6fc .. +0x70c: `lwu`, `ld`, `sub`, `sltu`, `xori`). *)
Lemma tq_allow_den : forall E now last gap,
  ew E 32 = Z_to_bv 64 now -> ew E 35 = Z_to_bv 64 last -> ew E 36 = Z_to_bv 64 gap ->
  0 <= now < 2 ^ 64 -> 0 <= last < 2 ^ 64 -> 0 <= gap < 2 ^ 32 ->
  sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 35 0) (SLit (-1))))
    (SExt false 32 (SOff 36 0))) (SLit 1)) = Z_to_bv 64 (DLib.int_of_bool (gap <=? TS0.u64 (now - last))).
Proof.
  intros E now last gap H32 H35 H36 Hn Hl Hg.
  assert (D32 : sv_denot E (SOff 32 0) = Z_to_bv 64 now)
    by (cbn [sv_denot]; rewrite H32, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (D35 : sv_denot E (SOff 35 0) = Z_to_bv 64 last)
    by (cbn [sv_denot]; rewrite H35, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 gap)
    by (cbn [sv_denot]; rewrite H36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  change (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 35 0) (SLit (-1))))
    (SExt false 32 (SOff 36 0))) (SLit 1))) with
    (alu64 ALU_XOR (alu64 ALU_SLTU (alu64 ALU_ADD (sv_denot E (SOff 32 0))
       (mul_div M_MUL (sv_denot E (SOff 35 0)) (Z_to_bv 64 (-1))))
       (zext 64 (bv_extract 0 32 (sv_denot E (SOff 36 0))))) (Z_to_bv 64 1)).
  rewrite D32, D35, D36.
  apply bv_eq.
  rewrite YK0e.AX2S.u_xor64, YK0e.AX2S.u_sltu64, YK0e.AX2S.u_add64, YK0e.AX2S.u_mul64, LMem.zext_small,
    YK0e.AX2S.u_lit64a, LMem.extract_low_mod by lia.
  rewrite !YK0e.AX2S.u_lit64a.
  rewrite (Z.mod_small now), (Z.mod_small last), (Z.mod_small gap) by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change (1 mod 2 ^ 64) with 1.
  change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small gap (2 ^ 32)) by lia.
  rewrite Z.add_mod_idemp_r by lia. repeat rewrite Z.mod_mod by lia.
  replace (now + last * (2 ^ 64 - 1)) with (now - last + last * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. unfold TS0.u64, DLib.int_of_bool.
  rewrite (Z.mod_small gap (2 ^ 64)) by lia.
  destruct (Z.ltb_spec ((now - last) mod 2 ^ 64) gap) as [L | L];
    destruct (Z.leb_spec gap ((now - last) mod 2 ^ 64)) as [L' | L']; try lia; reflexivity.
Qed.

Section hd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition tq_q_E (regs : bvmap 5 word) (now : Z) (B0 : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 now; Z_to_bv 64 (TW.S_queued B0);
    Z_to_bv 64 (TW.u_at B0 TW.A_S_display_sent 4); Z_to_bv 64 (TW.S_last_display_us B0);
    Z_to_bv 64 (TW.S_cfg_display_gap_us B0)]).

Lemma tq_q_entry0 : forall ly S (W : world segs) regs mem md now sp1 B0,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  (forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  tw_at TMAP_B (aview segs (w_H W) mem) B0 ->
  st_ok_pi segs VAL (tq_q_E regs now B0) (mkSS TICK_QUEUE sr_atoms [TQ_Q_W; TQ_Q_G; TQ_Q_SH] None TQ_TK_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_QUEUE)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md now sp1 B0 HSC HAR R9 Hsp Hsp32 Hn HP H56 Htw.
  set (E := tq_q_E regs now B0).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn'; unfold E, tq_q_E; apply ew_Eimg_Ereg_nat; exact Hn').
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 now)
    by (unfold E, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (TW.S_queued B0))
    by (unfold E, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at B0 TW.A_S_display_sent 4))
    by (unfold E, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (TW.S_last_display_us B0))
    by (unfold E, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (TW.S_cfg_display_gap_us B0))
    by (unfold E, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (ZSH : forall j, 0 <= j < 2283 -> val_mem segs (mrestrict (w_H W) mem) (TQ_SHG + j) 1 0).
  { intros j Hj. apply YE2y.val_mem1_of_aview.
    replace (TQ_SHG + j) with (FCells.shadow_addr (TICK_S + 8 * j)).
    - apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold TICK_S, TB_g_s. rewrite Z.add_mod, (Z.mul_comm 8 j), Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, TQ_SHG, TICK_S, TB_g_s.
      replace (6157888 + 8 * j) with ((769736 + j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  assert (GV : forall k (m : nat), 0 <= k -> k + Z.of_nat m <= TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (TB_g_s + k) m (TW.u_at B0 (TW.OFF_g_s + k) m))
    by (intros k m Hk Hm; exact (tw_read_val segs _ TMAP_B B0 _ _ _ k m TMAP_B_ok Htw TMAP_B_g_s Hk Hm)).
  pose proof (TWL.u_at_range B0) as UR.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TQ_Q_W TQ_Q_G TQ_Q_SH base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable segs). apply HP. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ sp1 56 8 (SOff 32 0) now);
          [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | exact Hn | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ H56).
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      pose proof (UR TW.A_S_cfg_display_gap_us 4%nat) as U1. pose proof (UR TW.A_S_last_display_us 8%nat) as U2.
      pose proof (UR TW.A_S_display_sent 4%nat) as U3. pose proof (UR TW.A_S_queued 4%nat) as U4.
      cbn [Z.of_nat Pos.of_succ_nat] in U1, U2, U3, U4.
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 48) 4 (SOff 36 0) (TW.S_cfg_display_gap_us B0));
          [cbn [sv_denot]; rewrite E36, unsigned_lit_small, Z.add_0_r by (unfold TW.S_cfg_display_gap_us; lia);
           reflexivity | unfold TW.S_cfg_display_gap_us; cbn; lia | unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (GV 48 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; cbn; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 200) 8 (SOff 35 0) (TW.S_last_display_us B0));
          [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by (unfold TW.S_last_display_us; lia);
           reflexivity | unfold TW.S_last_display_us; cbn; lia | unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (GV 200 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; cbn; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 208) 4 (SOff 34 0) (TW.u_at B0 TW.A_S_display_sent 4));
          [cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia |
           unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (GV 208 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; cbn; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 18144) 4 (SOff 33 0) (TW.S_queued B0));
          [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by (unfold TW.S_queued; lia); reflexivity |
           unfold TW.S_queued; cbn; lia | unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (GV 18144 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; cbn; lia)).
    + split; [unfold TQ_SHG; lia|]. split; [unfold TQ_SHG; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
        (apply (chunk_ok_val segs E _ 0 _ 1 (SLit 0) 0); [reflexivity | lia | unfold TQ_SHG; lia |]);
        rewrite Z.add_0_l; apply ZSH; lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TQ_Q_W, TQ_Q_G, TQ_Q_SH.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TQ_SHG, TICK_S, TB_g_s. repeat split; first [exact I | lia].
  - unfold TQ_TK_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tq_q_entry : forall ly S (W : world segs) regs mem md now sp1 B0,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  (forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  tw_at TMAP_B (aview segs (w_H W) mem) B0 ->
  YK11.getr regs 17 = w64 (TICK_S + 18144) -> YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (tq_q_E regs now B0) ss_tq_q
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_QUEUE)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md now sp1 B0 HSC HAR R9 Hsp Hsp32 Hn HP H56 Htw R17 R20 R24.
  rewrite restrict_mkst_fx.
  pose proof (tq_q_entry0 ly S W regs mem md now sp1 B0 HSC HAR R9 Hsp Hsp32 Hn HP H56 Htw) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 17) (TICK_S + 18144) H0 R17 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H1 R20 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H2 R24 eq_refl) as H3.
  exact H3.
Qed.
Lemma tq_hd_holds : @tick_epi_at fx rc B MT -> @tq_body_at fx rc B MT -> @tick_queue_at fx rc B MT.
Proof.
unfold tick_queue_at. intros EPI BODY LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF
  Bw Bw' pos sp1 F B0 ly2 S2 W2 mem2 md2 e regs2 HFIX HQC HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HQC as (HRC & Htwq & Hgfq & HINV & Hm).
pose proof HRC as (HC & Hnow56).
pose proof HC as (HJ1 & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24) & R17).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (tq_fix_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX)
  as (Hce0 & Hwin0 & Hspz & H47 & Hsp0a & Hsp1 & Hsp1a & HTS & HSDE & HSDT & HES).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
clear HJi memS.
rewrite tq_queue_eq in Hm.
(* +0x698 .. +0x6ac: queued, `beqz` *)
pose proof (tq_q_entry ly2 S2 W2 regs2 mem2 md2 now sp1 B0 HTC HAR2 R9 ltac:(lia) Hsp1a Hnow
  ltac:(intros a Ha; apply Hpres2; lia) Hnow56 Htwq R17 R20 R24) as HS.
set (E0 := tq_q_E regs2 now B0) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tq_q_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn0; unfold E0, tq_q_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.S_queued B0))
  by (unfold E0, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at B0 TW.A_S_display_sent 4))
  by (unfold E0, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
pose proof (TWL.u_at_range B0 TW.A_S_queued 4) as UQ. pose proof (TWL.u_at_range B0 TW.A_S_display_sent 4) as UD.
cbn [Z.of_nat Pos.of_succ_nat] in UQ, UD.
(* to the queued test *)
paj_run_tok RUN HS HJ1 SHOK TQ_B0.
{ tq_awr_rs. repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?U9 in Ha; left; split; [left; lia | lia] |]). apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
  cbn [In] in Hiw.
  repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; rewrite ?U9 in Hx; lia |]).
  destruct Hiw. }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
Ltac tq_hd_awr U9 := tq_awr_rs; repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?U9 in Ha; left; split; [left; lia | lia] |]); apply awr_ok_x_nil.
Ltac tq_hd_kept HFr U9 sp1 :=
  let Ha := fresh "Ha" in let Hn := fresh "Hn" in let a := fresh "a" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56) HFr); [| exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hiw := fresh "Hiw" in let Hx := fresh "Hx" in
  intros b wlo whi x Hiw Hx; cbv beta;
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end;
  cbn [In] in Hiw;
  repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; rewrite ?U9 in Hx; lia |]);
  destruct Hiw.
assert (QB : forall v, 0 <= v < 2 ^ 32 -> -2^63 <= bv_swrap 32 v < 2^63)
  by (intros v Hv; pose proof (tq_swrap32_range v); lia).
psrr_branch_tok RUN BR HS SHOK TQ_B0.
- (* queued = 0: s10 = 0, to the epilogue cut *)
  cbn [branch_taken] in Hc. rewrite (tq_sext_sw E0 33 _ E33 ltac:(unfold TW.S_queued in *; lia)) in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (tq_br_eqb_s _ 0 (QB (TW.S_queued B0) ltac:(unfold TW.S_queued in *; lia)) ltac:(lia)) in Hc.
  rewrite (tq_swrap32_eq0 (TW.S_queued B0) ltac:(unfold TW.S_queued in *; lia)) in Hc.
  rewrite Hc in Hm. destruct (tick_some_inv _ _ _ _ Hm) as [<- <-].
  paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TICK_EPI.
  { tq_hd_awr U9. }
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) (ms_mem ms1) a) by tq_hd_kept HFr U9 sp1.
  assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG.
  sn_regB HS (Z_to_bv 5 26) (w64 0) Q26 ltac:(reflexivity).
  tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
  tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
  tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
  tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27.
  pmkst HS.
  apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw B0 pos
    sp1 F ly2 S2 W2 (ms_mem ms2) md3 e (ms_regs ms2) HFIX).
  + split; [|split].
    * apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
        (ms_mem ms2) md3 e (fun a => sp1 + 48 <= a < sp1 + 56) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJ1 EF).
      -- intros a Ha. left. lia.
      -- intros a Ha Hn. rewrite (KR2 a Ha Hn). exact (KR1 a Ha Hn).
      -- exact GA2.
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htwq|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      rewrite (KR2 x ltac:(lia) ltac:(lia)). apply KR1; lia.
    * exact Hgfq.
  + exact (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 Q27)))))) Q26).
- (* queued <> 0: display_sent *)
  cbn [branch_taken] in Hc. rewrite (tq_sext_sw E0 33 _ E33 ltac:(unfold TW.S_queued in *; lia)) in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (tq_br_eqb_s _ 0 (QB (TW.S_queued B0) ltac:(unfold TW.S_queued in *; lia)) ltac:(lia)) in Hc.
  rewrite (tq_swrap32_eq0 (TW.S_queued B0) ltac:(unfold TW.S_queued in *; lia)) in Hc.
  rewrite Hc in Hm.
  paj_run_tok RUN HS HJ1 SHOK TQ_B0.
  { tq_hd_awr U9. }
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) (ms_mem ms1) a) by tq_hd_kept HFr U9 sp1.
  assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG.
  assert (E32 : ew E0 32 = Z_to_bv 64 now)
    by (unfold E0, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E35 : ew E0 35 = Z_to_bv 64 (TW.S_last_display_us B0))
    by (unfold E0, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
  assert (E36 : ew E0 36 = Z_to_bv 64 (TW.S_cfg_display_gap_us B0))
    by (unfold E0, tq_q_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
  pose proof (TWL.u_at_range B0 TW.A_S_last_display_us 8) as UL.
  pose proof (TWL.u_at_range B0 TW.A_S_cfg_display_gap_us 4) as UG.
  cbn [Z.of_nat Pos.of_succ_nat] in UL, UG.
  psrr_branch_tok RUN BR HS SHOK TQ_B0.
  + match goal with Hd : branch_taken _ _ _ = true |- _ => rename Hd into Hd0 end.
    cbn [branch_taken] in Hd0. rewrite (tq_sext_sw E0 34 _ E34 ltac:(lia)) in Hd0.
    change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hd0.
    rewrite (tq_br_eqb_s _ 0 (QB (TW.u_at B0 TW.A_S_display_sent 4) ltac:(lia)) ltac:(lia)) in Hd0.
    assert (HA : tq_allow B0 now = 1)
      by (unfold tq_allow, TW.S_display_sent, TW.s32_at; rewrite Hd0; reflexivity).
    rewrite HA in Hm.
    paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TQ_BODY.
    { tq_hd_awr U9. }
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
    assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) ->
      aview segs (w_H W2) (ms_mem ms3) a = aview segs (w_H W2) (ms_mem ms2) a) by tq_hd_kept HFr U9 sp1.
    assert (GA3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    clear HF HFr HG.
    sn_regB HS (Z_to_bv 5 26) (w64 1) Q26 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 21) (w64 (SHADOW_OFF + (TICK_S + 208) / 8)) Q21 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 23) (w64 (TICK_S + 200)) Q23 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) Q20 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Q24 ltac:(reflexivity).
    tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
    tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
    tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
    tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27. tq_kreg HS EE (Z_to_bv 5 19) 19%nat R19 Q19.
    tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22.
    pmkst HS.
    apply (BODY LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0 1
      ly2 S2 W2 (ms_mem ms3) md4 e (ms_regs ms3) HFIX).
    * split.
      -- apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
           (ms_mem ms3) md4 e (fun a => sp1 + 48 <= a < sp1 + 56) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJ1 EF).
         ++ intros a Ha. left. lia.
         ++ intros a Ha Hn. rewrite (KR3 a Ha Hn), (KR2 a Ha Hn). exact (KR1 a Ha Hn).
         ++ exact GA3.
      -- rewrite <- Hnow56. apply rdword_ext. intros i Hi.
         rewrite (KR3 (sp1 + 56 + i) ltac:(lia) ltac:(lia)), (KR2 (sp1 + 56 + i) ltac:(lia) ltac:(lia)). apply KR1; lia.
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htwq|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      rewrite (KR3 x ltac:(lia) ltac:(lia)), (KR2 x ltac:(lia) ltac:(lia)). apply KR1; lia.
    * exact Hgfq.
    * exact HINV.
    * lia.
    * exact Hm.
    * exact (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 Q27)))))) (conj Q19 (conj Q20 (conj Q21
        (conj Q22 (conj Q23 Q24)))))).
    * exact Q26.
  + match goal with Hd : branch_taken _ _ _ = false |- _ => rename Hd into Hd0 end.
    cbn [branch_taken] in Hd0. rewrite (tq_sext_sw E0 34 _ E34 ltac:(lia)) in Hd0.
    change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hd0.
    rewrite (tq_br_eqb_s _ 0 (QB (TW.u_at B0 TW.A_S_display_sent 4) ltac:(lia)) ltac:(lia)) in Hd0.
    paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TQ_BODY.
    { tq_hd_awr U9. }
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
    assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56) ->
      aview segs (w_H W2) (ms_mem ms3) a = aview segs (w_H W2) (ms_mem ms2) a) by tq_hd_kept HFr U9 sp1.
    assert (GA3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    clear HF HFr HG.
    sn_regB HS (Z_to_bv 5 26) (w64 (tq_allow B0 now)) Q26
      ltac:(unfold tq_allow, TW.S_display_sent, TW.s32_at; rewrite Hd0; cbn [orb];
            exact (tq_allow_den E0 now (TW.S_last_display_us B0) (TW.S_cfg_display_gap_us B0) E32 E35 E36 Hnow
                     ltac:(unfold TW.S_last_display_us; lia) ltac:(unfold TW.S_cfg_display_gap_us; lia))).
    sn_regB HS (Z_to_bv 5 21) (w64 (SHADOW_OFF + (TICK_S + 208) / 8)) Q21 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 23) (w64 (TICK_S + 200)) Q23 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) Q20 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Q24 ltac:(reflexivity).
    tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
    tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
    tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
    tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27. tq_kreg HS EE (Z_to_bv 5 19) 19%nat R19 Q19.
    tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22.
    pmkst HS.
    apply (BODY LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0
      (tq_allow B0 now) ly2 S2 W2 (ms_mem ms3) md4 e (ms_regs ms3) HFIX).
    * split.
      -- apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
           (ms_mem ms3) md4 e (fun a => sp1 + 48 <= a < sp1 + 56) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJ1 EF).
         ++ intros a Ha. left. lia.
         ++ intros a Ha Hn. rewrite (KR3 a Ha Hn), (KR2 a Ha Hn). exact (KR1 a Ha Hn).
         ++ exact GA3.
      -- rewrite <- Hnow56. apply rdword_ext. intros i Hi.
         rewrite (KR3 (sp1 + 56 + i) ltac:(lia) ltac:(lia)), (KR2 (sp1 + 56 + i) ltac:(lia) ltac:(lia)). apply KR1; lia.
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htwq|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      rewrite (KR3 x ltac:(lia) ltac:(lia)), (KR2 x ltac:(lia) ltac:(lia)). apply KR1; lia.
    * exact Hgfq.
    * exact HINV.
    * exact (tq_allow_range B0 now).
    * exact Hm.
    * exact (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 Q27)))))) (conj Q19 (conj Q20 (conj Q21
        (conj Q22 (conj Q23 Q24)))))).
    * exact Q26.
Qed.

End hd.
