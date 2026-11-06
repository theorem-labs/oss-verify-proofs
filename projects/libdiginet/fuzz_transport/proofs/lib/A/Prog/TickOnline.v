(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module names and numbers changed; 1218 of its 1352 lines of code are new or changed and 1076 lines of the source are left out. *)
(* TickOnline: Theorem tick_online : tick_online_stmt (lib/A/Prog/TickCut.v), the online piece of the image-A walk
   of diginet_session_tick (fuzz_transport.asan 0x892b8 = transport_sigma TS_diginet_session_tick), from the cut
   tick_online_at (+0x384) to the cuts tick_step_at (+0x3c8) and tick_epi_at (+0x7cc). The runs are the
   position-abstract runs of lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x over the caller's G journal:
     run 0  +0x384 .. +0x3c4  the two instrumented checks of the silence test (the shadow bytes of s + 176 and
                              s + 40 are 0: trans_tick_cells), the 8-byte load of S_last_rx_us, the 4-byte load of
                              S_cfg_offline_ms, now from s1 + 56, now - last_rx and offline * 1000, up to
                              `bgeu a1, a0`;
     +0x3c4                   the branch, taken up from a state with no region: no silence runs one instruction to
                              +0x3c8 and concludes by tick_step_at (the memory is the cut's); silence runs one
                              instruction to +0x558 and takes the lost arm;
     run 1  +0x558 .. +0x5bc  the checked stores of 0 at s + 212 and s + 168, p = frame + 32, the notice's nine
                              shadow bytes := 0, `jal __asan_memset` (p + 16, 0, 56) through TransportGCg.v
                              gx_intrin_at;
     run 2  +0x5c0 .. +0x618  the notice's first 16 bytes, the checked store of 0 at s + 112, the loads of
                              g_s.notify and g_s.notify_ctx and `jalr a2` = notice at TI.ti_notice timg_A;
     run 3  +0x61c .. +0x648  s10 = 0, the nine shadow bytes := 0xf8, to the epilogue cut. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_tick_cg TickCut TransportGNotice SlostNtcKit TickSrcKit TickOnline_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SlostHead SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition TO_B0 : Z * Z := (0, 0).
Definition TO_Bx : sv := SLit 0.

(* run 0, +0x384 .. +0x3c4: the two g_s loads (atoms 32 and 33), now from s1 + 56 (atom 34) and the two shadow
   bytes the checks read. s4 (atom 20) is pinned to s and s8 (atom 24) to the shadow base, so every g_s and
   shadow address of the run is a literal; s1 (atom 9) stays an atom. *)
Definition TO0_R_gs : YP09.region :=
  YP09.mkRegion None (TICK_S + 40) (TICK_S + 184) 0 0
    [YP09.mkChunk (TICK_S + 40) (YP09.CVal 4 (SOff 33 0));
     YP09.mkChunk (TICK_S + 176) (YP09.CVal 8 (SOff 32 0))].
Definition TO0_R_sh : YP09.region :=
  YP09.mkRegion None TO_SH40 (TO_SH176 + 1) 0 0
    [YP09.mkChunk TO_SH40 (YP09.CVal 1 (SLit 0)); YP09.mkChunk TO_SH176 (YP09.CVal 1 (SLit 0))].
Definition TO0_R_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 34 0))].
Definition TO0_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 45) (2 ^ 47) 5); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition TO0_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_to0 : sstate := mkSS TICK_ONLINE TO0_REGS [TO0_R_gs; TO0_R_sh; TO0_R_now] None TO0_FACTS.
(* +0x3c4, the branch, from a state with no region. *)
Definition ss_to_br : sstate := mkSS TO_BR sr_atoms [] None (mkFacts [] [] []).

(* run 1, +0x558 .. +0x5bc: the checked stores of 0 at s + 212 and s + 168 and the notice's nine shadow bytes.
   s3 (atom 19) holds the frame's shadow address, s11 (atom 27) the frame. *)
Definition TO1_R_sh : YP09.region := YP09.mkRegion (Some 19%nat) 4 13 4 13 [].
Definition TO1_R_gsd : YP09.region :=
  YP09.mkRegion None (TICK_S + 168) (TICK_S + 172) (TICK_S + 168) (TICK_S + 172) [].
Definition TO1_R_gsi : YP09.region :=
  YP09.mkRegion None (TICK_S + 212) (TICK_S + 216) (TICK_S + 212) (TICK_S + 216) [].
Definition TO1_R_shg : YP09.region :=
  YP09.mkRegion None TO_SH168 (TO_SH212 + 1) 0 0
    [YP09.mkChunk TO_SH168 (YP09.CVal 1 (SLit 0)); YP09.mkChunk TO_SH212 (YP09.CVal 1 (SLit 0))].
Definition TO1_FACTS : facts :=
  mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (27%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition TO1_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_to1 : sstate := mkSS TO_LOST TO1_REGS [TO1_R_sh; TO1_R_gsd; TO1_R_gsi; TO1_R_shg] None TO1_FACTS.

(* run 2, +0x5c0 .. +0x618: the notice's first 16 bytes at p (atom 21 = s5), the checked store of 0 at s + 112 and
   the loads of g_s.notify and g_s.notify_ctx. *)
Definition TO2_R_p : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 0 16 [].
Definition TO2_R_gs : YP09.region :=
  YP09.mkRegion None (TICK_S + 96) (TICK_S + 116) (TICK_S + 112) (TICK_S + 116)
    [YP09.mkChunk (TICK_S + 96) (YP09.CVal 8 (SOff 32 0));
     YP09.mkChunk (TICK_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition TO2_R_shg : YP09.region :=
  YP09.mkRegion None TO_SH96 (TO_SH96 + 3) 0 0
    [YP09.mkChunk TO_SH96 (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TO_SH96 + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TO_SH96 + 2) (YP09.CVal 1 (SLit 0))].
Definition TO2_FACTS : facts := mkFacts [(21%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition TO2_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 25) (SLit TO_SH112).
Definition ss_to2 : sstate := mkSS TO_AFTER_MS TO2_REGS [TO2_R_p; TO2_R_gs; TO2_R_shg] None TO2_FACTS.
(* run 3, +0x61c .. +0x648: s10 = 0 and the notice's nine shadow bytes := 0xf8 through s3 (atom 19). *)
Definition ss_to3 : sstate := mkSS TO_AFTER_NTC sr_atoms [TO1_R_sh] None
  (mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).
(* The bytes the piece may change between the online cut and the call of notice. *)
Definition to_Z1 (F : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (TICK_S + 168 <= x < TICK_S + 172) \/
  (TICK_S + 212 <= x < TICK_S + 216).
Definition to_Z2 (F sp1 : Z) (x : Z) : Prop :=
  to_Z1 F x \/ (F + 48 <= x < F + 104) \/ (sp1 - ESTACK <= x < sp1).
Definition to_Z (F sp1 : Z) (x : Z) : Prop :=
  to_Z2 F sp1 x \/ (F + 32 <= x < F + 48) \/ (TICK_S + 112 <= x < TICK_S + 116).

Section to. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The value of `sub a1, a2, a1` (now - last_rx, both uint64_t) and of `mul a0, a0, a2` (offline_ms * 1000, the
   model's ms) as the engine leaves them. *)
Lemma to_sub : forall E (eb ec : sv) now x,
  U E eb = now -> U E ec = x -> 0 <= now < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL ec (SLit (-1))) eb) = Z_to_bv 64 (TS0.u64 (now - x)).
Proof.
intros E eb ec now x Hb Hc Hn Hx.
rewrite (denot_lit_U E (SAlu ALU_ADD (SMd M_MUL ec (SLit (-1))) eb)). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, Hb, Hc.
assert (Em1 : zcanon (-1) = 2 ^ 64 - 1) by reflexivity. rewrite Em1.
unfold zcanon, M64, TS0.u64.
rewrite Zplus_mod_idemp_l.
replace (x * (2 ^ 64 - 1) + now) with (now - x + x * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.

Lemma to_mul1000 : forall E (ea : sv) t,
  U E ea = t -> 0 <= t < 2 ^ 32 -> sv_denot E (SMd M_MUL ea (SLit 1000)) = Z_to_bv 64 (TS0.ms_m t).
Proof.
intros E ea t Ha Ht.
rewrite (denot_lit_U E (SMd M_MUL ea (SLit 1000))). f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, Ha.
assert (E1k : zcanon 1000 = 1000) by reflexivity. rewrite E1k.
unfold zcanon, M64, TS0.ms_m, TS0.u64. reflexivity.
Qed.

(* The valuation of run 0: the registers at the cut, then S_last_rx_us, S_cfg_offline_ms and now. *)
Definition to_vals (Bw : list byte) (now : Z) : list word :=
  [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 176) 8); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 40) 4); Z_to_bv 64 now].
Definition to_E0 (regs : bvmap 5 word) (Bw : list byte) (now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs (to_vals Bw now)).

Lemma to_entry0 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 45 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (to_E0 regs Bw now)
    (mkSS TICK_ONLINE sr_atoms [TO0_R_gs; TO0_R_sh; TO0_R_now] None TO0_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_ONLINE)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp1r Hsp1a Hnow Hrd.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := to_E0 regs Bw now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, to_E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (to_vals Bw now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, to_E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth to_vals] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 176) 8) as R32.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 40) 4) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33.
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = TW.u_at Bw (TW.OFF_g_s + 40) 4)
    by (rewrite E33; apply unsigned_lit_small; lia).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T HT0 HT1 HT2. apply (AE2y.val_mem1_of_aview _ _ _ 0).
    exact (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR HT0 HT1 HT2 HTC). }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TO0_R_gs TO0_R_sh TO0_R_now
        base_val]; rewrite ?U9.
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 40) 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 40) 4));
          [apply DEN; [exact E33 | lia] | exact R33 | unfold TICK_S, TA_g_s; lia |].
        replace (0 + (TICK_S + 40)) with (TA_g_s + 40) by (unfold TICK_S; lia).
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 40 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 176) 8 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 176) 8));
          [apply DEN; [exact E32 | exact R32] | exact R32 | unfold TICK_S, TA_g_s; lia |].
        replace (0 + (TICK_S + 176)) with (TA_g_s + 176) by (unfold TICK_S; lia).
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 176 8 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TO_SH40; lia|]. split; [unfold TO_SH176; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 TO_SH40 1 (SLit 0) 0); [reflexivity | lia | unfold TO_SH40; lia |].
        rewrite Z.add_0_l. change TO_SH40 with (FCells.shadow_addr (TICK_S + 40)).
        apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
          | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 TO_SH176 1 (SLit 0) 0); [reflexivity | lia | unfold TO_SH176; lia |].
        rewrite Z.add_0_l. change TO_SH176 with (FCells.shadow_addr (TICK_S + 176)).
        apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
          | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 34 0) now);
        [apply DEN; [exact E34 | exact Hnow] | exact Hnow | lia |].
      exact (AE2y.val_mem_of_rdword (w_H W) mem (sp1 + 56) now Hrd).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TO0_R_gs, TO0_R_sh, TO0_R_now.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TO_SH40, TO_SH176, TICK_S, TA_g_s. repeat split; first [exact I | lia].
  - unfold TO0_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U33.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma to_entry : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 45 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (to_E0 regs Bw now) ss_to0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_ONLINE)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp1r Hsp1a Hnow Hrd R20 R24.
  rewrite restrict_mkst_fx.
  pose proof (to_entry0 ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp1r Hsp1a Hnow Hrd) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

(* The valuation at a state whose registers are atoms. *)
Definition to_Eb (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).
Lemma to_ew_reg : forall (regs : bvmap 5 word) n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (to_Eb regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold to_Eb. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma to_Eb_img : forall regs, img_env VAL A_LIM (to_Eb regs).
Proof. intros regs. unfold to_Eb. apply Eimg_env. Qed.

(* The state at the branch (+0x3c4) with no region. *)
Lemma to_entry_br : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (to_Eb regs) ss_to_br
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_BR)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_to_br, to_Eb.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The state at the first instruction of the lost arm (+0x558). *)
Lemma to_entry1 : forall ly Sx (W : world segs) regs mem md F,
  trans_tick_cells B -> @AR rc segs B ly Sx W mem md ->
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 20 = w64 TICK_S ->
  YK11.getr regs 24 = w64 SHADOW_OFF -> YK11.getr regs 27 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + TICK_FBYTES <= 2 ^ 47 ->
  (F + TICK_FBYTES <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (to_Eb regs) ss_to1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_LOST)) mem (YK11.seg_rom segs))).
Proof.
  intros ly Sx W regs mem md F HTC HAR R19 R20 R24 R27 HF0 HF64 HFc HFG Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold TICK_FBYTES in HFc, HFG.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  rewrite restrict_mkst_fx.
  assert (ZSH : forall T, T mod 8 = 0 -> TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T HT0 HT1 HT2. apply (AE2y.val_mem1_of_aview _ _ _ 0).
    exact (decode_zshadow_rd B ly Sx W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR HT0 HT1 HT2 HTC). }
  assert (H0 : st_ok_pi segs VAL (to_Eb regs)
    (mkSS TO_LOST sr_atoms [TO1_R_sh; TO1_R_gsd; TO1_R_gsi; TO1_R_shg] None TO1_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_LOST)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { assert (U19 : bv_unsigned (ew (to_Eb regs) 19) = SHADOW_OFF + F / 8)
      by (rewrite (to_ew_reg regs 19%nat 19%bv eq_refl), R19; unfold w64;
          apply unsigned_lit_small; unfold SHADOW_OFF; lia).
    assert (U27 : bv_unsigned (ew (to_Eb regs) 27) = F)
      by (rewrite (to_ew_reg regs 27%nat 27%bv eq_refl), R27; unfold w64;
          apply unsigned_lit_small; lia).
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - unfold to_Eb. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TO1_R_sh TO1_R_gsd TO1_R_gsi TO1_R_shg
          base_val]; rewrite ?U19.
      + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
      + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [|constructor].
        intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
               | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [|constructor].
        intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
               | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      + split; [unfold TO_SH168; lia|]. split; [unfold TO_SH212; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val segs (to_Eb regs) _ 0 TO_SH168 1 (SLit 0) 0);
            [reflexivity | lia | unfold TO_SH168; lia |].
          rewrite Z.add_0_l. change TO_SH168 with (FCells.shadow_addr (TICK_S + 168)).
          apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
            | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
        * apply (chunk_ok_val segs (to_Eb regs) _ 0 TO_SH212 1 (SLit 0) 0);
            [reflexivity | lia | unfold TO_SH212; lia |].
          rewrite Z.add_0_l. change TO_SH212 with (FCells.shadow_addr (TICK_S + 208)).
          apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
            | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, TO1_R_sh, TO1_R_gsd, TO1_R_gsi, TO1_R_shg.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold TO_SH168, TO_SH212, SHADOW_OFF, TICK_S, TA_g_s, TW.SZ_g_s in *. rewrite HF8.
      repeat split; first [exact I | lia].
    - unfold TO1_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U27.
      change (2 ^ 3) with 8. change (2 ^ 6) with 64.
      assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
      { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
        apply Z.mod_mul. lia. }
      unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

(* The state after notice returns (+0x61c): the registers as atoms, the notice's shadow bytes 4 .. 12. *)
Lemma to_entry3 : forall (W : world segs) regs mem F,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + TICK_FBYTES <= 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (to_Eb regs) ss_to3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_AFTER_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R19 HF0 HF64 HFc Hpsh. unfold TICK_FBYTES in HFc.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (U19 : bv_unsigned (ew (to_Eb regs) 19) = SHADOW_OFF + F / 8)
    by (rewrite (to_ew_reg regs 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_to3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - unfold to_Eb. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TO1_R_sh base_val]. rewrite U19.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The valuation of run 2: the registers after the memset, then g_s.notify and g_s.notify_ctx at the world the
   two stores of the lost arm made. *)
Definition to_vals2 (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 96) 8);
   Z_to_bv 64 (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 104) 8)].

(* A region cell of n bytes holding 0, read byte by byte through the view. *)
Lemma to_aview0 : forall H (m : word -> option byte) a (n : nat),
  val_mem segs (mrestrict H m) a n 0 -> forall j, 0 <= j < Z.of_nat n -> aview segs H m (a + j) = Some 0.
Proof.
intros H m a n HV j Hj. pose proof (HV (Z.to_nat j) ltac:(lia)) as H0.
rewrite Z2Nat.id in H0 by lia. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
lazymatch goal with |- context [?f 0 n (Z.to_nat j)] => unfold f end.
rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.

(* The state after the memset (+0x5c0). *)
Lemma to_entry2 : forall ly Sx (W : world segs) regs mem md Bw F,
  trans_tick_cells B -> @AR rc segs B ly Sx W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) (slost_w1 Bw) ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 25 = w64 TO_SH112 -> YK11.getr regs 21 = w64 (F + 32) ->
  4096 <= F -> F mod 64 = 0 -> F + TICK_FBYTES <= 2 ^ 47 -> in_app F TICK_FBYTES ->
  (F + TICK_FBYTES <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs (to_vals2 Bw))) ss_to2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_AFTER_MS)) mem (YK11.seg_rom segs))).
Proof.
  intros ly Sx W regs mem md Bw F HTC HAR Htw R20 R24 R25 R21 HF0 HF64 HFc HFapp HFG Hpf.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold TICK_FBYTES in HFc, HFapp, HFG.
  rewrite restrict_mkst_fx.
  set (E := Eimg (PI := PI_transport) (Ereg regs (to_vals2 Bw))).
  assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs rr)
    by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (to_vals2 Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth to_vals2] in E32, E33.
  pose proof (TWL.u_at_range (slost_w1 Bw) (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range (slost_w1 Bw) (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (U21 : bv_unsigned (ew E 21) = F + 32)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T HT0 HT1 HT2. apply (AE2y.val_mem1_of_aview _ _ _ 0).
    exact (decode_zshadow_rd B ly Sx W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR HT0 HT1 HT2 HTC). }
  assert (H0 : st_ok_pi segs VAL E (mkSS TO_AFTER_MS sr_atoms [TO2_R_p; TO2_R_gs; TO2_R_shg] None TO2_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TO_AFTER_MS)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - unfold E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TO2_R_p TO2_R_gs TO2_R_shg
          base_val]; rewrite ?U21.
      + split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
      + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split.
        * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
          unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
          split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
                 | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
        * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
          -- apply (chunk_ok_val segs E _ 0 (TICK_S + 96) 8 (SOff 32 0)
               (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 96) 8));
               [apply DEN; [exact E32 | exact R32] | exact R32 | unfold TICK_S, TA_g_s; lia |].
             replace (0 + (TICK_S + 96)) with (TA_g_s + 96) by (unfold TICK_S; lia).
             exact (tw_read_val segs _ TMAP_A (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw
               TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
          -- apply (chunk_ok_val segs E _ 0 (TICK_S + 104) 8 (SOff 33 0)
               (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 104) 8));
               [apply DEN; [exact E33 | exact R33] | exact R33 | unfold TICK_S, TA_g_s; lia |].
             replace (0 + (TICK_S + 104)) with (TA_g_s + 104) by (unfold TICK_S; lia).
             exact (tw_read_val segs _ TMAP_A (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw
               TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      + split; [unfold TO_SH96; lia|]. split; [unfold TO_SH96; lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val segs E _ 0 TO_SH96 1 (SLit 0) 0); [reflexivity | lia | unfold TO_SH96; lia |].
          rewrite Z.add_0_l. change TO_SH96 with (FCells.shadow_addr (TICK_S + 96)).
          apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
            | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
        * apply (chunk_ok_val segs E _ 0 (TO_SH96 + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold TO_SH96; lia |].
          rewrite Z.add_0_l. change (TO_SH96 + 1) with (FCells.shadow_addr (TICK_S + 104)).
          apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
            | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
        * apply (chunk_ok_val segs E _ 0 (TO_SH96 + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold TO_SH96; lia |].
          rewrite Z.add_0_l. change (TO_SH96 + 2) with (FCells.shadow_addr (TICK_S + 112)).
          apply ZSH; [unfold TICK_S, TA_g_s; reflexivity | unfold TICK_S, TA_g_s; lia
            | unfold TICK_S, TA_g_s, TW.SZ_g_s; lia].
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, TO2_R_p, TO2_R_gs, TO2_R_shg.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U21.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, TO_SH96, SHADOW_OFF, TICK_S, TA_g_s,
        TW.SZ_g_s in *.
      repeat split; first [exact I | lia].
    - unfold TO2_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21.
      change (2 ^ 5) with 32.
      assert (M32 : (F + 32) mod 32 = 0).
      { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
        replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) TO_SH112 H2 R25 eq_refl) as H3.
  exact H3.
Qed.
(* The facts the cuts before the first program callee carry, moved to a later memory whose view is the same at
   every address. *)
Lemma to_pre_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k regs now Bw pos sp1 F S2
    mem2 md2 mem3 md3,
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  (forall a, aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3
  (((HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) & Hn56) & Hbl & HGK & Htw) HJ3 KD GR.
split; [split|].
- split; [exact HJ3|]. split; [exact He|]. split; [exact Hfr|]. split; [exact Hperm|].
  split; [exact HlyF|]. split; [exact HMO|]. split.
  + destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
    split; [intros a Ha Hw; rewrite KD; exact (K1 a Ha Hw)|].
    split; [intros b m i Hb Hi Hn; rewrite KD; exact (K2 b m i Hb Hi Hn)|].
    split; [intros a Hi HnG Hno Hne; rewrite KD; exact (K3 a Hi HnG Hno Hne)|].
    split; [intros cid pos0 a Hin Hr Hn; rewrite KD; exact (K4 cid pos0 a Hin Hr Hn)|].
    split; [intros a Ha Hw Hp; apply GR; exact (K5 a Ha Hw Hp)|].
    intros a Ha; apply GR; exact (K6 a Ha).
  + split.
    * refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
    * rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Hn56.
- split; [exact Hbl|]. split.
  + intros a Hg. rewrite KD. exact (HGK a Hg).
  + apply (tw_kept TMAP_A (aview segs (w_H W) mem2)); [exact Htw | intros x _; exact (KD x)].
Qed.


(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac to_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "to_reg: no match for" T; fail
  end.

(* The awr obligation's regions, computed. *)
Ltac to_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A state whose regions have an empty write window writes nothing. *)
Ltac to_nowr :=
  let x := fresh "x" in let Hx := fresh "Hx" in let rr := fresh "rr" in
  let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros x Hx; unfold in_wrange; intros (rr & Hr & Hb); vm_compute in Hr;
  repeat (destruct Hr as [Hr | Hr];
    [rewrite <- Hr in Hb; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]);
  destruct Hr.
(* After a run that writes nothing: every byte of the view as before (KD), presence grown (GR). *)
Ltac to_after HS W KD GR m0 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m0 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m0 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m0 (ms_mem msF) 0 HFx ltac:(lia) ltac:(to_nowr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m0 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac to_kreg HS EWL rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    to_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EWL rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

Lemma to_holds : @tick_online_stmt fx rc B MT.
Proof.
unfold tick_online_stmt. intros STEP EPI. unfold tick_online_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof CALLEES as (HSF8 & HMS & HN & HIO & HSFR & HS00 & HSD & HTK).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTFe &
  Hrom & Hapart & Hrinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnow56) & Hbl & HGK & Htw1)
  & Hst).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R22 & R23 & R24 & R25) & R21).
assert (R2' : YK11.getr regs2 (Z_to_bv 5 2) = w64 sp1) by exact R2.
assert (R3' : YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs 3) by exact R3.
assert (R4' : YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs 4) by exact R4.
assert (R8' : YK11.getr regs2 (Z_to_bv 5 8) = w64 (spZ regs)) by exact R8.
assert (R9' : YK11.getr regs2 (Z_to_bv 5 9) = w64 sp1) by exact R9.
assert (R18' : YK11.getr regs2 (Z_to_bv 5 18) = w64 F) by exact R18.
assert (R19' : YK11.getr regs2 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8)) by exact R19.
assert (R21' : YK11.getr regs2 (Z_to_bv 5 21) = w64 (TW.S_state Bw)) by exact R21.
assert (R22' : YK11.getr regs2 (Z_to_bv 5 22) = w64 (SHADOW_OFF + F / 8 + 48)) by exact R22.
assert (R23' : YK11.getr regs2 (Z_to_bv 5 23) = w64 (TICK_S + 112)) by exact R23.
assert (R25' : YK11.getr regs2 (Z_to_bv 5 25) = w64 (SHADOW_OFF + (TICK_S + 112) / 8)) by exact R25.
assert (R27' : YK11.getr regs2 (Z_to_bv 5 27) = w64 F) by exact R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HTS : TICK_STK = 208 + Z.max ESTACK (Z.max NOTICE_STK (Z.max IOSEND_STK (Z.max SENDDATA_STK TAKE_STK))))
  by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (rr := (spZ regs - 192) mod 32) in *.
  set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the window's linear facts; HTS's nested Z.max would make every later lia split 16 ways *)
assert (BAC : alloc_ceiling <= spZ regs - TICK_STK) by (unfold TICK_STK, TICK_FRAME, TICK_ALIGN in *; lia).
assert (BTS : 208 + ESTACK <= TICK_STK /\ 208 + NOTICE_STK <= TICK_STK) by (rewrite HTS; lia).
clear HTS.
(* run 0, +0x384 .. +0x3c4 *)
pose proof (to_entry lyc S2 W regs2 mem2 md2 Bw now sp1 HTC HAR2 Htw1 R9 ltac:(lia) (proj2 Hsp1) Hnow Hnow56
  R20 R24) as HS.
set (E0 := to_E0 regs2 Bw now) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, to_E0; apply Eimg_env).
assert (SHOK : sh_ok segs TO_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ1 SHOK TO_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
(* the facts of the cut at the memory run 0 leaves (it writes nothing) *)
to_after HS W KD0 GR0 mem2 ms0. clear HF HFr HG.
(* the two operands of `bgeu a1, a0` *)
assert (ELR : TW.u_at Bw (TW.OFF_g_s + 176) 8 = TW.S_last_rx_us Bw) by reflexivity.
assert (EOF : TW.u_at Bw (TW.OFF_g_s + 40) 4 = TW.S_cfg_offline_ms Bw) by reflexivity.
assert (EE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0, to_E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX0 : forall j, (j < 3)%nat -> ew E0 (32 + j) = nth j (to_vals Bw now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, to_E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX0 0%nat ltac:(lia)) as E32. pose proof (EX0 1%nat ltac:(lia)) as E33.
pose proof (EX0 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth to_vals] in E32, E33, E34.
rewrite ELR in E32. rewrite EOF in E33.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 176) 8) as R32. rewrite ELR in R32.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 40) 4) as R33. rewrite EOF in R33.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33.
assert (Rv1 : 0 <= TS0.u64 (now - TW.S_last_rx_us Bw) < 2 ^ 64)
  by (unfold TS0.u64; apply Z.mod_pos_bound; lia).
assert (Rv0 : 0 <= TS0.ms_m (TW.S_cfg_offline_ms Bw) < 2 ^ 64)
  by (unfold TS0.ms_m, TS0.u64; apply Z.mod_pos_bound; lia).
to_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (TS0.u64 (now - TW.S_last_rx_us Bw))) Q11
  ltac:(exact (to_sub E0 (SOff 34 0) (SOff 32 0) now (TW.S_last_rx_us Bw)
                 (U_atom E0 34%nat now E34 Hnow) (U_atom E0 32%nat _ E32 R32) Hnow R32)).
to_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TS0.ms_m (TW.S_cfg_offline_ms Bw))) Q10
  ltac:(exact (to_mul1000 E0 (SOff 33 0) (TW.S_cfg_offline_ms Bw)
                 (U_atom E0 33%nat _ E33 ltac:(lia)) R33)).
(* the registers run 0 keeps *)
to_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) T2
  ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) T3
  ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) T4
  ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) T19
  ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 21) (YK11.getr regs2 (Z_to_bv 5 21)) T21
  ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 22) (YK11.getr regs2 (Z_to_bv 5 22)) T22
  ltac:(cbn [sv_denot]; rewrite (EE0 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23
  ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) T25
  ltac:(cbn [sv_denot]; rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 27) (YK11.getr regs2 (Z_to_bv 5 27)) T27
  ltac:(cbn [sv_denot]; rewrite (EE0 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
to_reg HS (Z_to_bv 5 20) (w64 TICK_S) T20 ltac:(reflexivity).
to_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
(* +0x3c4: the branch, from a state with no region *)
pmkst HS.
clear HS SHOK HEI.
pose proof (to_entry_br W (ms_regs ms0) (ms_mem ms0)) as HS.
assert (HEI : img_env VAL A_LIM (to_Eb (ms_regs ms0))) by apply to_Eb_img.
assert (SHOK : sh_ok segs TO_Bx (@nil shent) (to_Eb (ms_regs ms0)) (mrestrict (w_H W) (ms_mem ms0)))
  by constructor.
assert (D11 : ew (to_Eb (ms_regs ms0)) 11%nat = Z_to_bv 64 (TS0.u64 (now - TW.S_last_rx_us Bw)))
  by (rewrite (to_ew_reg (ms_regs ms0) 11%nat (Z_to_bv 5 11) eq_refl); exact Q11).
assert (D10 : ew (to_Eb (ms_regs ms0)) 10%nat = Z_to_bv 64 (TS0.ms_m (TW.S_cfg_offline_ms Bw)))
  by (rewrite (to_ew_reg (ms_regs ms0) 10%nat (Z_to_bv 5 10) eq_refl); exact Q10).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TO_BR)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK TO_B0.
- (* silence: the lost arm *)
  rewrite branch_geu_U, (U_atom _ 11%nat _ D11 Rv1), (U_atom _ 10%nat _ D10 Rv0) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (HTO : (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)) = true)
    by (apply Z.leb_le; lia).
  destruct (to_model_lost TF Bw now Bw' r Hst HTO Hm) as [HLM Hr0].
  (* the frame is apart from g_s: a frame byte is not an image byte *)
  assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh.
  change (fs_frame_bytes TICK_CID) with 2048 in HFb.
  change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
  change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (HFG : F + TICK_FBYTES <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
  { unfold TICK_FBYTES.
    destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
    exfalso.
    assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
    { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F];
      unfold TW.SZ_g_s in *; lia. }
    destruct Hx as (x & Hx1 & Hx2).
    apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
      [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
    apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TICK_S in *; cbn [fst snd]; lia]. }
  (* one instruction to +0x558 *)
  paj_run_to_tok RUNTO HS HJ1 SHOK TO_B0 TO_LOST.
  { to_awr_rs. apply awr_ok_x_nil. }
  to_after HS W KD1 GR1 (ms_mem ms0) ms1. clear HF HFr HG.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 2) 2%nat T2 Y2.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 3) 3%nat T3 Y3.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 4) 4%nat T4 Y4.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 8) 8%nat T8 Y8.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 9) 9%nat T9 Y9.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 18) 18%nat T18 Y18.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 19) 19%nat T19 Y19.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 20) 20%nat T20 Y20.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 24) 24%nat T24 Y24.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 25) 25%nat T25 Y25.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 27) 27%nat T27 Y27.
  assert (KDL : forall a, aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem2 a)
    by (intros a; rewrite (KD1 a); exact (KD0 a)).
  assert (GRL : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms1) a)
    by (intros a Ha; exact (GR1 a (GR0 a Ha))).
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARL.
  pmkst HS. clear HS SHOK HEI.
  pose proof (to_entry1 lyc S2 W (ms_regs ms1) (ms_mem ms1) md3 F HTC HARL
    ltac:(exact (eq_trans Y19 R19')) ltac:(exact Y20)
    ltac:(exact Y24) ltac:(exact (eq_trans Y27 R27'))
    HF0 HF64 ltac:(unfold TICK_FBYTES in *; lia) HFG
    ltac:(intros i Hi; apply GRL; exact (proj1 (HFsh i ltac:(lia))))) as HS.
  assert (HEI : img_env VAL A_LIM (to_Eb (ms_regs ms1))) by apply to_Eb_img.
  assert (SHOK : sh_ok segs TO_Bx (@nil shent) (to_Eb (ms_regs ms1)) (mrestrict (w_H W) (ms_mem ms1)))
    by constructor.
  assert (HF8b : 0 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; unfold TICK_FBYTES in *; lia]).
  assert (Y19b : YK11.getr (ms_regs ms1) 19%bv = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans Y19 R19').
  assert (Y27b : YK11.getr (ms_regs ms1) 27%bv = w64 F) by exact (eq_trans Y27 R27').
  assert (U19b : bv_unsigned (ew (to_Eb (ms_regs ms1)) 19) = SHADOW_OFF + F / 8)
    by (rewrite (to_ew_reg (ms_regs ms1) 19%nat 19%bv eq_refl), Y19b; unfold w64;
        apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U27b : bv_unsigned (ew (to_Eb (ms_regs ms1)) 27) = F)
    by (rewrite (to_ew_reg (ms_regs ms1) 27%nat 27%bv eq_refl), Y27b; unfold w64;
        apply unsigned_lit_small; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TO_LOST)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ1 SHOK TO_B0.
  { to_awr_rs.
    eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19b in Ha.
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF.
      change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    - apply awr_ok_x_cons_g.
      + intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
               | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      + apply awr_ok_x_cons_g.
        * intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
          unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
          split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
                 | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
        * apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
          apply awr_ok_x_nil. }
  (* the nine shadow bytes the run stored 0 *)
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi. rewrite <- U19b.
    assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    apply (SlostNtc.sn_chunk0 (to_Eb (ms_regs ms1)) (w_H W) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
    cbn [In]; repeat (first [left; reflexivity | right]). }
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
  destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms) _ TICK_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
  rewrite <- EF in HFb1, HFsh1.
  change (fs_frame_bytes TICK_CID) with 2048 in HFb1.
  change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh1.
  change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh1.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  pmkst HS.
  to_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) M10 ltac:(cbn [sv_denot]; rewrite U27b; reflexivity).
  to_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) M11 ltac:(reflexivity).
  to_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) M12 ltac:(reflexivity).
  to_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y2 R2')).
  to_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 34324)) MRA ltac:(apply codeptr_val; exact HEI).
  to_reg HS (3%bv : bv 5) (w64 (as_gp B)) M3
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y3 (eq_trans R3' Hgp))).
  to_reg HS (4%bv : bv 5) (w64 (as_tp B)) M4
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y4 (eq_trans R4' Htp))).
  assert (MSP : spZ (ms_regs ms) = sp1)
    by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
        apply unsigned_lit_small; lia).
  (* +0x5bc: __asan_memset (p + 16, 0, 56), through the G call kit *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet
      (transport_sigma TS___asan_memset) (HMS fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0
      md0 ((TICK_CID, pos) :: own) lyc S2 _ (k + 0) (F + 48) 0 56 (sp1 - sp0)
      (Z_to_bv 64 (BASE + 34324)) HGX G_HARNESS_rw HJ1 M10 M11 M12).
    - lia.
    - lia.
    - lia.
    - rewrite MSP. lia.
    - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
      destruct Hsp1 as (_ & Msp32). rewrite Msp32, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
      rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
      apply Z.mod_mul. lia.
    - lia.
    - lia.
    - exact M3.
    - exact M4.
    - exact MRA.
    - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite MSP. split.
      + unfold awr_byte. right; right; right. unfold in_frames. exists TICK_CID, pos.
        split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
      + unfold TICK_FBYTES, TICK_FRAME, TICK_ALIGN in *. lia.
    - apply (amem_range_sub_app F 2048); [exact HFapp | unfold TICK_FBYTES in *; lia | lia | lia | lia].
    - apply (frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
      intros i Hi. exact (ZS1 i ltac:(lia)).
    - intros _. apply (frame_hull_vis _ F 2048 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
  assert (HeffM' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 104) -> ~ (sp1 - ESTACK <= a < sp1) ->
    aview segs (w_H W) memM a = aview segs (w_H W) (ms_mem ms) a).
  { intros a Ha Hd1 Hd2. apply HeffM; [exact Ha | intros Hx; apply Hd1; lia |].
    replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hd2. }
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ to_Z1 F a ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (to_Z1 F) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
    cbn [In] in Hiw.
    repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx;
      rewrite ?U19b in Hx; unfold to_Z1, TICK_S, TA_g_s; first [left; lia | right; lia | lia] |]).
    destruct Hiw. }
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ to_Z2 F sp1 a ->
    aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
  { intros a Ha Hn.
    rewrite (HeffM' a Ha ltac:(intros Hd; apply Hn; right; left; exact Hd)
      ltac:(intros Hd; apply Hn; right; right; exact Hd)).
    rewrite (KR1 a Ha ltac:(intros Hz; apply Hn; left; exact Hz)).
    exact (KDL a). }
  assert (GA2 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memM a)
    by (intros a Ha; exact (HgrM a (apresent_grows _ _ _ a HG (GRL a Ha)))).
  clear HF HFr HG.
  destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 TICK_CID pos F
    (flag_addr lyc TICK_CID pos) HAR2 Hfrs Hbl EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  assert (NZG2 : forall x, inG TG.G_HARNESS x -> ~ (TICK_S + 212 <= x < TICK_S + 216) ->
    ~ (TICK_S + 168 <= x < TICK_S + 172) -> ~ to_Z2 F sp1 x).
  { intros x Hx Hn1 Hn2 Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl.
    unfold kLowMemEnd in Hl.
    destruct Hz as [[Hz | [Hz | Hz]] | [Hz | Hz]].
    - unfold SHADOW_OFF in Hz. lia.
    - exact (Hn2 Hz).
    - exact (Hn1 Hz).
    - apply (N2 x); [left; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img x Hx)].
    - lia. }
  (* the two stores of 0 the lost arm made *)
  pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
  pose proof (SlostNtc.sn_chunk_val (to_Eb (ms_regs ms1)) (w_H W) (ms_mem ms) None _ _ _ _ _ (TICK_S + 212) 4 (SLit 0)
    RG2 ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VI.
  pose proof (SlostNtc.sn_chunk_val (to_Eb (ms_regs ms1)) (w_H W) (ms_mem ms) None _ _ _ _ _ (TICK_S + 168) 4 (SLit 0)
    RG1 ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VD.
  cbn [base_val] in VI, VD. rewrite !Z.add_0_l in VI, VD.
  change (N.to_nat 4) with 4%nat in VI, VD.
  change (bv_unsigned (sv_denot (to_Eb (ms_regs ms1)) (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VI, VD.
  assert (ZI1 : forall j, 0 <= j < 4 -> aview segs (w_H W) memM (TICK_S + 212 + j) = Some 0).
  { intros j Hj.
    rewrite (HeffM' (TICK_S + 212 + j) ltac:(unfold TICK_S, TA_g_s; lia)
      ltac:(unfold TICK_S, TA_g_s, TW.SZ_g_s, TICK_FBYTES in *; lia) ltac:(unfold TICK_S, TA_g_s in *; lia)).
    exact (to_aview0 (w_H W) (ms_mem ms) (TICK_S + 212) 4 VI j ltac:(cbn; lia)). }
  assert (ZD1 : forall j, 0 <= j < 4 -> aview segs (w_H W) memM (TICK_S + 168 + j) = Some 0).
  { intros j Hj.
    rewrite (HeffM' (TICK_S + 168 + j) ltac:(unfold TICK_S, TA_g_s; lia)
      ltac:(unfold TICK_S, TA_g_s, TW.SZ_g_s, TICK_FBYTES in *; lia) ltac:(unfold TICK_S, TA_g_s in *; lia)).
    exact (to_aview0 (w_H W) (ms_mem ms) (TICK_S + 168) 4 VD j ltac:(cbn; lia)). }
  assert (TW2 : tw_at TMAP_A (aview segs (w_H W) memM) (slost_w1 Bw)).
  { apply (SlostHead.slh_tw_w1 (aview segs (w_H W) mem2) (aview segs (w_H W) memM) Bw Htw1 ZI1 ZD1).
    intros x Hx Hn1 Hn2.
    assert (HxG : inG TG.G_HARNESS x).
    { destruct Hx as (o & b & n & Hin3 & Hxr). unfold inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transport_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
    apply KA2; [lia|]. apply NZG2; [exact HxG | exact Hn1 | exact Hn2]. }
  (* the registers the memset keeps *)
  to_reg HS (Z_to_bv 5 21) (w64 (F + 32)) P21 ltac:(cbn [sv_denot]; rewrite U27b; reflexivity).
  to_reg HS (Z_to_bv 5 20) (w64 TICK_S) P20 ltac:(reflexivity).
  to_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) P24 ltac:(reflexivity).
  to_reg HS (Z_to_bv 5 25) (w64 TO_SH112) P25
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 25%nat 25%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact (eq_trans Y25 R25')).
  to_reg HS (Z_to_bv 5 2) (w64 sp1) P2
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y2 R2')).
  to_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) P3
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y3 (eq_trans R3' Hgp))).
  to_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) P4
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y4 (eq_trans R4' Htp))).
  to_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) P8
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact Y8).
  to_reg HS (Z_to_bv 5 9) (w64 sp1) P9
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y9 R9')).
  to_reg HS (Z_to_bv 5 18) (w64 F) P18
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y18 R18')).
  to_reg HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) P19
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y19 R19')).
  to_reg HS (Z_to_bv 5 27) (w64 F) P27
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg (ms_regs ms1) 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans Y27 R27')).
  (* run 2, +0x5c0 .. +0x618 *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARM.
  clear HS SHOK HEI.
  pose proof (to_entry2 lyc S2 W regsM memM _ Bw F HTC HARM TW2
    ltac:(exact (eq_trans (HPM 20 ltac:(hnf; lia)) P20))
    ltac:(exact (eq_trans (HPM 24 ltac:(hnf; lia)) P24))
    ltac:(exact (eq_trans (HPM 25 ltac:(hnf; lia)) P25))
    ltac:(exact (eq_trans (HPM 21 ltac:(hnf; lia)) P21))
    HF0 HF64 ltac:(unfold TICK_FBYTES in *; lia) HFapp HFG
    ltac:(intros a Ha; apply GA2; exact (proj1 (HFb a ltac:(lia))))) as HS.
  set (E2 := Eimg (PI := PI_transport) (Ereg regsM (to_vals2 Bw))) in HS.
  assert (HEI : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
  assert (SHOK : sh_ok segs TO_Bx (@nil shent) E2 (mrestrict (w_H W) memM)) by constructor.
  assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E2 n = YK11.getr regsM rr)
    by (intros n rr Hn; unfold E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (Q21b : YK11.getr regsM 21%bv = w64 (F + 32))
    by exact (eq_trans (HPM 21 ltac:(hnf; lia)) P21).
  assert (U21M : bv_unsigned (ew E2 21) = F + 32)
    by (rewrite (EE2 21%nat 21%bv eq_refl), Q21b; unfold w64; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TO_AFTER_MS)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ2 SHOK TO_B0.
  { to_awr_rs.
    eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U21M in Ha.
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - apply awr_ok_x_cons_g.
      + intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
               | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      + apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
        apply awr_ok_x_nil. }
  (* the model on this arm *)
  assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
  assert (EST2 : TW.S_state (slost_w1 Bw) = TS0.DIGINET_S_ONLINE)
    by (rewrite (proj1 (to_w1_facts Bw HLB)); exact Hst).
  assert (HNI : TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE)
    by (rewrite EST2; unfold TS0.DIGINET_S_ONLINE, TS0.DIGINET_S_IDLE; lia).
  destruct (sn_model TF Bw TS0.DIGINET_R_SILENCE Bw' HLM HNI) as (HNT & HNM).
  (* what run 2 kept, and the notice's 72 bytes *)
  assert (KRN : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((F + 32 <= a < F + 48) \/ (TICK_S + 112 <= a < TICK_S + 116)) ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memM a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (TICK_S + 112 <= x < TICK_S + 116)) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
    cbn [In] in Hiw.
    repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx;
      rewrite ?U21M in Hx; unfold TICK_S, TA_g_s; first [left; lia | right; lia | lia] |]).
    destruct Hiw. }
  change (0 mod 256) with 0 in HsetM.
  assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W) (ms_mem ms2) a = Some 0).
  { intros a Ha.
    rewrite (KRN a ltac:(unfold TICK_FBYTES in *; lia)
      ltac:(intros [Hz | Hz]; [lia | unfold TICK_S, TA_g_s, TW.SZ_g_s, TICK_FBYTES in *; lia])).
    replace a with (F + 48 + (a - (F + 48))) by lia. exact (HsetM (a - (F + 48)) ltac:(lia)). }
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RP0. cbn [ms_mem restrict] in RP0.
  pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RP1. cbn [ms_mem restrict] in RP1.
  pose proof (SlostNtc.sn_chunk_val E2 (w_H W) (ms_mem ms2) (Some 21%nat) _ _ _ _ _ 0 8 (SLit 2) RP0
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
  pose proof (SlostNtc.sn_chunk_val E2 (w_H W) (ms_mem ms2) (Some 21%nat) _ _ _ _ _ 8 8 (SLit 17179869186) RP0
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
  pose proof (SlostNtc.sn_chunk_val E2 (w_H W) (ms_mem ms2) None _ _ _ _ _ (TICK_S + 112) 4 (SLit 0) RP1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
  cbn [base_val] in VP0, VP8, VG. rewrite U21M in VP0, VP8. rewrite Z.add_0_l in VG.
  change (N.to_nat 8) with 8%nat in VP0, VP8. change (N.to_nat 4) with 4%nat in VG.
  change (bv_unsigned (sv_denot E2 (SLit 2)) mod 2 ^ (8 * Z.of_N 8)) with 2 in VP0.
  change (bv_unsigned (sv_denot E2 (SLit 17179869186)) mod 2 ^ (8 * Z.of_N 8)) with 17179869186 in VP8.
  change (bv_unsigned (sv_denot E2 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG.
  rewrite Z.add_0_r in VP0. replace (F + 32 + 8) with (F + 40) in VP8 by lia.
  destruct (to_val_split2 (mrestrict (w_H W) (ms_mem ms2)) (F + 40) VP8) as [VP8a VP8b].
  replace (F + 40 + 4) with (F + 44) in VP8b by lia.
  assert (VP8a' : val_mem segs (mrestrict (w_H W) (ms_mem ms2)) (F + 40) 4 (TW.S_state (slost_w1 Bw)))
    by (rewrite EST2; exact VP8a).
  pose proof (to_nb (w_H W) (ms_mem ms2) F (TW.S_state (slost_w1 Bw)) TS0.DIGINET_R_SILENCE
    VP0 VP8a' VP8b ZMN) as HNB.
  (* the world relation after the store of 0 at s + 112 *)
  assert (PTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms2)) (slost_w2 Bw)).
  { rewrite sn_w2_eq.
    apply (tw_write TMAP_A (aview segs (w_H W) memM) _ (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 0
      TMAP_A_ok TW2 TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. assert (L0 : YO0f.le_byte 0 4 j = 0)
        by (unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia; reflexivity).
      rewrite L0. unfold aview. replace (TA_g_s + 112 + Z.of_nat j) with (TICK_S + 112 + Z.of_nat j)
        by (unfold TICK_S; lia).
      rewrite (VG j Hj), L0. reflexivity.
    - intros x Hx Hn.
      assert (HxG : inG TG.G_HARNESS x).
      { destruct Hx as (o & b & n & Hin3 & Hxr). unfold inG. apply Exists_exists. exists (b, n).
        split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
      pose proof (inG_low segs B transport_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
      apply KRN; [lia|].
      intros [Hz | Hz]; [| apply Hn; unfold TICK_S, TA_g_s in *; lia].
      apply (N2 x); [left; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img x HxG)]. }
  (* the registers at `jalr a2` *)
  assert (E32N : ew E2 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
  { unfold E2. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsM (to_vals2 Bw) 0) as X. cbn [Nat.add nth to_vals2] in X. rewrite X.
    rewrite <- (sn_notify Bw HLB), HNT. reflexivity. }
  to_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
    ltac:(cbn [sv_denot]; rewrite E32N, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  to_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11
    ltac:(cbn [sv_denot]; rewrite U21M; rewrite Z.add_0_r; reflexivity).
  to_reg HS (Z_to_bv 5 2) (w64 sp1) T2b
    ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 2 ltac:(hnf; lia)) P2)).
  to_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3b
    ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 3 ltac:(hnf; lia)) P3)).
  to_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4b
    ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 4 ltac:(hnf; lia)) P4)).
  to_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8b
    ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 8 ltac:(hnf; lia)) P8)).
  to_reg HS (Z_to_bv 5 9) (w64 sp1) T9b
    ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 9 ltac:(hnf; lia)) P9)).
  to_reg HS (Z_to_bv 5 18) (w64 F) T18b
    ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 18 ltac:(hnf; lia)) P18)).
  to_reg HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) T19b
    ltac:(cbn [sv_denot]; rewrite (EE2 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 19 ltac:(hnf; lia)) P19)).
  to_reg HS (Z_to_bv 5 27) (w64 F) T27b
    ltac:(cbn [sv_denot]; rewrite (EE2 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans (HPM 27 ltac:(hnf; lia)) P27)).
  (* what the call kept, from its entry to the call of notice *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
  assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ to_Z F sp1 a ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) mem2 a).
  { intros a Ha Hn.
    rewrite (KRN a Ha ltac:(intros [Hz | Hz]; apply Hn; [right; left; exact Hz | right; right; exact Hz])).
    apply KA2; [exact Ha | intros Hz; apply Hn; left; exact Hz]. }
  assert (GA3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG.
  assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    destruct HFapp as (_ & [HL | (HH1 & HH2)]); [right | left];
    unfold TICK_FBYTES, SHADOW_OFF in *; lia. }
  assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms2) (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi.
    rewrite (KRN (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF in *; lia)
      ltac:(intros [Hz | Hz]; unfold TICK_S, TA_g_s, SHADOW_OFF in *; lia)).
    rewrite (HeffM' (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF in *; lia)
      ltac:(unfold SHADOW_OFF in *; lia) ltac:(unfold SHADOW_OFF in *; lia)).
    exact (ZS1 i Hi). }
  assert (HSZ : forall a, to_Z F sp1 a ->
    (spZ regs - TICK_STK <= a < spZ regs) \/ dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos) a \/
    inG TG.G_HARNESS a).
  { intros a [[[Hz | [Hz | Hz]] | [Hz | Hz]] | [Hz | Hz]].
    - right; left; right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
             | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
    - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
             | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
    - right; left; left. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - left. unfold TICK_FRAME, TICK_ALIGN in *. lia.
    - right; left; left. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s)
             | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia]. }
  pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
    (ms_mem ms2) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (tick_wr Bw)
    (to_Z F sp1) HGX HARc HAR2 Hfrs ltac:(intros bm Hb; rewrite Hbl; exact Hb) eq_refl EF eq_refl FFL
    ltac:(unfold TICK_FRAME, TICK_ALIGN in *; lia) ltac:(lia) HSZ HK KA3 GA3) as KCN.
  assert (GKN : gx_kept_ex segs TG.G_HARNESS (tick_wr Bw) W memc W (ms_mem ms2)).
  { intros a Ha Hn.
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
    rewrite (KA3 a ltac:(lia)).
    - exact (HGK a Ha).
    - intros [[[Hz | [Hz | Hz]] | [Hz | Hz]] | [Hz | Hz]].
      + unfold SHADOW_OFF in Hz. lia.
      + exact (Hn (to_wr_dcv Bw a Hz)).
      + exact (Hn (to_wr_inflight Bw a Hz)).
      + apply (N2 a); [left; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img a Ha)].
      + lia.
      + apply (N2 a); [left; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img a Ha)].
      + exact (Hn (to_wr_state Bw a Hz)). }
  pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
  assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
  (* +0x618: `jalr a2`, a2 = notice *)
  assert (P4n : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
  assert (P5n : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
  eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W E2 _ _ _ _ 0x600e7 (1%bv : bv 5)
    (12%bv : bv 5) (TI.ti_notice timg_A) HEI HS eq_refl);
    [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4n
    | exact P5n |].
  intros matC msC EmsC _. subst msC.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    set (regsC := rg); set (mdC := mdx);
    change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms2) mdC) Qx) end.
  assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (34412 + 4)))
    by (unfold regsC; rewrite YK11.getr_same by (intros Hcc; apply (f_equal bv_unsigned) in Hcc;
        vm_compute in Hcc; discriminate Hcc); reflexivity).
  assert (RCK : forall rr : bv 5, bv_unsigned rr <> 1 -> YK11.getr regsC rr = YK11.getr (ms_regs ms2) rr)
    by (intros rr Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
  assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2b).
  assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3b).
  assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4b).
  assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 32))
    by (rewrite RCK by (vm_compute; discriminate); exact T11).
  assert (USPC : spZ regsC = sp1)
    by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
  assert (EBN : BASE + (34412 + 4) = 0x898d4) by (vm_compute; reflexivity).
  eapply SRr_bind.
  { exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms2) mdC (k + 0) regsC
      (F + 32) (slost_ntc Bw TS0.DIGINET_R_SILENCE) TF (slost_w2 Bw) Bw'
      ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
      ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
      ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
      RC3 RC4 RC11
      ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
            rewrite M1, Z.add_0_r in D1; rewrite D1;
            replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring; apply Z.mod_mul; lia)
      ltac:(rewrite USPC; unfold TICK_FRAME, TICK_ALIGN in *; lia) ltac:(rewrite USPC; lia)
      (to_ntc_at B lyc S2 W (ms_mem ms2) _ regsC Bw TS0.DIGINET_R_SILENCE F pos LAWS HARN Hin EF HF0 HF64
         HFc HFapp ltac:(rewrite USPC; unfold TICK_FBYTES, TICK_FRAME, TICK_ALIGN in *; lia)
         ltac:(unfold TS0.DIGINET_R_SILENCE; lia) ZSN HNB)
      (trans_tframe_at_top B LAWS HRU HRE lyc Sc W memc mdc S2 (ms_mem ms2) _ regs regsC TF (tick_wr Bw)
         TICK_STK NOTICE_STK TICK_CID pos HARc HARN Hfrs Hbl HSTKLT KCN GKN Hapart (to_wr_lo B HGX Bw)
         ltac:(rewrite USPC; unfold TICK_FRAME, TICK_ALIGN in *; lia) ltac:(rewrite USPC; lia) HTFe)
      ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
            destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
            apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
            intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
            unfold TG.G_HARNESS_LO in Gh; lia)
      PTW HNM
      (to_apart B lyc S2 W mem2 md2 W (ms_mem ms2) TF Bw F pos LAWS HAR2 Hin EF Hapart)
      ltac:(intros HD; exfalso; unfold slost_ntc in HD; cbn [TI.n_kind] in HD;
            unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
      ltac:(unfold TICK_EV in Hev; unfold NOTICE_EV; lia)). }
  intros W3 c3 _ HPOST.
  unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
  assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  clear HJi3 memS3.
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
  assert (EF3 : frame_addr ly3 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
  assert (Hin3 : In (TICK_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 TICK_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
  rewrite EF3 in HFsh3. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh3.
  change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh3.
  assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
  assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
  { intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
  assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8)).
  { rewrite (HP3 19 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T19b. }
  (* what the call kept, from its entry to notice's return *)
  assert (KCr3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms2) W3 mem3
      (spZ regs - TICK_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (tick_wr Bw)
      (notice_wr (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_SILENCE))
      (dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos))).
    - unfold TICK_FRAME, TICK_ALIGN in *. lia.
    - lia.
    - intros c p. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - intros bm Hbm. rewrite Hbl. exact Hbm.
    - exact N1.
    - exact N3.
    - exact KCN.
    - exact HK3.
    - rewrite USPC. unfold TICK_FRAME, TICK_ALIGN in *. lia.
    - rewrite USPC. lia.
    - intros a Ha. left. exact (to_wr_ntc Bw a Ha). }
  (* +0x61c .. +0x648: s10 = 0, shadow bytes 4 .. 12 := 0xf8, to the epilogue cut *)
  rewrite RC1. change (Z_to_bv 64 (BASE + (34412 + 4))) with (Z_to_bv 64 (BASE + TO_AFTER_NTC)).
  clear HS SHOK HEI.
  pose proof (to_entry3 W3 regs3 mem3 F R3_19 HF0 HF64 ltac:(unfold TICK_FBYTES in *; lia)
    ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HSr3.
  assert (HEIr3 : img_env VAL A_LIM (to_Eb regs3)) by apply to_Eb_img.
  assert (U19c : bv_unsigned (ew (to_Eb regs3) 19) = SHADOW_OFF + F / 8)
    by (rewrite (to_ew_reg regs3 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64;
        apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  assert (SHOKr3 : sh_ok segs TO_Bx (@nil shent) (to_Eb regs3) (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_to_tok RUNTO HSr3 HJ3 SHOKr3 TO_B0 TICK_EPI.
  { to_awr_rs.
    eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19c in Ha.
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3.
      change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    - apply awr_ok_x_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md5 := mdx) in * end. clearbody md5.
  lazymatch type of HSr3 with context [restrict _ ?m] => rename m into ms4 end.
  assert (KRr4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
    aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
    cbn [In] in Hiw.
    repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx;
      rewrite ?U19c in Hx; lia |]).
    destruct Hiw. }
  assert (GAr4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KCr4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md4 mem3
      (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (tick_wr Bw)
      (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl
      FFL ltac:(unfold TICK_FRAME, TICK_ALIGN in *; lia) ltac:(lia)); [| exact KCr3 | exact KRr4 | exact GAr4].
    intros a Ha. right. left. right. left. change (fs_frame_bytes TICK_CID / 8) with 256. cbv beta in Ha. lia. }
  pmkst HSr3.
  (* the registers the epilogue reads *)
  to_reg HSr3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) F27
    ltac:(cbn [sv_denot]; rewrite (to_ew_reg regs3 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  to_reg HSr3 (Z_to_bv 5 26) (Z_to_bv 64 0) F26 ltac:(reflexivity).
  (* the bytes the epilogue reads: the saved words above sp1 and the frame's last word *)
  pose proof HK3 as (K31 & _ & _ & K34 & _).
  assert (HALC : F + TICK_FBYTES <= spZ regs - TICK_STK) by (unfold TICK_FRAME, TICK_ALIGN in *; lia).
  assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
  { intros a Ha. rewrite KRr4 by (unfold SHADOW_OFF in *; lia). rewrite USPC in K31. rewrite K31 by lia.
    apply KA3; [lia|].
    unfold to_Z, to_Z2, to_Z1, TICK_S, TA_g_s, SHADOW_OFF, TICK_FBYTES in *. lia. }
  assert (KFL : forall i, 0 <= i < 8 ->
    aview segs (w_H W3) (ms_mem ms4) (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
  { intros i Hi. rewrite KRr4 by (unfold SHADOW_OFF, TICK_FBYTES in *; destruct HSHF; lia).
    rewrite (K34 TICK_CID pos (F + 2040 + i) Hin).
    - apply KA3; [unfold TICK_FBYTES in *; lia|].
      unfold to_Z, to_Z2, to_Z1, TICK_S, TA_g_s, SHADOW_OFF, TICK_FBYTES in *.
      destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; destruct HSHF; lia.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - intros Hw. apply (N2 (F + 2040 + i)); [left; change (fs_frame_bytes TICK_CID) with 2048; lia|].
      exact (trans_g_img _ (notice_wr_G _ _ _ Hw)). }
  assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold TICK_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Qx) end.
  apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem ms4) md5 0 (ms_regs ms4) HFIX).
  + split; [|split].
    * split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
      split; [unfold TICK_EV; lia|].
      split; [exact Hfrs3|].
      split; [rewrite <- Hbl; exact Hperm3|].
      split; [exact ELF3c|].
      split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
      split; [exact KCr4|].
      split.
      -- rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
         pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK.
         unfold TICK_FRAME, TICK_ALIGN in *. lia.
      -- unfold TICK_FBYTES. rewrite <- HFLw. unfold TICK_FBYTES.
         replace (F + 2048 - 8) with (F + 2040) by lia.
         apply rdword_ext. intros i Hi. exact (KFL i Hi).
    * apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KRr4; [lia | unfold SHADOW_OFF in *; lia].
    * rewrite (sn_gfn' TF Bw TS0.DIGINET_R_SILENCE Bw' HLB HNM). exact Hgf.
  + assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
      YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms2) (Z_to_bv 5 n))
      by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
    split; [split|].
    * exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2b)).
    * split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
               (eq_trans T3b (eq_sym Hgp))))|].
      split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
               (eq_trans T4b (eq_sym Htp))))|].
      split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
               (eq_trans T8b R8')))|].
      split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T9b))|].
      split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T18b))|].
      exact (eq_trans F27 (eq_trans (CH 27 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T27b)).
    * refine (eq_trans F26 _). rewrite Hr0. reflexivity.
- (* no silence: one instruction to the step cut *)
  rewrite branch_geu_U, (U_atom _ 11%nat _ D11 Rv1), (U_atom _ 10%nat _ D10 Rv0) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (HTO : (TS0.ms_m (TW.S_cfg_offline_ms Bw) <=? TS0.u64 (now - TW.S_last_rx_us Bw)) = false)
    by (apply Z.leb_gt; lia).
  pose proof (to_model_step TF Bw now Bw' r Hst HTO Hm) as HGO.
  paj_run_to_tok RUNTO HS HJ1 SHOK TO_B0 TICK_STEP.
  { to_awr_rs. apply awr_ok_x_nil. }
  to_after HS W KD1 GR1 (ms_mem ms0) msF. clear HF HFr HG.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 2) 2%nat T2 Y2.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 3) 3%nat T3 Y3.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 4) 4%nat T4 Y4.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 8) 8%nat T8 Y8.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 9) 9%nat T9 Y9.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 18) 18%nat T18 Y18.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 19) 19%nat T19 Y19.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 20) 20%nat T20 Y20.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 21) 21%nat T21 Y21.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 22) 22%nat T22 Y22.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 23) 23%nat T23 Y23.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 24) 24%nat T24 Y24.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 25) 25%nat T25 Y25.
  to_kreg HS to_ew_reg (ms_regs ms0) (Z_to_bv 5 27) 27%nat T27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_STEP)) mm rom) mdx) Q) end.
  assert (KDF : forall a, aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) mem2 a)
    by (intros a; rewrite (KD1 a); exact (KD0 a)).
  assert (GRF : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; exact (GR1 a (GR0 a Ha))).
  apply (STEP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
    S2 (ms_mem msF) _ (ms_regs msF) HFIX).
  + split; [|exact HGO].
    exact (to_pre_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2
      (ms_mem msF) _ (proj1 HCUR) HJ1 KDF GRF).
  + unfold tick_regs_disp, tick_regs_run, tick_regs_base.
    split; [split|].
    * split; [exact (eq_trans Y2 R2')|].
      split; [exact (eq_trans Y3 R3')|].
      split; [exact (eq_trans Y4 R4')|].
      split; [exact (eq_trans Y8 R8')|].
      split; [exact (eq_trans Y9 R9')|].
      split; [exact (eq_trans Y18 R18')|].
      exact (eq_trans Y27 R27').
    * split; [exact (eq_trans Y19 R19')|].
      split; [exact Y20|].
      split; [exact (eq_trans Y22 R22')|].
      split; [exact (eq_trans Y23 R23')|].
      split; [exact Y24|].
      exact (eq_trans Y25 R25').
    * exact (eq_trans Y21 R21').
Qed.

End to.

(* The online piece of the walk of diginet_session_tick (TickCut.v tick_online_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_online : forall fx rc B MT, @tick_online_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@to_holds fx rc B MT). Qed.

Print Assumptions tick_online.
