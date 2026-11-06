(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 259 of its 350 lines of code are new or changed and 1119 lines of the source are left out. *)
(* TickBWake: the wake piece of diginet_session_tick's image-B G-form walk, tick_wake : tick_wake_stmt
   (lib/B/Prog/TickCutB.v), code 0x89264 .. 0x892dc (+0x1c8 .. +0x240 from the entry 0x8909c), no call.
   rule 24: proves no function (one piece of a walk; the walk is composed at TickCutB.v tick_holds_of).
   From the wake cut (tick_wake_cur: the state the head loaded is S_WAKING, no byte of G stored yet), run 1 (the
   PaRun token engine over the caller's G journal, TransportGRunB.v paj_run_x) does the checked loads of
   g_s.wake_sent_us (s + 152, 8 bytes) and g_s.cfg.wake_timeout_ms (s + 44, 4 bytes), loads now from s1 + 56 and stops
   at `bltu a1, a0` (+0x208). Taken (no timeout; TickCutB.v tick_model_wake gives tick_go): one step to the step cut,
   with the memory and the registers of the cut. Not taken (the session is lost): one step to +0x20c, then run 2
   does the checked stores of 0 at s + 212 and s + 168 (the world becomes slost_w1 Bw), a2 = 6 (R_WAKE_TIMEOUT) and
   `j` to the lost cut (+0x478); the lost cut's facts come from TickBWake_kit.v twb_lost_cur. Template: image A's
   TickWake.v (run 1 and the stores of run 2). trans_src_ok is not used. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB TickBKit TickBWake_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Run 1, +0x1c8 .. +0x208: the two g_s fields it loads (atoms 33, 34), their two shadow bytes 5 and 19, and now at
   s1 + 56 (atom 32; s1 is atom 9). s4 is s and s8 the shadow base, as literals. No region has a write window. *)
Definition TWBW_R1_cfg : YP09.region :=
  YP09.mkRegion None (TICK_S + 44) (TICK_S + 48) 0 0 [YP09.mkChunk (TICK_S + 44) (YP09.CVal 4 (SOff 33 0))].
Definition TWBW_R1_sent : YP09.region :=
  YP09.mkRegion None (TICK_S + 152) (TICK_S + 160) 0 0 [YP09.mkChunk (TICK_S + 152) (YP09.CVal 8 (SOff 34 0))].
Definition TWBW_R1_sh : YP09.region :=
  YP09.mkRegion None (TWB_SH + 5) (TWB_SH + 20) 0 0
    [YP09.mkChunk (TWB_SH + 5) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TWB_SH + 19) (YP09.CVal 1 (SLit 0))].
Definition TWBW_R1_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0))].
Definition TWBW_FACTS1 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_twbw1 : sstate :=
  mkSS TICK_WAKE TWB_REGS2 [TWBW_R1_cfg; TWBW_R1_sent; TWBW_R1_sh; TWBW_R1_now] None TWBW_FACTS1.
(* The lost arm's first instruction, the fall-through of `bltu` at +0x208. *)
Definition TWBW_C2 : Z := TICK_WAKE + 0x44.

(* `bltu a1, a0` at +0x208 with a1 = now - wake_sent_us (the engine's now + sent * -1) and a0 = the zero-extended
   cfg.wake_timeout_ms times 1000: taken exactly when the model's timeout test is false. *)
Lemma twbw_tmo : forall (E : env) now x t,
  ew E 32 = Z_to_bv 64 now -> ew E 34 = Z_to_bv 64 x -> ew E 33 = Z_to_bv 64 t ->
  0 <= now < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= t < 2 ^ 32 ->
  branch_taken BC_LTU
    (sv_denot E (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))))
    (sv_denot E (SMd M_MUL (SExt false 32 (SOff 33 0)) (SLit 1000)))
  = negb (TS0.ms_m t <=? TS0.u64 (now - x)).
Proof.
  intros E now x t E32 E34 E33 Hn Hx Ht.
  rewrite branch_ltu_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SMd. cbn [zmd_raw].
  rewrite U_zext, (U_atom E 32 now E32 Hn), (U_atom E 34 x E34 Hx), (U_atom E 33 t E33 ltac:(lia)), !U_SLit.
  unfold zcanon, M64, TS0.ms_m, TS0.u64.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  change (1000 mod 2 ^ 64) with 1000.
  rewrite (Z.mod_small t (2 ^ 32)) by lia.
  rewrite (Z.mod_small (t * 1000) (2 ^ 64)) by lia.
  rewrite Z.add_mod_idemp_r by lia.
  replace (now + x * (2 ^ 64 - 1)) with ((now - x) + x * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.leb_antisym, negb_involutive. reflexivity.
Qed.

Section twbw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition twbw_vals1 (Bw : list byte) (now : Z) : list word :=
  [Z_to_bv 64 now; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 44) 4); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 152) 8)].
Definition twbw_E1 (regs : bvmap 5 word) (Bw : list byte) (now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (twbw_vals1 Bw now)).

Lemma twbw_entry1_0 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 - 64 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (twbw_E1 regs Bw now)
    (mkSS TICK_WAKE sr_atoms [TWBW_R1_cfg; TWBW_R1_sent; TWBW_R1_sh; TWBW_R1_now] None TWBW_FACTS1)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_WAKE)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp Hsp32 Hnow Hrd.
  set (E := twbw_E1 regs Bw now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, twbw_E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (twbw_vals1 Bw now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, twbw_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth twbw_vals1] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 44) 4) as R33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 152) 8) as R34.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TWBW_R1_cfg TWBW_R1_sent TWBW_R1_sh
        TWBW_R1_now base_val]; rewrite ?U9.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 44) 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 44) 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      replace (0 + (TICK_S + 44)) with (TB_g_s + 44) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 44 4 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 152) 8 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 152) 8));
        [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
      replace (0 + (TICK_S + 152)) with (TB_g_s + 152) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 152 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TWB_SH; lia|]. split; [unfold TWB_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TWB_SH + 5) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. apply YE2y.val_mem1_of_aview. exact (twb_gsh0 B ly S W mem md 5 HTC HAR ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (TWB_SH + 19) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. apply YE2y.val_mem1_of_aview. exact (twb_gsh0 B ly S W mem md 19 HTC HAR ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 32 0) now); [apply DEN; [exact E32 | exact Hnow] | exact Hnow | lia |].
      apply val_mem_of_rdword. exact Hrd.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TWBW_R1_cfg, TWBW_R1_sent, TWBW_R1_sh, TWBW_R1_now.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TWB_SH, SHADOW_OFF, TICK_S, TB_g_s in *. repeat split; first [exact I | lia].
  - unfold TWBW_FACTS1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma twbw_entry1 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 - 64 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (twbw_E1 regs Bw now) ss_twbw1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_WAKE)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 R20 R24 Hsp Hsp32 Hnow Hrd.
  rewrite restrict_mkst_fx.
  pose proof (twbw_entry1_0 ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp Hsp32 Hnow Hrd) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

Lemma twbw_wake : @tick_wake_stmt fx rc B MT.
Proof.
unfold tick_wake_stmt. intros STEP LOST. unfold tick_wake_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF & Hrom &
  Hapart & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnow56) & Hbl & HGK & Htw1) & Hst).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24) & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HTS : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
assert (HES : ESTACK <= SENDDATA_STK) by (apply Z.leb_le; reflexivity).
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47 - 64) by lia.
(* the model at S_WAKING *)
rewrite (tick_model_wake timg_B TF Bw now Hst) in Hm.
(* +0x1c8 .. +0x208: the checked loads of s + 152 and s + 44, now from s1 + 56, `bltu a1, a0` *)
pose proof (twbw_entry1 lyc S2 W regs2 mem2 md2 Bw now sp1 HTC HAR2 Htw1 R9 R20 R24 Hsp1b (proj2 Hsp1) Hnow Hnow56)
  as HS.
set (E1 := twbw_E1 regs2 Bw now) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1, twbw_E1; apply Eimg_env).
assert (EE1 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E1 n = YK11.getr regs2 r0)
  by (intros n r0 Hn; unfold E1, twbw_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs TWB_Bx (@nil shent) E1 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ1 SHOK TWB_B0.
{ twb_awr_vac. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
twb_kept_vac HFr KD1.
assert (GR1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (EX1 : forall j, (j < 3)%nat -> ew E1 (32 + j) = nth j (twbw_vals1 Bw now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E1, twbw_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX1 0%nat ltac:(lia)) as E32. pose proof (EX1 1%nat ltac:(lia)) as E33.
pose proof (EX1 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth twbw_vals1] in E32, E33, E34.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 44) 4) as R33.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 152) 8) as R34.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
pose proof (twbw_tmo E1 now (TW.u_at Bw (TW.OFF_g_s + 152) 8) (TW.u_at Bw (TW.OFF_g_s + 44) 4) E32 E34 E33 Hnow R34
  R33) as HTMO.
change (TW.u_at Bw (TW.OFF_g_s + 152) 8) with (TW.S_wake_sent_us Bw) in HTMO.
change (TW.u_at Bw (TW.OFF_g_s + 44) 4) with (TW.S_cfg_wake_timeout_ms Bw) in HTMO.
psrr_branch_tok RUN BR HS SHOK TWB_B0.
- (* now - wake_sent_us below the timeout: no timeout, one step to the step cut (+0x2a4) *)
  rewrite HTMO in Hc. apply negb_true_iff in Hc. rewrite Hc in Hm. clear Hc.
  paj_run_to_tok RUNTO HS HJ1 SHOK TWB_B0 TICK_STEP.
  { twb_awr_vac. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msS end.
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  twb_kept_vac HFr KD2.
  assert (GR2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem msS) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  twb_keep HS EE1 regs2 2 2%nat Y2. twb_keep HS EE1 regs2 3 3%nat Y3. twb_keep HS EE1 regs2 4 4%nat Y4.
  twb_keep HS EE1 regs2 8 8%nat Y8. twb_keep HS EE1 regs2 9 9%nat Y9. twb_keep HS EE1 regs2 18 18%nat Y18.
  twb_keep HS EE1 regs2 19 19%nat Y19. twb_keep HS EE1 regs2 21 21%nat Y21. twb_keep HS EE1 regs2 22 22%nat Y22.
  twb_keep HS EE1 regs2 23 23%nat Y23. twb_keep HS EE1 regs2 25 25%nat Y25. twb_keep HS EE1 regs2 27 27%nat Y27.
  sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) Y20 ltac:(reflexivity).
  sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_STEP)) mm rom) mdx) Q) end.
  apply (STEP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
    (ms_mem msS) md3 (ms_regs msS) HFIX).
  + split; [| exact Hm].
    apply (twb_pre_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2
      (ms_mem msS) md3 (proj1 HCUR) HJ1).
    * intros a. rewrite KD2. exact (KD1 a).
    * intros a Ha. exact (GR2 a (GR1 a Ha)).
  + refine (conj (conj (conj (eq_trans Y2 R2) (conj (eq_trans Y3 R3) (conj (eq_trans Y4 R4) (conj (eq_trans Y8 R8)
      (conj (eq_trans Y9 R9) (conj (eq_trans Y18 R18) (eq_trans Y27 R27))))))) (conj (eq_trans Y19 R19) (conj Y20
      (conj (eq_trans Y21 R21) (conj (eq_trans Y22 R22) (conj (eq_trans Y23 R23) Y24)))))) (eq_trans Y25 R25)).
- (* the wake timeout passed: the session is lost *)
  rewrite HTMO in Hc. apply negb_false_iff in Hc. rewrite Hc in Hm. clear Hc.
  (* +0x208 not taken: one step to +0x20c *)
  paj_run_to_tok RUNTO HS HJ1 SHOK TWB_B0 TWBW_C2.
  { twb_awr_vac. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  twb_kept_vac HFr KD2.
  assert (GR2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KDB : forall a, aview segs (w_H W) (ms_mem msB) a = aview segs (w_H W) mem2 a)
    by (intros a; rewrite KD2; exact (KD1 a)).
  assert (GRB : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; exact (GR2 a (GR1 a Ha))).
  clear KD1 KD2 GR1 GR2.
  (* the registers at +0x20c *)
  twb_keep HS EE1 regs2 2 2%nat V2. twb_keep HS EE1 regs2 3 3%nat V3. twb_keep HS EE1 regs2 4 4%nat V4.
  twb_keep HS EE1 regs2 8 8%nat V8. twb_keep HS EE1 regs2 9 9%nat V9. twb_keep HS EE1 regs2 18 18%nat V18.
  twb_keep HS EE1 regs2 27 27%nat V27.
  sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) V20 ltac:(reflexivity).
  sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) V24 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TWBW_C2)) mm rom) mdx) Q) end.
  clear HS SHOK.
  set (regsB := ms_regs msB) in *. set (mB := ms_mem msB) in *. clearbody regsB mB. clear msB.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARB.
  (* +0x20c .. +0x240: the checked stores of 0 at s + 212 and s + 168, a2 = 6, `j` to the lost cut *)
  pose proof (twb_entry2 B lyc S2 W regsB mB md3 TWBW_C2 HTC HARB V20 V24) as HS.
  set (E2 := Eimg (PI := PI_transportb) (Ereg regsB [])) in HS.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
  assert (EE2 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E2 n = YK11.getr regsB r0)
    by (intros n r0 Hn; unfold E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (SHOK2 : sh_ok segs TWB_Bx (@nil shent) E2 (mrestrict (w_H W) mB)) by constructor.
  paj_run_to_tok RUNTO HS HJ1 SHOK2 TWB_B0 TICK_LOST.
  { twb_awr2. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ twb_Z a ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mB a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ twb_Z HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta. sn_winB Hiw Hx ltac:(unfold twb_Z, TICK_S, TB_g_s; lia). }
  assert (GA2 : forall a, apresent (w_H W) mB a -> apresent (w_H W) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
  cbn [ms_mem restrict] in RS0, RS1.
  pose proof (sn_chunk_valB E2 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 6158100 4 (SLit 0) RS0
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG212.
  pose proof (sn_chunk_valB E2 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 6158056 4 (SLit 0) RS1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG168.
  cbn [base_val] in VG212, VG168. change (N.to_nat 4) with 4%nat in VG212, VG168.
  change (bv_unsigned (sv_denot E2 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG212, VG168.
  assert (Z212 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms3) (TICK_S + 212 + j) = Some 0).
  { intros j Hj. apply (twb_aview_of_val0 (w_H W) (ms_mem ms3) (TICK_S + 212) 4); [|lia].
    replace (TICK_S + 212) with (0 + 6158100) by (unfold TICK_S, TB_g_s; lia). exact VG212. }
  assert (Z168 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms3) (TICK_S + 168 + j) = Some 0).
  { intros j Hj. apply (twb_aview_of_val0 (w_H W) (ms_mem ms3) (TICK_S + 168) 4); [|lia].
    replace (TICK_S + 168) with (0 + 6158056) by (unfold TICK_S, TB_g_s; lia). exact VG168. }
  assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ twb_Z a ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a)
    by (intros a Ha Hn; rewrite (KR2 a Ha Hn); exact (KDB a)).
  assert (GAN : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms3) a)
    by (intros a Ha; exact (GA2 a (GRB a Ha))).
  clear HF HFr HG RS0 RS1 VG212 VG168.
  (* the registers at the lost cut *)
  twb_keep HS EE2 regsB 2 2%nat Q2. twb_keep HS EE2 regsB 3 3%nat Q3. twb_keep HS EE2 regsB 4 4%nat Q4.
  twb_keep HS EE2 regsB 8 8%nat Q8. twb_keep HS EE2 regsB 9 9%nat Q9. twb_keep HS EE2 regsB 18 18%nat Q18.
  twb_keep HS EE2 regsB 27 27%nat Q27.
  sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) Q20 ltac:(reflexivity).
  sn_regB HS (Z_to_bv 5 12) (w64 TS0.DIGINET_R_WAKE_TIMEOUT) Q12 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_LOST)) mm rom) mdx) Q) end.
  apply (LOST LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
    TS0.DIGINET_R_WAKE_TIMEOUT S2 (ms_mem ms3) md4 (ms_regs ms3) HFIX).
  + exact (twb_lost_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
      mem2 md2 (ms_mem ms3) md4 TS0.DIGINET_R_WAKE_TIMEOUT LAWS0 HFIX (proj1 HCUR) HJ1 Z212 Z168 KAN GAN
      (or_introl eq_refl) Hm).
  + refine (conj (conj (eq_trans Q2 (eq_trans V2 R2)) (conj (eq_trans Q3 (eq_trans V3 R3))
      (conj (eq_trans Q4 (eq_trans V4 R4)) (conj (eq_trans Q8 (eq_trans V8 R8)) (conj (eq_trans Q9 (eq_trans V9 R9))
      (conj (eq_trans Q18 (eq_trans V18 R18)) (eq_trans Q27 (eq_trans V27 R27)))))))) (conj Q20 Q12)).
Qed.

End twbw.

(* The wake piece of the walk of diginet_session_tick (TickCutB.v tick_wake_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_wake : forall fx rc B MT, @tick_wake_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@twbw_wake fx rc B MT). Qed.

Print Assumptions tick_wake.
