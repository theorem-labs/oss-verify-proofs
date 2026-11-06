(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module names changed; 548 of its 671 lines of code are new or changed and 1087 lines of the source are left out. *)
(* TickAckl: the ack-lost piece of diginet_session_tick's image-A G-form walk, tick_ackl : tick_ackl_stmt (TickCut.v),
   code 0x89904 .. 0x89a0c (+0x64c .. +0x754), from the cut tick_ackl_at to the tail cut tick_tail_at. Run 1 (PaRun
   token engine, TickAckl_ent.v ss_ta1) checks s + 212 through t1, saves t2 / a7 at s1 + 24 / s1 + 32, stores 0 at
   s + 212 and stats.ack_lost + 1 at s + 18240 (the world tick_ack_w1 Bw), sets s10 = p = frame + 256, unpoisons the
   notice's shadow bytes 32 .. 40 and sets up __asan_memset (p + 8, 0, 64), taken through TransportGCg.v gx_intrin_at;
   run 2 (ss_ta2) stores kind 5, the state, the counter and the retry into p and loads g_s.notify / notify_ctx; `jalr
   a2` at 0x899d4 calls notice through the premise transport_notice_cg with the notice tick_ack_ntc Bw (the same G
   journal; the call's kept facts fold with dk_kept_trans_nf_g); run 3 (ss_ta3) re-poisons the shadow bytes, loads
   a7 / t0 / t1 back and jumps to the tail cut, whose world is notice's (TickAckl_kit.v ta_model: set_M_fly_on
   (tick_ack_w1 Bw) 0) and whose run invariants come from tick_runinv Bw (ta_runinv_b0). *)
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
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_tick_cg TickCut TransportGNotice TickSrcKit TickAckl_kit TickAckl_ent.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The bytes run 1 may change: the notice's shadow bytes 32 .. 40, the saves at s1 + 24 .. s1 + 40, g_s.inflight and
   g_s.stats.ack_lost. *)
Definition ta_Z1 (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 32 <= x < SHADOW_OFF + F / 8 + 41) \/ (sp1 + 24 <= x < sp1 + 40) \/
  (TICK_S + 212 <= x < TICK_S + 216) \/ (TICK_S + 18240 <= x < TICK_S + 18248).

(* A register the run left as it was (its symbolic value is the atom n), from the equation EE of the valuation's
   atoms with the registers rg at the run's start. *)
Ltac ta_kreg HS EE rg nn zn H :=
  ta_reg HS (Z_to_bv 5 zn) (YK11.getr rg (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

Section ta. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma ta_holds : @tick_ackl_stmt fx rc B MT.
Proof.
unfold tick_ackl_stmt. intros TAIL. unfold tick_ackl_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof CALLEES as (CSF8 & HMS & HN & HIO & HSF & CS00 & HSD & HTK).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnoww) & Hbl & HGK & Htw1) &
  (Ht48 & Ht40) & Hm2).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R22 & R23 & R24 & R25) & R21 & R6 & R7 & R17).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TICK_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HPW : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a).
{ pose proof HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
assert (HTS : NOTICE_STK + 208 <= TICK_STK) by (vm_compute; congruence).
assert (HTS2 : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HNS : 4096 <= NOTICE_STK) by (vm_compute; congruence).
assert (HTS3 : 4096 + 208 <= TICK_STK) by (vm_compute; congruence).
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
destruct Hsp1 as (Hsp1r & Hs32).
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
destruct (FFL lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr lyc TICK_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  apply trans_g_img. apply (ta_row _ _ _ _ TMAP_A_g_s). unfold TICK_S in *. lia. }
assert (HFNI : forall x, F <= x < F + 2048 -> ~ inG TG.G_HARNESS x).
{ intros x Hx Hg. apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img x Hg)]. }
assert (HtwG : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x)
  by (intros x (o & b & n & Hin3 & Hx); exact (ta_row o b n x Hin3 ltac:(lia))).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (Hs0 : 2 ^ 46 <= sp1) by lia.
assert (Hs1 : sp1 + 64 <= 2 ^ 47) by lia.
(* the model on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (ta_model TF Bw now Bw' r HLB Hm2) as (HNT & HNM & HTT).
set (B0 := TW.set_M_fly_on (tick_ack_w1 Bw) 0) in *.
(* +0x64c .. +0x6b4: run 1, up to `jal __asan_memset` *)
pose proof (ta_entry1 B lyc S2 W regs2 mem2 md2 Bw F sp1 HTC HAR2 Htw1 R19 R9 R6 R17 R20 R24 HF0 HF64 ltac:(lia) HFG
  Hs0 Hs1 Hs32 ltac:(intros a Ha; apply HPW; lia) ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
set (E0 := ta_E1 regs2 Bw) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ta_E1; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E0, ta_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E0 27) = F)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs TA_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK TA_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID / 8) with 256.
    lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    apply (ta_row _ _ _ _ TMAP_A_g_s). unfold TA_g_s, TW.SZ_g_s. lia. }
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    apply (ta_row _ _ _ _ TMAP_A_g_s). unfold TA_g_s, TW.SZ_g_s. lia. }
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ta_Z1 F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ta_Z1 F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  ta_win Hiw Hx ltac:(rewrite ?U19, ?U9 in Hx; unfold ta_Z1, TICK_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
pose proof (st_ok_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3.
assert (ZS1 : forall i, 32 <= i < 41 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19.
  assert (Hi' : i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/ i = 40) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ta_chunk0 E0 (w_H W) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
pose proof (ta_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 7 0) RG1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VT2.
pose proof (ta_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 32 8 (SLit 6176928) RG1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VA7.
pose proof (ta_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158996 4 (SLit 0) RG2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG0.
pose proof (ta_chunk_val E0 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6177024 8 (SOff 32 1) RG3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VGA.
cbn [base_val] in VT2, VA7, VG0, VGA. rewrite U9 in VT2, VA7.
change (N.to_nat 8) with 8%nat in VT2, VA7, VGA. change (N.to_nat 4) with 4%nat in VG0.
change (bv_unsigned (sv_denot E0 (SLit 6176928)) mod 2 ^ (8 * Z.of_N 8)) with (TICK_S + 18144) in VA7.
change (bv_unsigned (sv_denot E0 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG0.
assert (D7 : sv_denot E0 (SOff 7 0) = YK11.getr regs2 7).
{ cbn [sv_denot]. rewrite (EE 7%nat 7%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite D7 in VT2.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs2 7)) as RT2. unfold bv_modulus in RT2.
change (2 ^ Z.of_N 64) with (2 ^ 64) in RT2.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in VT2. rewrite (Z.mod_small _ (2 ^ 64) RT2) in VT2.
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8))
  by (unfold E0, ta_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (DGA : bv_unsigned (sv_denot E0 (SOff 32 1)) mod 2 ^ (8 * Z.of_N 8) =
  TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8 + 1)).
{ pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18240) 8) as R32. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
  cbn [sv_denot]. rewrite E32, (unsigned_lit_small (TW.u_at Bw (TW.OFF_g_s + 18240) 8)) by exact R32.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, TS0.u64.
  change (bv_modulus 64) with (2 ^ 64). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Zmod_mod. }
rewrite DGA in VGA.
(* the world after the two stores *)
assert (PTW1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (tick_ack_w1 Bw)).
{ apply (ta_tw_w1 (aview segs (w_H W) mem2) _ Bw HLB Htw1).
  - intros j Hj. exact (ta_aview_val _ _ _ 4 0 VG0 j Hj).
  - intros j Hj. exact (ta_aview_val _ _ _ 8 _ VGA j Hj).
  - intros x (o & b & n & Hin3 & Hx) H1 H2.
    assert (HxG : inG TG.G_HARNESS x) by (apply (ta_row o b n x Hin3); lia).
    pose proof (inG_low segs B transport_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
    apply KR1; [lia|]. unfold ta_Z1, TICK_S. unfold SHADOW_OFF. lia. }
pmkst HS.
ta_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 264)) Q10 ltac:(cbn [sv_denot]; rewrite U27; reflexivity).
ta_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ta_reg HS (Z_to_bv 5 12) (Z_to_bv 64 64) Q12 ltac:(reflexivity).
ta_reg HS (Z_to_bv 5 26) (Z_to_bv 64 (F + 256)) Q26 ltac:(cbn [sv_denot]; rewrite U27; reflexivity).
ta_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ta_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 34572)) Q1 ltac:(apply codeptr_val; exact HEI).
ta_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ta_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
ta_reg HS (Z_to_bv 5 20) (w64 TICK_S) Q20 ltac:(reflexivity).
ta_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Q24 ltac:(reflexivity).
ta_kreg HS EE regs2 8%nat 8 Q8. ta_kreg HS EE regs2 9%nat 9 Q9. ta_kreg HS EE regs2 18%nat 18 Q18.
ta_kreg HS EE regs2 19%nat 19 Q19. ta_kreg HS EE regs2 21%nat 21 Q21. ta_kreg HS EE regs2 22%nat 22 Q22.
ta_kreg HS EE regs2 23%nat 23 Q23. ta_kreg HS EE regs2 25%nat 25 Q25. ta_kreg HS EE regs2 27%nat 27 Q27.
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x6b4: __asan_memset (p + 8, 0, 64), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 md1
    (k + 0) (F + 264) 0 64 (sp1 - sp0) (Z_to_bv 64 (BASE + 34572)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hs32, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists TICK_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
    + lia.
  - apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia].
  - apply (frame_ra_zero _ F (F + 264) 64 33 41); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms) md1 TICK_CID pos
      (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) Hin) as (_ & _ & _ & HFsh1).
    rewrite <- EF, ESH in HFsh1. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh1.
    apply (frame_hull_vis _ F 2048 (F + 264) 64); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8). apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ ta_Z1 F sp1 a -> ~ (F + 264 <= a < F + 328) ->
  ~ (sp1 - ESTACK <= a < sp1) -> aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn Hd He. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | intros Hd'; apply Hd; lia | lia]. }
assert (GAM : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
assert (KMM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 264 <= a < F + 328) -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W) memM a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha Hd He. apply HeffM; [exact Ha | intros Hd'; apply Hd; lia | lia]. }
assert (ZMM : forall a, F + 264 <= a < F + 328 -> aview segs (w_H W) memM a = Some 0).
{ intros a Ha. replace a with ((F + 264) + (a - (F + 264))) by lia. rewrite (HsetM (a - (F + 264)) ltac:(lia)). reflexivity. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARM.
(* the facts run 2 reads: the world, the registers, the saved t2 *)
assert (PTWM : tw_at TMAP_A (aview segs (w_H W) memM) (tick_ack_w1 Bw)).
{ apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms))); [exact PTW1|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KMM; [lia | intros Hd; apply (HFNI x ltac:(lia)); exact (HtwG x Hx) | lia]. }
assert (RM : forall n, acallee_saved n -> YK11.getr regsM (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
  by (intros n Hn; exact (HPM n Hn)).
assert (R26M : YK11.getr regsM 26 = w64 (F + 256)) by exact (eq_trans (RM 26 ltac:(hnf; lia)) Q26).
assert (R9M : YK11.getr regsM 9 = w64 sp1) by exact (eq_trans (RM 9 ltac:(hnf; lia)) (eq_trans Q9 R9)).
assert (R20M : YK11.getr regsM 20 = w64 TICK_S) by exact (eq_trans (RM 20 ltac:(hnf; lia)) Q20).
assert (R24M : YK11.getr regsM 24 = w64 SHADOW_OFF) by exact (eq_trans (RM 24 ltac:(hnf; lia)) Q24).
assert (M2 : YK11.getr regsM 2 = w64 sp1) by exact (eq_trans (RM 2 ltac:(hnf; lia)) Q2).
assert (M3 : YK11.getr regsM 3 = w64 (as_gp B)) by exact (eq_trans (RM 3 ltac:(hnf; lia)) Q3).
assert (M4 : YK11.getr regsM 4 = w64 (as_tp B)) by exact (eq_trans (RM 4 ltac:(hnf; lia)) Q4).
assert (MK : forall n, In n [8; 18; 19; 21; 22; 23; 25; 27] ->
  YK11.getr regsM (Z_to_bv 5 n) = YK11.getr regs2 (Z_to_bv 5 n)).
{ intros n Hn. cbn [In] in Hn.
  destruct Hn as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
  [exact (eq_trans (RM 8 ltac:(hnf; lia)) Q8) | exact (eq_trans (RM 18 ltac:(hnf; lia)) Q18) |
   exact (eq_trans (RM 19 ltac:(hnf; lia)) Q19) | exact (eq_trans (RM 21 ltac:(hnf; lia)) Q21) |
   exact (eq_trans (RM 22 ltac:(hnf; lia)) Q22) | exact (eq_trans (RM 23 ltac:(hnf; lia)) Q23) |
   exact (eq_trans (RM 25 ltac:(hnf; lia)) Q25) | exact (eq_trans (RM 27 ltac:(hnf; lia)) Q27)]. }
assert (ZSM : forall i, 32 <= i < 41 -> aview segs (w_H W) memM (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KMM; [exact (ZS1 i Hi) | unfold SHADOW_OFF in *; lia | destruct HSHF; lia | unfold SHADOW_OFF; lia]. }
assert (VT2M : val_mem segs (mrestrict (w_H W) memM) (sp1 + 24) 8 (bv_unsigned (YK11.getr regs2 7))).
{ apply (ta_vm_kept _ _ (ms_mem ms) memM _ 8 _ VT2). intros j Hj. apply KMM; [lia | lia | lia]. }
assert (VA7M : val_mem segs (mrestrict (w_H W) memM) (sp1 + 32) 8 (TICK_S + 18144)).
{ apply (ta_vm_kept _ _ (ms_mem ms) memM _ 8 _ VA7). intros j Hj. apply KMM; [lia | lia | lia]. }
(* +0x6b8 .. +0x71c: run 2, the notice's fields, up to `jalr a2` *)
change (Z_to_bv 64 (BASE + 34572)) with (Z_to_bv 64 (BASE + TA_C2)).
pose proof (ta_entry2 B lyc S2 W regsM memM mdM (tick_ack_w1 Bw) F sp1 (YK11.getr regs2 7) HTC HARM PTWM R26M R9M
  R20M R24M HF0 HF64 ltac:(lia) HFapp HFG Hs0 Hs1 Hs32 ltac:(lia) VT2M
  ltac:(intros a Ha; exact (GAM a (proj1 (HFb a ltac:(lia)))))) as HS2.
set (E2 := ta_E2 regsM (YK11.getr regs2 7) (tick_ack_w1 Bw)) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, ta_E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regsM r)
  by (intros n r0 Hn; unfold E2, ta_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U26 : bv_unsigned (ew E2 26) = F + 256)
  by (rewrite (EE2 26%nat 26%bv eq_refl), R26M; unfold w64; apply unsigned_lit_small; lia).
assert (U9b : bv_unsigned (ew E2 9) = sp1)
  by (rewrite (EE2 9%nat 9%bv eq_refl), R9M; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK2 : sh_ok segs TA_Bx (@nil shent) E2 (mrestrict (w_H W) memM)) by constructor.
clear dependent ms.
paj_run_tok RUN HS2 HJ2 SHOK2 TA_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U26 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia. }
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U26 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia. }
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 256 <= a < F + 264) -> ~ (F + 320 <= a < F + 326) ->
  aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memM a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 256 <= x < F + 264) \/ (F + 320 <= x < F + 326)) HFr);
    [| exact Ha | intros [X | X]; [exact (H1 X) | exact (H2 X)]].
  intros b wlo whi x Hiw Hx. cbv beta.
  ta_win Hiw Hx ltac:(rewrite ?U26, ?U9b in Hx; first [lia | left; lia | right; lia]). }
assert (GA2 : forall a, apresent (w_H W) memM a -> apresent (w_H W) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS2 eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RS1.
cbn [ms_mem restrict] in RS0, RS1.
set (cnt := TW.u_at (tick_ack_w1 Bw) (TW.OFF_g_s + 1744) 4) in *.
assert (Rcnt : 0 <= cnt < 2 ^ 32) by (unfold cnt; exact (TWL.u_at_range _ _ 4)).
assert (E32b : ew E2 32 = Z_to_bv 64 cnt)
  by (unfold E2, ta_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 0)).
assert (E33b : ew E2 33 = YK11.getr regs2 7)
  by (unfold E2, ta_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 1)).
assert (D21 : sv_denot E2 (SOff 21 0) = Z_to_bv 64 (TW.S_state Bw)).
{ cbn [sv_denot]. rewrite (EE2 21%nat (Z_to_bv 5 21) eq_refl).
  rewrite (eq_trans (MK 21 ltac:(cbn; tauto)) R21). unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D32 : sv_denot E2 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 cnt)).
{ cbn [sv_denot]. rewrite E32b. rewrite (unsigned_lit_small cnt) by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite (unsigned_lit_small cnt) by lia. reflexivity. }
assert (D33 : sv_denot E2 (SOff 33 0) = Z_to_bv 64 (bv_swrap 32 (TW.S_inflight_retries Bw))).
{ cbn [sv_denot]. rewrite E33b, R7. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (ta_chunk_val E2 (w_H W) (ms_mem ms2) _ _ _ _ _ _ 0 4 (SLit 5) RS0
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (ta_chunk_val E2 (w_H W) (ms_mem ms2) _ _ _ _ _ _ 4 4 (SOff 21 0) RS0
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP4.
pose proof (ta_chunk_val E2 (w_H W) (ms_mem ms2) _ _ _ _ _ _ 64 4 (SExt true 32 (SOff 32 0)) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP64.
pose proof (ta_chunk_val E2 (w_H W) (ms_mem ms2) _ _ _ _ _ _ 68 2 (SOff 33 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP68.
cbn [base_val] in VP0, VP4, VP64, VP68. rewrite U26 in VP0, VP4, VP64, VP68.
rewrite D21 in VP4. rewrite D32 in VP64. rewrite D33 in VP68.
change (bv_unsigned (sv_denot E2 (SLit 5)) mod 2 ^ (8 * Z.of_N 4)) with 5 in VP0.
change (N.to_nat 4) with 4%nat in VP0. rewrite Z.add_0_r in VP0.
apply (ta_vm_w _ _ 4 _ ltac:(lia)) in VP4. apply (ta_vm_w _ _ 4 _ ltac:(lia)) in VP64.
apply (ta_vm_w _ _ 2 _ ltac:(lia)) in VP68.
change (N.to_nat 4) with 4%nat in VP4, VP64. change (N.to_nat 2) with 2%nat in VP68.
apply (ta_vm_eqm _ _ 4 _ cnt (ta_swrap_mod cnt (8 * Z.of_nat 4) ltac:(cbn; lia))) in VP64.
apply (ta_vm_eqm _ _ 2 _ (DSpec.u16 (TW.S_inflight_retries Bw))) in VP68;
  [| rewrite (ta_swrap_mod _ (8 * Z.of_nat 2) ltac:(cbn; lia)); unfold DSpec.u16; cbn; rewrite Zmod_mod; reflexivity].
pose proof (ta_w1_facts Bw HLB) as (W1st & W1cnt & W1ret & W1nt & W1gf).
assert (HNB : garr8 segs (mrestrict (w_H W) (ms_mem ms2)) (F + 256)
  (map DSpec.bz (ta_ack_bytes (TW.S_state (tick_ack_w1 Bw)) (TW.S_inflight_counter (tick_ack_w1 Bw))
     (DSpec.u16 (TW.S_inflight_retries (tick_ack_w1 Bw)))))).
{ rewrite W1st, W1ret. change (TW.S_inflight_counter (tick_ack_w1 Bw)) with cnt.
  apply (ta_nb (w_H W) (ms_mem ms2) (F + 256)); [exact VP0 | exact VP4 | | exact VP64 | exact VP68 |].
  - intros a Ha. rewrite KR2 by lia. apply ZMM. lia.
  - intros a Ha. rewrite KR2 by lia. apply ZMM. lia. }
(* what the call kept, from its entry to the call of notice *)
set (Zs2 := fun x => ta_Z1 F sp1 x \/ (F + 256 <= x < F + 328) \/ (sp1 - ESTACK <= x < sp1)).
assert (KZ2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs2 a -> aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. unfold Zs2 in Hn. rewrite KR2 by (try lia; intros X; apply Hn; right; left; lia).
  apply KAM; [exact Ha | intros X; apply Hn; left; exact X | intros X; apply Hn; right; left; lia |
    intros X; apply Hn; right; right; exact X]. }
assert (GZ2 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms2) a)
  by (intros a Ha; exact (GA2 a (GAM a Ha))).
assert (HZ2 : forall a, Zs2 a ->
  (spZ regs - TICK_STK <= a < spZ regs) \/ dkg_nf TICK_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [[Hz | [Hz | [Hz | Hz]]] | [Hz | Hz]].
  - right; left; right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - left; lia.
  - right; right. apply (ta_row _ _ _ _ TMAP_A_g_s). unfold TICK_S, TA_g_s, TW.SZ_g_s in *. lia.
  - right; right. apply (ta_row _ _ _ _ TMAP_A_g_s). unfold TICK_S, TA_g_s, TW.SZ_g_s in *. lia.
  - right; left; left. change (fs_frame_bytes TICK_CID) with 2048. lia.
  - left; lia. }
assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms2) (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
    (ms_mem ms2) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw) Zs2 HGX HARc HAR2 Hfrs
    ltac:(intros bm Hbm; rewrite Hbl; exact Hbm) eq_refl EF eq_refl FFL ltac:(lia) ltac:(lia) HZ2 HK KZ2 GZ2). }
assert (GKN : gx_kept_ex segs TG.G_HARNESS (tick_wr Bw) W memc W (ms_mem ms2)).
{ intros a Ha Hn. rewrite <- (HGK a Ha).
  pose proof (inG_low segs B transport_segs_low _ a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
  apply KZ2; [lia|]. intros [[Hz | [Hz | [Hz | Hz]]] | [Hz | Hz]].
  - unfold SHADOW_OFF in Hz. lia.
  - lia.
  - apply Hn. left. unfold twa_fld, TW.A_S_inflight, TW.OFF_g_s, TICK_S in *. lia.
  - apply Hn. do 12 right; left. unfold twa_fld, TW.A_S_stats_ack_lost, TW.OFF_g_s, TICK_S in *. lia.
  - exact (HFNI a ltac:(lia) Ha).
  - lia. }
(* the registers at `jalr a2` *)
assert (E34 : ew E2 34 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ unfold E2, ta_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth].
  change (TW.u_at (tick_ack_w1 Bw) (TW.OFF_g_s + 96) 8) with (TW.S_notify (tick_ack_w1 Bw)).
  rewrite W1nt, HNT. reflexivity. }
ta_reg HS2 (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ta_reg HS2 (Z_to_bv 5 11) (w64 (F + 256)) T11 ltac:(cbn [sv_denot]; rewrite U26, Z.add_0_r; reflexivity).
ta_kreg HS2 EE2 regsM 2%nat 2 T2. ta_kreg HS2 EE2 regsM 3%nat 3 T3. ta_kreg HS2 EE2 regsM 4%nat 4 T4.
ta_kreg HS2 EE2 regsM 8%nat 8 T8. ta_kreg HS2 EE2 regsM 9%nat 9 T9. ta_kreg HS2 EE2 regsM 18%nat 18 T18.
ta_kreg HS2 EE2 regsM 19%nat 19 T19. ta_kreg HS2 EE2 regsM 21%nat 21 T21.
ta_reg HS2 (Z_to_bv 5 20) (w64 TICK_S) T20 ltac:(reflexivity).
ta_reg HS2 (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
ta_kreg HS2 EE2 regsM 22%nat 22 T22. ta_kreg HS2 EE2 regsM 23%nat 23 T23.
ta_kreg HS2 EE2 regsM 25%nat 25 T25. ta_kreg HS2 EE2 regsM 26%nat 26 T26. ta_kreg HS2 EE2 regsM 27%nat 27 T27.
(* +0x71c: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W E2 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI2 HS2 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms2) mdC) Qx) end.
assert (EBN : BASE + 34676 = 0x899d8) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + 34676))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r0 : bv 5, bv_unsigned r0 <> 1 -> YK11.getr regsC r0 = YK11.getr (ms_regs ms2) r0)
  by (intros r0 Hr; unfold regsC; apply YK11.getr_other; intros E; apply Hr; rewrite E; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1)
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T2 M2)).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T3 M3)).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T4 M4)).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 256)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (PTW2 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms2)) (tick_ack_w1 Bw)).
{ apply (tw_kept TMAP_A (aview segs (w_H W) memM)); [exact PTWM|].
  intros x Hx. apply KR2; [pose proof (TMAP_A_hull x Hx) as Hh; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh; lia | |];
    intros Hd; apply (HFNI x ltac:(lia)); exact (HtwG x Hx). }
assert (ZSN : forall i, 32 <= i < 41 -> aview segs (w_H W) (ms_mem ms2) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KR2; [exact (ZSM i Hi) | unfold SHADOW_OFF in *; lia | destruct HSHF; lia | destruct HSHF; lia]. }
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms2) mdC (k + 0) regsC
    (F + 256) (tick_ack_ntc Bw) TF (tick_ack_w1 Bw) B0
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite Hs32, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ta_ntc_at B lyc S2 W (ms_mem ms2) md3 regsC Bw F pos LAWS HARN Hin EF HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; unfold TICK_FBYTES; lia) ZSN HNB)
    (trans_tframe_at_top B LAWS HRU HRE lyc Sc W memc mdc S2 (ms_mem ms2) md3 regs regsC TF (tick_wr Bw) TICK_STK
       NOTICE_STK TICK_CID pos
       HARc HARN Hfrs Hbl HSTKLT KCN GKN Hapart (ta_wr_lo Bw) ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_LO in Gh; lia)
    PTW2 HNM
    (ta_apart B lyc S2 W mem2 md2 W (ms_mem ms2) TF Bw F pos LAWS HAR2 Hin EF Hapart)
    ltac:(intros HD; exfalso; unfold tick_ack_ntc in HD; cbn [TI.n_kind] in HD; cbv in HD; discriminate HD)
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
rewrite EF3 in HFsh3. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
  YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms2) (Z_to_bv 5 n))
  by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (CH 19 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
    (eq_trans T19 (eq_trans (MK 19 ltac:(cbn; tauto)) R19))).
assert (R3_9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1)
  by exact (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9M)).
(* what the call kept, from its entry to notice's return *)
destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 TICK_CID pos F FL HAR2 Hfrs Hbl EF eq_refl FFL)
  as (N1 & N2 & N3 & N4).
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms2) W3 mem3
    (spZ regs - TICK_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (tick_wr Bw)
    (notice_wr (tick_ack_w1 Bw) (tick_ack_ntc Bw)) (dkg_nf TICK_CID F FL)).
  - lia.
  - lia.
  - intros c p0. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. unfold tick_wr. do 15 right; left. exact Ha. }
(* the words run 3 loads back, at notice's return *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
rewrite USPC in K31.
assert (KN : forall a, sp1 + 40 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite K31 by lia. rewrite KR2 by lia. apply KAM; [lia | unfold ta_Z1, TICK_S, TA_g_s, SHADOW_OFF; lia | lia | lia]. }
assert (V32_3 : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 32) 8 (TICK_S + 18144)).
{ apply (ta_vm_kept _ _ memM mem3 _ 8 _ VA7M). intros j Hj. rewrite K31 by lia. apply KR2; lia. }
assert (V40_3 : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 40) 8 TA_SH212).
{ apply (ta_vm_kept _ _ mem2 mem3 _ 8 _ (val_mem_of_rdword segs _ _ _ _ Ht40)). intros j Hj. apply KN. lia. }
assert (V48_3 : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 48) 8 (TICK_S + 212)).
{ apply (ta_vm_kept _ _ mem2 mem3 _ 8 _ (val_mem_of_rdword segs _ _ _ _ Ht48)). intros j Hj. apply KN. lia. }
(* +0x720 .. +0x754: run 3, shadow bytes 32 .. 40 := 0xf8, a7 / t0 / t1 back, `j` to the tail cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + 34676)) with (Z_to_bv 64 (BASE + TA_C3)).
pose proof (ta_entry3 W3 regs3 mem3 F sp1 R3_19 R3_9 HF0 HF64 ltac:(lia) Hs0 Hs1 Hs32
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia)))) V32_3 V40_3 V48_3) as HS3.
set (E3 := ta_E3 regs3) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, ta_E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r0 Hn; unfold E3, ta_E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19c : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs TA_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 TA_B0 TICK_TAIL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 32 <= a < SHADOW_OFF + F / 8 + 41) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 32 <= x < SHADOW_OFF + F / 8 + 41) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. ta_win Hiw Hx ltac:(rewrite ?U19c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (dk_kept_nf_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc ly3 S3 W3 mem3 md4 (ms_mem ms4)
    (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw) HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL KC3).
  - intros a Ha Hn. apply KR4; [exact Ha|]. intros X. apply Hn. right; left.
    change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - exact GA4. }
pmkst HS3.
(* the registers at the tail cut *)
assert (E3x : forall j, (j < 3)%nat -> ew E3 (32 + j) =
    nth j [w64 (TICK_S + 18144); w64 TA_SH212; w64 (TICK_S + 212)] (Z_to_bv 64 0))
  by (intros j Hj; unfold E3, ta_E3; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (E3x 0%nat ltac:(lia)) as E3a. pose proof (E3x 1%nat ltac:(lia)) as E3b. pose proof (E3x 2%nat ltac:(lia)) as E3c.
cbn [Nat.add nth] in E3a, E3b, E3c.
ta_reg HS3 (Z_to_bv 5 17) (w64 (TICK_S + 18144)) F17
  ltac:(cbn [sv_denot]; rewrite E3a; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ta_reg HS3 (Z_to_bv 5 6) (w64 (SHADOW_OFF + (TICK_S + 212) / 8)) F6
  ltac:(cbn [sv_denot]; rewrite E3b, (proj1 ta_sh_eq); unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ta_reg HS3 (Z_to_bv 5 5) (w64 (TICK_S + 212)) F5
  ltac:(cbn [sv_denot]; rewrite E3c; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ta_kreg HS3 EE3 regs3 2%nat 2 F2. ta_kreg HS3 EE3 regs3 3%nat 3 F3. ta_kreg HS3 EE3 regs3 4%nat 4 F4.
ta_kreg HS3 EE3 regs3 8%nat 8 F8. ta_kreg HS3 EE3 regs3 9%nat 9 F9. ta_kreg HS3 EE3 regs3 18%nat 18 F18.
ta_kreg HS3 EE3 regs3 19%nat 19 F19. ta_kreg HS3 EE3 regs3 20%nat 20 F20. ta_kreg HS3 EE3 regs3 22%nat 22 F22.
ta_kreg HS3 EE3 regs3 23%nat 23 F23. ta_kreg HS3 EE3 regs3 24%nat 24 F24. ta_kreg HS3 EE3 regs3 25%nat 25 F25.
ta_kreg HS3 EE3 regs3 27%nat 27 F27.
assert (CK : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
  YK11.getr (ms_regs ms4) (Z_to_bv 5 n) = YK11.getr regs3 (Z_to_bv 5 n) ->
  YK11.getr (ms_regs ms4) (Z_to_bv 5 n) = YK11.getr (ms_regs ms2) (Z_to_bv 5 n))
  by (intros n Hn H1 Hf; rewrite Hf; exact (CH n Hn H1)).
(* the bytes the tail reads or the cuts carry: the saved words, the frame's last word, now *)
assert (KST : forall a, sp1 + 40 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF in *; lia). exact (KN a Ha). }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 TICK_CID pos (F + 2040 + i) Hin).
  - rewrite KR2 by lia. apply KAM; [lia | unfold ta_Z1, TICK_S, TA_g_s, SHADOW_OFF in *; destruct HSHF; destruct HFG as [Hg | Hg];
      unfold TW.SZ_g_s in Hg; lia | lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
  - intros Hw. apply (HFNI (F + 2040 + i) ltac:(lia)). apply (ta_wr_G Bw). do 15 right; left. exact Hw. }
assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold TICK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (TAIL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0 ly3 S3
  W3 (ms_mem ms4) md5 0 (ms_regs ms4) HFIX).
- split; [split; [split|] |].
  + replace (k + 0) with (k + 0 + 0) by lia. exact HJ3.
  + split; [unfold TICK_EV; lia|].
    split; [exact Hfrs3|].
    split; [rewrite <- Hbl; exact Hperm3|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KST. lia.
    * unfold TICK_FBYTES. change (flag_addr lyc TICK_CID pos) with FL. rewrite <- HFLw. replace (F + 2048 - 8) with (F + 2040) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + rewrite <- Hnoww. apply rdword_ext. intros i Hi. apply KST. lia.
  + split; [|split; [|split]].
    * apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KR4; [lia | unfold SHADOW_OFF; lia].
    * unfold B0. rewrite (ta_gfn_b0 Bw HLB). exact Hgf.
    * exact HTT.
    * intros _. unfold B0. exact (ta_runinv_b0 Bw HLB Hinv).
- unfold tick_regs_tail, tick_regs_run, tick_regs_base.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) (conj _ (conj _ (conj _ (conj _ (conj _ _))))))
    (conj F5 (conj F6 F17))).
  + exact (eq_trans (CK 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F2) (eq_trans T2 M2)).
  + exact (eq_trans (CK 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F3) (eq_trans T3 (eq_trans M3 (eq_sym Hgp)))).
  + exact (eq_trans (CK 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F4) (eq_trans T4 (eq_trans M4 (eq_sym Htp)))).
  + exact (eq_trans (CK 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F8) (eq_trans T8 (eq_trans (MK 8 ltac:(cbn; tauto)) R8))).
  + exact (eq_trans (CK 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F9) (eq_trans T9 R9M)).
  + exact (eq_trans (CK 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F18) (eq_trans T18 (eq_trans (MK 18 ltac:(cbn; tauto)) R18))).
  + exact (eq_trans (CK 27 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F27) (eq_trans T27 (eq_trans (MK 27 ltac:(cbn; tauto)) R27))).
  + exact (eq_trans (CK 19 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F19) (eq_trans T19 (eq_trans (MK 19 ltac:(cbn; tauto)) R19))).
  + exact (eq_trans (CK 20 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F20) T20).
  + exact (eq_trans (CK 22 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F22) (eq_trans T22 (eq_trans (MK 22 ltac:(cbn; tauto)) R22))).
  + exact (eq_trans (CK 23 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F23) (eq_trans T23 (eq_trans (MK 23 ltac:(cbn; tauto)) R23))).
  + exact (eq_trans (CK 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F24) T24).
  + exact (eq_trans (CK 25 ltac:(hnf; lia) ltac:(vm_compute; discriminate) F25) (eq_trans T25 (eq_trans (MK 25 ltac:(cbn; tauto)) R25))).
Qed.

End ta.

(* The ack-lost piece of the walk of diginet_session_tick (TickCut.v tick_ackl_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_ackl : forall fx rc B MT, @tick_ackl_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ta_holds fx rc B MT). Qed.

Print Assumptions tick_ackl.
