(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names and numbers changed; 141 of its 212 lines of code are new or changed and 694 lines of the source are left out. *)
(* TickQueue_f8: the last segment of the queue piece of diginet_session_tick's image-A walk, tq_f8 : tick_epi_at ->
   tq_f8_at (TickQueue_kit.v), code +0x9fc .. +0xa08 (0x89cb4 .. 0x89cc0): a1 = 186, a0 = s6 (the body's shadow address),
   `jal __asan_set_shadow_f8` (+0xa04; the bundle's aset_shadow_realizes .. 0xf8 through TransportGRt.v
   gx_set_shadow_at: the body's 186 shadow bytes, bytes of the walk's own frame's shadow, stored 0xf8, every other byte
   kept), then `j` (+0xa08) to the epilogue cut tick_epi_at. Both runs are from a state with no region (TickQueue_kit.v
   tq_entry_nr); tick_cur is carried over the fill by TickQueue_kit.v tq_cur_step. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut TickQueue_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section f8. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma tq_f8_holds : @tick_epi_at fx rc B MT -> @tq_f8_at fx rc B MT.
Proof.
unfold tq_f8_at. intros EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS R22.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof CALLEES as (CF8 & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HC & Htw' & Hgf').
pose proof HC as (HJ1 & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (tq_fix_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX)
  as (Hce0 & Hwin0 & Hspz & H47 & Hsp0a & Hsp1 & Hsp1a & HTS & HSDE & HSDT & HES).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
unfold TICK_FBYTES in HFc, HFapp, HFL.
assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite DFm8, Z.add_0_r in D8.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* +0x9fc .. +0xa04: a1 = 186, a0 = s6, `jal __asan_set_shadow_f8` *)
pose proof (tq_entry_nr TQ_F8 W2 regs2 mem2) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ1 SHOK TQ_B0.
{ tq_awr_rs. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by exact (tq_nr_kept _ (w_H W2) mem2 (ms_mem ms) HFr).
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
tq_reg HS (Z_to_bv 5 10) (w64 (SHADOW_OFF + F / 8 + 48)) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
tq_reg HS (Z_to_bv 5 11) (w64 186) Q11 ltac:(reflexivity).
tq_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 35420)) Q1 ltac:(apply codeptr_val; exact HEI).
tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2.
tq_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
tq_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8. tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9.
tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18. tq_kreg HS EE (Z_to_bv 5 26) 26%nat R26 Q26.
tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27.
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0xa04: __asan_set_shadow_f8 (s6, 186), through the G journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_f8)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (gx_set_shadow_at (SK := tfib_sink_head) segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_f8) 0xf8 (CF8 fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S
    W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 md1 (k + e) TICK_CID pos (SHADOW_OFF + F / 8 + 48) 186 (sp1 - sp0)
    (Z_to_bv 64 (BASE + 35420)) HJ1 (or_introl eq_refl) Q10 Q11).
  - lia.
  - rewrite EF2. unfold shadow_addr. lia.
  - rewrite EF2. unfold shadow_addr. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp1a, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hset3 & Hkeep3 & Hgr3).
(* tick_cur and the world relation at mem3: only the body's shadow bytes changed *)
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 48 <= a < SHADOW_OFF + F / 8 + 48 + 186) ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (Hkeep3 a Ha Hn); exact (KR1 a Ha)).
assert (GZ : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) by (intros a Ha; exact (Hgr3 a (GA1 a Ha))).
assert (HC3 : tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem3 md3 e).
{ apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2 mem3 md3
    e (fun a => SHADOW_OFF + F / 8 + 48 <= a < SHADOW_OFF + F / 8 + 48 + 186) LAWS HGX FFL HARc ltac:(lia) ltac:(lia)
    HC HJ3 EF); [| exact KZ | exact GZ].
  intros a Ha. right. left. split.
  - unfold dkg_nf. right. left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - unfold TICK_FBYTES, SHADOW_OFF in *. destruct HSHF; lia. }
assert (Htw3 : tw_at TMAP_A (aview segs (w_H W2) mem3) Bw').
{ apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw'|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KZ; [lia | unfold SHADOW_OFF; lia]. }
(* the registers set_shadow_f8 keeps *)
assert (P2 : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
assert (P3 : YK11.getr regs3 (Z_to_bv 5 3) = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
assert (P4 : YK11.getr regs3 (Z_to_bv 5 4) = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
assert (P8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
assert (P9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
assert (P18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
assert (P26 : YK11.getr regs3 (Z_to_bv 5 26) = w64 r) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) Q26).
assert (P27 : YK11.getr regs3 (Z_to_bv 5 27) = w64 F) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) Q27).
clear dependent ms.
(* 0x89cc0: `j` to the epilogue cut *)
pose proof (tq_entry_nr TQ_RF8 W2 regs3 mem3) as HS.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r0 Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W2) mem3)) by constructor.
change (Z_to_bv 64 (BASE + 35420)) with (Z_to_bv 64 (BASE + TQ_RF8)).
paj_run_to_tok RUNTO HS HJ3 SHOK3 TQ_B0 TICK_EPI.
{ tq_awr_rs. apply awr_ok_x_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem3 a)
  by exact (tq_nr_kept _ (w_H W2) mem3 (ms_mem ms) HFr).
assert (GA4 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
tq_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 26) (YK11.getr regs3 (Z_to_bv 5 26)) F26
  ltac:(cbn [sv_denot]; rewrite (EE3 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) F27
  ltac:(cbn [sv_denot]; rewrite (EE3 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pmkst HS.
apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly2 S2 W2
  (ms_mem ms) md4 e (ms_regs ms) HFIX).
- split; [|split].
  + apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem3 md3
      (ms_mem ms) md4 e (fun _ => False) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC3 HJ3 EF); [intros a [] | | exact GA4].
    intros a Ha _. exact (KR4 a Ha).
  + apply (tw_kept TMAP_A (aview segs (w_H W2) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4. lia.
  + exact Hgf'.
- refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) _).
  + exact (eq_trans F2 P2).
  + exact (eq_trans F3 (eq_trans P3 (eq_sym Hgp))).
  + exact (eq_trans F4 (eq_trans P4 (eq_sym Htp))).
  + exact (eq_trans F8 P8).
  + exact (eq_trans F9 P9).
  + exact (eq_trans F18 P18).
  + exact (eq_trans F27 P27).
  + exact (eq_trans F26 P26).
Qed.
End f8.
