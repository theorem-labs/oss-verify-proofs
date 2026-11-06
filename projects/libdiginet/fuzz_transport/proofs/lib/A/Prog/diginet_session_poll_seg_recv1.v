(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 524 of its 583 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_poll_seg_rel.v; 424 of its 494 lines of code are new or changed and 513 lines of the source are left out. *)
(* diginet_session_poll_seg_recv1: Theorem pw_recv1_piece : pw_recv1_stmt (lib/A/Prog/diginet_session_poll_segs.v),
   the first-recv piece: from the cut recv1 (+0x234, 0x8afbc): `jalr a4` (io_recv,
   diginet_session_poll_seg_grecv.v pw_recv_call); a negative result to the cut rel with s10 = r1; else the checks of
   s + 88 (through the slot s1 + 24) and s + 64, `jalr a1` (+0x25c; io_now, diginet_session_poll_seg_leaf.v
   pw_now_call); r1 = 0 to the cut tick; else `jal diginet_session_rx` (+0x278; diginet_session_poll_seg_grx.v
   pw_rx_call) and `mv a3, s10`, to the cut tick. Premise (3) of the rx call and the drain's from kit pw_rx_first
   (poll_rx_each at the entry's world, whose recv pointer is the image's io_recv). The symbolic state, the no-store
   runs and the register and buffer carry are diginet_session_poll_seg_loop.v's (pw_entry, pw_run_kept,
   pw_garr_move, pw_rg_buf_pres, pw_rg_buf_call). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg notice_cg io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_poll_seg_rt diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_loop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma pw_recv1_holds : @pw_recv1_stmt fx rc B MT.
Proof.
unfold pw_recv1_stmt. intros c REL TICK RT KEEP OK pos ly2 S2 W2 mem2 md2 regs2 B1 r1 got HRUN HRG R11 R12 R14
  HIORECV HM1 HREST.
pose proof RT as (HSM & HCELLS & HSC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE &
  ASM & ASF8 & ASF0 & LIN & LSD & HRECVC & HRXC & HTICKC & HFREE).
pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRX & _).
pose proof (pw_ok_sp B MT c OK) as (HARc & HSPR & HCEIL & HPRES & HM32 & HSP1R & HSP0M & HSTKLE & HSPLE & HSTKEQ &
  HESIO & HIOSRX & HTKSRX).
pose proof (pw_recv_ret timg_A (cx_TF c) (cx_Bw c) B1 r1 got HM1) as (HR1R & HR1LEN).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
assert (EIOR : TI.ti_io_recv timg_A = 0x834c4) by reflexivity.
assert (EION : TI.ti_io_now timg_A = 0x8356c) by reflexivity.
pose proof HRG as (HRGR & HRG25).
pose proof HRGR as ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27).
(* +0x234: `jalr a4` = io_recv at the entry's world *)
pose proof (pw_entry B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) regs2 PW_RECV1 RT OK HRUN HRGR) as HS.
set (E0 := pw_E regs2 (cx_Bw c)) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply pw_env_img).
assert (EPC : PW_RECV1 = 40280) by reflexivity.
change (SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PW_RECV1)) mem2 (YK11.seg_rom segs)) md2)
  (pw_post B MT c)).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E0 _ _ _ _ 0x700e7 (1%bv : bv 5)
  (14%bv : bv 5) (TI.ti_io_recv timg_A) HEI HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | unfold PW_SS; cbn [ss_pc]; rewrite EPC; lia | exact R14
  | rewrite EIOR; lia | rewrite EIOR; reflexivity |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_recv timg_A) regsC mm mdC) Qx) end.
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (PW_RECV1 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq;
      discriminate Hq); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr regs2 r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
assert (EBN : BASE + (PW_RECV1 + 4) = 0x8afc0) by (vm_compute; reflexivity).
assert (HJC : ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
    (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 mdC (cx_k c))
  by (unfold mdC; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact (proj1 (proj1 HRUN))).
assert (HRUNC : pw_run B MT c pos ly2 S2 W2 mem2 mdC (cx_Bw c))
  by (apply (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw c) mem2 mdC RT OK HRUN HJC);
      [intros a _ _; reflexivity | intros a Ha; exact Ha]).
eapply SRr_bind.
{ exact (pw_recv_call B MT c pos ly2 S2 W2 mem2 mdC (cx_Bw c) regsC B1 r1 got RT KEEP OK HRUNC
    ltac:(rewrite (RCK 2%bv ltac:(vm_compute; discriminate)); exact R2)
    ltac:(rewrite (RCK 3%bv ltac:(vm_compute; discriminate)); exact R3)
    ltac:(rewrite (RCK 4%bv ltac:(vm_compute; discriminate)); exact R4)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [rewrite EPC; lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN, unsigned_lit_small by lia; lia)
    ltac:(rewrite (RCK 11%bv ltac:(vm_compute; discriminate)); exact R11)
    ltac:(rewrite (RCK 12%bv ltac:(vm_compute; discriminate)); exact R12)
    HM1). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HP3 & HA03 & HX3 & HRUN3).
rewrite RC1.
assert (HRG3 : pw_rg_buf B c pos regs3)
  by exact (pw_rg_buf_pres B c pos regsC regs3 (pw_rg_buf_call B c pos regs2 regsC HRG RCK) HP3).
pose proof (proj1 (proj1 HRUN3)) as HJ3.
clear RC1 RCK HJC HRUNC HP3 regsC mdC.
(* +0x238 .. +0x23c: s10 = r1, up to `bltz a0` *)
pose proof HRG3 as (((P2 & P3 & P4 & P8 & P9 & P18) & P19 & P20 & P21 & P22 & P23 & P24 & P27) & P25).
pose proof (pw_entry B MT c pos ly3 S3 W3 mem3 md3 B1 regs3 (PW_RECV1 + 4) RT OK HRUN3 (proj1 HRG3)) as HS2.
set (E1 := pw_E regs3 B1) in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; apply pw_env_img).
assert (SHOK2 : sh_ok segs PW_Bx (@nil shent) E1 (mrestrict (w_H W3) mem3)) by constructor.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E1; apply pw_ew_reg; exact Hn).
assert (D10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 r1)
  by (cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
paj_run_tok RUN HS2 HJ3 SHOK2 PW_B0.
{ pw_awr. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
assert (KD4 : forall a, aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a)
  by (intros a; exact (pw_run_kept E1 (w_H W3) mem3 (ms_mem ms) HFr a)).
assert (HRUN4 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1)
  by (apply (pw_run_win B MT c pos ly3 S3 W3 mem3 md3 B1 (ms_mem ms) md4 RT OK HRUN3 HJ3);
      [intros a _ _; exact (KD4 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
assert (HX4 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
    garr8 segs (mrestrict (w_H W3) (ms_mem ms)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
{ destruct HX3 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
  apply (pw_garr_move (w_H W3) mem3 (ms_mem ms)); [exact HXG | intros x _; exact (KD4 x)]. }
assert (HBR : branch_taken BC_LT (sv_denot E1 (SOff 10 0)) (sv_denot E1 (SLit 0)) = (r1 <? 0)).
{ cbn [branch_taken]. rewrite D10. change (sv_denot E1 (SLit 0)) with (Z_to_bv 64 0).
  exact (pw_lts r1 0 ltac:(lia) ltac:(lia)). }
psrr_branch_tok RUN BR HS2 SHOK2 PW_B0.
- (* r1 < 0: the negative result returned with io_recv's world (:517-518), to the release cut *)
  rewrite HBR in Hc. apply Z.ltb_lt in Hc.
  destruct HREST as [(Hneg & EBw & Er) | (Hpos & _)]; [| lia].
  paj_run_to_tok RUNTO HS2 HJ3 SHOK2 PW_B0 PW_REL.
  { pw_awr. }
  set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
  assert (KD5 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
    by (intros a; exact (pw_run_kept E1 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
  assert (HRUN5 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md5 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1 (ms_mem ms0) md5 RT OK HRUN4 HJ3);
        [intros a _ _; exact (KD5 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
  pw_reg HS2 (Z_to_bv 5 2) (w64 (pw_sp1 c)) F2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P2).
  pw_reg HS2 (Z_to_bv 5 3) (w64 (as_gp B)) F3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P3).
  pw_reg HS2 (Z_to_bv 5 4) (w64 (as_tp B)) F4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P4).
  pw_reg HS2 (Z_to_bv 5 8) (w64 (pw_SP c)) F8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P8).
  pw_reg HS2 (Z_to_bv 5 9) (w64 (pw_sp1 c)) F9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P9).
  pw_reg HS2 (Z_to_bv 5 18) (w64 (pw_F c pos)) F18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P18).
  pw_reg HS2 (Z_to_bv 5 26) (w64 r1) F26
    ltac:(cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS2.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx segs (BASE + PW_REL) rg mm mdx) Q) end.
  apply (REL RT OK pos ly3 S3 W3 (ms_mem ms0) md5 (ms_regs ms0)).
  + rewrite EBw. exact (proj1 HRUN5).
  + repeat apply conj; [exact F2 | exact F3 | exact F4 | exact F8 | exact F9 | exact F18].
  + rewrite Er. exact F26.
- (* 0 <= r1: the checks of s + 88 and s + 64, `jalr a1` = io_now (:519) *)
  rewrite HBR in Hc. apply Z.ltb_ge in Hc.
  destruct HREST as [(Hneg & _) | (_ & now2 & B2 & B3 & r3 & HCN & HRX & HTK & HDR)]; [lia |].
  destruct (TPL.call_now_inv timg_A B1 now2 HCN) as (HNOW1 & Enow2).
  destruct (pw_rx_first timg_A (cx_TF c) (poll_dn_in (cx_TF c)) (cx_Bw c) B1 r1 got HPRX HIORECV HM1 Hc)
    as (HDN & HDRXF).
  pose proof (HDRXF now2 B2 B3 r3 HCN
    ltac:(destruct HRX as [(E0r & EB2) | (Hp & r2 & HRXM)];
          [subst r1; exact EB2 | rewrite (proj2 (Z.ltb_lt 0 r1) Hp); exists r2; exact HRXM])
    HTK) as HDRX3.
  clear HDRXF.
  paj_run_tok RUN HS2 HJ3 SHOK2 PW_B0.
  { pw_awr. }
  set (md6 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md6. clear mat.
  assert (KD6 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
    by (intros a; exact (pw_run_kept E1 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
  assert (HRUN6 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1 (ms_mem ms0) md6 RT OK HRUN4 HJ3);
        [intros a _ _; exact (KD6 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
  assert (HX6 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) (ms_mem ms0)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX4 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    apply (pw_garr_move (w_H W3) (ms_mem ms) (ms_mem ms0)); [exact HXG | intros x _; exact (KD6 x)]. }
  assert (EV34 : ew E1 34 = Z_to_bv 64 (TI.ti_io_now timg_A))
    by (unfold E1; rewrite pw_ew_now, <- pw_fld_now, HNOW1; reflexivity).
  pw_reg HS2 (Z_to_bv 5 2) (w64 (pw_sp1 c)) N2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P2).
  pw_reg HS2 (Z_to_bv 5 3) (w64 (as_gp B)) N3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P3).
  pw_reg HS2 (Z_to_bv 5 4) (w64 (as_tp B)) N4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P4).
  pw_reg HS2 (Z_to_bv 5 8) (w64 (pw_SP c)) N8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P8).
  pw_reg HS2 (Z_to_bv 5 9) (w64 (pw_sp1 c)) N9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P9).
  pw_reg HS2 (Z_to_bv 5 18) (w64 (pw_F c pos)) N18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P18).
  pw_reg HS2 (Z_to_bv 5 19) (w64 POLL_S) N19 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) N20
    ltac:(cbn [sv_denot]; rewrite (EE1 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P20).
  pw_reg HS2 (Z_to_bv 5 21) (w64 PW_SH64) N21 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 22) (w64 (POLL_S + 80)) N22 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 23) (w64 (POLL_S + 88)) N23 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 24) (w64 (POLL_S + 64)) N24 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) N25
    ltac:(cbn [sv_denot]; rewrite (EE1 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P25).
  pw_reg HS2 (Z_to_bv 5 26) (w64 r1) N26
    ltac:(cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pw_reg HS2 (Z_to_bv 5 27) (w64 PW_SH80) N27 ltac:(reflexivity).
  pw_reg HS2 (Z_to_bv 5 11) (Z_to_bv 64 (TI.ti_io_now timg_A)) N11
    ltac:(cbn [sv_denot]; rewrite EV34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HRGms0 : pw_rg_buf B c pos (ms_regs ms0)).
  { unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
      [ exact N2 | exact N3 | exact N4 | exact N8 | exact N9 | exact N18 | exact N19 | exact N20 | exact N21
      | exact N22 | exact N23 | exact N24 | exact N27 | exact N25 ]. }
  eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W3 E1 _ _ _ _ 0x580e7 (1%bv : bv 5)
    (11%bv : bv 5) (TI.ti_io_now timg_A) HEI1 HS2 eq_refl);
    [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact N11
    | rewrite EION; lia | rewrite EION; reflexivity |].
  intros matN msN EmsN _. subst msN.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    set (regsN := rg); set (mdN := mdx);
    change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_now timg_A) regsN mm mdN) Qx) end.
  assert (RN1 : YK11.getr regsN 1%bv = Z_to_bv 64 (BASE + (40320 + 4)))
    by (unfold regsN; rewrite YK11.getr_same by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq;
        discriminate Hq); reflexivity).
  assert (RNK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsN r = YK11.getr (ms_regs ms0) r)
    by (intros r Hr; unfold regsN; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
  assert (EBN2 : BASE + (40320 + 4) = 0x8afe8) by (vm_compute; reflexivity).
  assert (HJN : ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
      (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly3 S3 W3 (ms_mem ms0) mdN (cx_k c))
    by (unfold mdN; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ3).
  assert (HRUNN : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) mdN B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1 (ms_mem ms0) mdN RT OK HRUN6 HJN);
        [intros a _ _; reflexivity | intros a Ha; exact Ha]).
  eapply SRr_bind.
  { exact (pw_now_call B MT c pos ly3 S3 W3 (ms_mem ms0) mdN B1 regsN RT OK HRUNN
      ltac:(rewrite (RNK 2%bv ltac:(vm_compute; discriminate)); exact N2)
      ltac:(rewrite (RNK 3%bv ltac:(vm_compute; discriminate)); exact N3)
      ltac:(rewrite (RNK 4%bv ltac:(vm_compute; discriminate)); exact N4)
      ltac:(rewrite RN1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
      ltac:(unfold raZ; rewrite RN1, EBN2, unsigned_lit_small by lia; lia)). }
  cbv beta. intros W4 c4 _ (EW4 & regs4 & mem4 & md7 & -> & HP4 & HA04 & HRUN7 & HKEEP4 & HGR4).
  subst W4.
  rewrite RN1.
  change (Z_to_bv 64 (BASE + (40320 + 4))) with (Z_to_bv 64 (BASE + (PW_RECV1 + 0x2c))).
  assert (HRG4 : pw_rg_buf B c pos regs4)
    by exact (pw_rg_buf_pres B c pos regsN regs4 (pw_rg_buf_call B c pos (ms_regs ms0) regsN HRGms0 RNK) HP4).
  assert (N26' : YK11.getr regs4 26 = w64 r1)
    by exact (eq_trans (HP4 26 ltac:(hnf; lia)) (eq_trans (RNK 26%bv ltac:(vm_compute; discriminate)) N26)).
  assert (HX7 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) mem4) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX6 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    pose proof (pw_cur_frame B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1 RT OK (proj1 HRUN6))
      as (_ & _ & _ & _ & _ & _ & HF4096 & _ & HFceil & _).
    unfold POLL_FBYTES in HFceil.
    assert (HLEN : Z.of_nat (length (TW.zs X)) = TS0.DIGINET_MAX_FRAME_LEN)
      by (unfold TW.zs; rewrite length_map, HXL, Z2Nat.id by (cbv; discriminate); reflexivity).
    assert (HCAP : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity.
    apply (pw_garr_move (w_H W3) (ms_mem ms0) mem4); [exact HXG |].
    intros x Hx. rewrite HLEN, HCAP in Hx.
    assert (H47 : 2 ^ 47 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    assert (HLE : pw_F c pos + 1546 <= pw_sp1 c - ESTACK) by lia.
    assert (HES : ESTACK = 4096) by reflexivity.
    apply HKEEP4; lia. }
  (* +0x260 .. +0x264: a3 = now2, up to `beqz s10` *)
  pose proof (proj1 (proj1 HRUN7)) as HJ7.
  clear dependent ms0. clear dependent ms.
  pose proof HRG4 as (((M2 & M3 & M4 & M8 & M9 & M18) & M19 & M20 & M21 & M22 & M23 & M24 & M27) & M25).
  pose proof (pw_entry B MT c pos ly3 S3 W3 mem4 md7 B1 regs4 (PW_RECV1 + 0x2c) RT OK HRUN7 (proj1 HRG4)) as HS4.
  set (E2 := pw_E regs4 B1) in HS4.
  assert (HEIR : img_env VAL A_LIM E2) by (unfold E2; apply pw_env_img).
  assert (SHOK4 : sh_ok segs PW_Bx (@nil shent) E2 (mrestrict (w_H W3) mem4)) by constructor.
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs4 r)
    by (intros n r Hn; unfold E2; apply pw_ew_reg; exact Hn).
  paj_run_tok RUN HS4 HJ7 SHOK4 PW_B0.
  { pw_awr. }
  set (md8 := with_vm_backing (m_vm_lazy md7) mat md7) in *. clearbody md8. clear mat.
  assert (KD8 : forall a, aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem4 a)
    by (intros a; exact (pw_run_kept E2 (w_H W3) mem4 (ms_mem ms) HFr a)).
  assert (HRUN8 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms) md8 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 mem4 md7 B1 (ms_mem ms) md8 RT OK HRUN7 HJ7);
        [intros a _ _; exact (KD8 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
  assert (HX8 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) (ms_mem ms)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX7 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    apply (pw_garr_move (w_H W3) mem4 (ms_mem ms)); [exact HXG | intros x _; exact (KD8 x)]. }
  assert (D26 : sv_denot E2 (SOff 26 0) = Z_to_bv 64 r1)
    by (cbn [sv_denot]; rewrite (EE2 26%nat 26%bv eq_refl), N26', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HBR2 : branch_taken BC_EQ (sv_denot E2 (SOff 26 0)) (sv_denot E2 (SLit 0)) = (r1 =? 0)).
  { cbn [branch_taken]. rewrite D26. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0).
    exact (pw_eqb r1 0 ltac:(lia) ltac:(lia)). }
  assert (HNR : 0 <= TC.io_now_m B1 < 2 ^ 64) by exact (pw_now_range B1).
  psrr_branch_tok RUN BR HS4 SHOK4 PW_B0.
  + (* r1 = 0: no frame, to the cut tick at io_recv's world (:520) *)
    rewrite HBR2 in Hc0. apply Z.eqb_eq in Hc0. subst r1.
    destruct HRX as [(_ & EB2) | (Hp & _)]; [| lia]. subst B2.
    paj_run_to_tok RUNTO HS4 HJ7 SHOK4 PW_B0 PW_TICK.
    { pw_awr. }
    set (md9 := with_vm_backing (m_vm_lazy md8) mat md8) in *. clearbody md9. clear mat.
    assert (KD9 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
      by (intros a; exact (pw_run_kept E2 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
    assert (HRUN9 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md9 B1)
      by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md8 B1 (ms_mem ms0) md9 RT OK HRUN8 HJ7);
          [intros a _ _; exact (KD9 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
    pw_reg HS4 (Z_to_bv 5 2) (w64 (pw_sp1 c)) T2
      ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M2).
    pw_reg HS4 (Z_to_bv 5 3) (w64 (as_gp B)) T3
      ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M3).
    pw_reg HS4 (Z_to_bv 5 4) (w64 (as_tp B)) T4
      ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M4).
    pw_reg HS4 (Z_to_bv 5 8) (w64 (pw_SP c)) T8
      ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M8).
    pw_reg HS4 (Z_to_bv 5 9) (w64 (pw_sp1 c)) T9
      ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M9).
    pw_reg HS4 (Z_to_bv 5 18) (w64 (pw_F c pos)) T18
      ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M18).
    pw_reg HS4 (Z_to_bv 5 19) (w64 POLL_S) T19 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) T20
      ltac:(cbn [sv_denot]; rewrite (EE2 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M20).
    pw_reg HS4 (Z_to_bv 5 21) (w64 PW_SH64) T21 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 22) (w64 (POLL_S + 80)) T22 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 23) (w64 (POLL_S + 88)) T23 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 24) (w64 (POLL_S + 64)) T24 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) T25
      ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M25).
    pw_reg HS4 (Z_to_bv 5 27) (w64 PW_SH80) T27 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 13) (w64 now2) T13
      ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, Enow2; exact HA04).
    pmkst HS4.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (@cfg_at fx segs (BASE + PW_TICK) rg mm mdx) Qx) end.
    apply (TICK RT KEEP OK pos ly3 S3 W3 (ms_mem ms0) md9 (ms_regs ms0) B1 now2 B3 r3 HRUN9).
    * unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
        [ exact T2 | exact T3 | exact T4 | exact T8 | exact T9 | exact T18 | exact T19 | exact T20 | exact T21
        | exact T22 | exact T23 | exact T24 | exact T27 | exact T25 ].
    * exact T13.
    * rewrite Enow2. exact HNR.
    * exact HTK.
    * exact HDR.
    * exact HDRX3.
  + (* 0 < r1: diginet_session_rx at io_recv's world with the bytes it handed over (:521) *)
    rewrite HBR2 in Hc0. apply Z.eqb_neq in Hc0.
    assert (Hp : 0 < r1) by lia.
    destruct HRX as [(Er0 & _) | (_ & r2 & HRXM)]; [lia |].
    destruct (HR1LEN Hp) as (HGOTL & HR1CAP).
    paj_run_tok RUN HS4 HJ7 SHOK4 PW_B0.
    { pw_awr. }
    set (md9 := with_vm_backing (m_vm_lazy md8) mat md8) in *. clearbody md9. clear mat.
    assert (KD9 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
      by (intros a; exact (pw_run_kept E2 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
    assert (HRUN9 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md9 B1)
      by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md8 B1 (ms_mem ms0) md9 RT OK HRUN8 HJ7);
          [intros a _ _; exact (KD9 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
    assert (HX9 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
        garr8 segs (mrestrict (w_H W3) (ms_mem ms0)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
    { destruct HX8 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
      apply (pw_garr_move (w_H W3) (ms_mem ms) (ms_mem ms0)); [exact HXG | intros x _; exact (KD9 x)]. }
    pw_reg HS4 (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 40352)) S1 ltac:(apply codeptr_val; exact HEIR).
    pw_reg HS4 (Z_to_bv 5 2) (w64 (pw_sp1 c)) S2r
      ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M2).
    pw_reg HS4 (Z_to_bv 5 3) (w64 (as_gp B)) S3r
      ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M3).
    pw_reg HS4 (Z_to_bv 5 4) (w64 (as_tp B)) S4r
      ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M4).
    pw_reg HS4 (Z_to_bv 5 10) (w64 POLL_S) S10 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 11) (w64 (pw_F c pos + 32)) S11
      ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M25).
    pw_reg HS4 (Z_to_bv 5 12) (w64 (Z.of_nat (length got))) S12
      ltac:(cbn [sv_denot]; rewrite (EE2 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, N26', HGOTL;
            reflexivity).
    pw_reg HS4 (Z_to_bv 5 13) (w64 now2) S13
      ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, Enow2; exact HA04).
    pw_reg HS4 (Z_to_bv 5 8) (w64 (pw_SP c)) S8
      ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M8).
    pw_reg HS4 (Z_to_bv 5 9) (w64 (pw_sp1 c)) S9
      ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M9).
    pw_reg HS4 (Z_to_bv 5 18) (w64 (pw_F c pos)) S18
      ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M18).
    pw_reg HS4 (Z_to_bv 5 19) (w64 POLL_S) S19 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) S20
      ltac:(cbn [sv_denot]; rewrite (EE2 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M20).
    pw_reg HS4 (Z_to_bv 5 21) (w64 PW_SH64) S21 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 22) (w64 (POLL_S + 80)) S22 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 23) (w64 (POLL_S + 88)) S23 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 24) (w64 (POLL_S + 64)) S24 ltac:(reflexivity).
    pw_reg HS4 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) S25
      ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M25).
    pw_reg HS4 (Z_to_bv 5 26) (w64 now2) S26
      ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, Enow2; exact HA04).
    pw_reg HS4 (Z_to_bv 5 27) (w64 PW_SH80) S27 ltac:(reflexivity).
    assert (HRGms0 : pw_rg_buf B c pos (ms_regs ms0)).
    { unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
        [ exact S2r | exact S3r | exact S4r | exact S8 | exact S9 | exact S18 | exact S19 | exact S20 | exact S21
        | exact S22 | exact S23 | exact S24 | exact S27 | exact S25 ]. }
    assert (EBN3 : BASE + 40352 = 0x8b004) by (vm_compute; reflexivity).
    assert (S1' : YK11.getr (ms_regs ms0) 1%bv = Z_to_bv 64 (BASE + 40352)) by exact S1.
    pmkst HS4.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr segs Wx (@cfg_at fx segs (transport_sigma TS_diginet_session_rx) rg mm mdx) Qx) end.
    eapply SRr_bind.
    { exact (pw_rx_call B MT c pos ly3 S3 W3 (ms_mem ms0) md9 B1 (ms_regs ms0) got now2 B2 r2
        RT KEEP OK HRUN9 S2r S3r S4r
        ltac:(rewrite S1'; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
        ltac:(unfold raZ; rewrite S1', EBN3, unsigned_lit_small by lia; lia)
        S10 S11 S12 S13 ltac:(rewrite Enow2; exact HNR) ltac:(lia) HX9 HRXM (HDN Hp)). }
    cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md10 & -> & HP5 & HRUN10).
    rewrite S1'.
    change (Z_to_bv 64 (BASE + 40352)) with (Z_to_bv 64 (BASE + (PW_RECV1 + 0x48))).
    assert (HRG5 : pw_rg_buf B c pos regs5) by exact (pw_rg_buf_pres B c pos (ms_regs ms0) regs5 HRGms0 HP5).
    assert (S26' : YK11.getr regs5 26 = w64 now2) by exact (eq_trans (HP5 26 ltac:(hnf; lia)) S26).
    pose proof (proj1 (proj1 HRUN10)) as HJ10.
    clear dependent ms0. clear dependent ms.
    (* +0x27c: a3 = s10 = now2, to the cut tick at rx's world *)
    pose proof HRG5 as (((V2 & V3 & V4 & V8 & V9 & V18) & V19 & V20 & V21 & V22 & V23 & V24 & V27) & V25).
    pose proof (pw_entry B MT c pos ly5 S5 W5 mem5 md10 B2 regs5 (PW_RECV1 + 0x48) RT OK HRUN10 (proj1 HRG5))
      as HS5.
    set (E3 := pw_E regs5 B2) in HS5.
    assert (HEIL : img_env VAL A_LIM E3) by (unfold E3; apply pw_env_img).
    assert (SHOK5 : sh_ok segs PW_Bx (@nil shent) E3 (mrestrict (w_H W5) mem5)) by constructor.
    assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs5 r)
      by (intros n r Hn; unfold E3; apply pw_ew_reg; exact Hn).
    paj_run_to_tok RUNTO HS5 HJ10 SHOK5 PW_B0 PW_TICK.
    { pw_awr. }
    set (md11 := with_vm_backing (m_vm_lazy md10) mat md10) in *. clearbody md11. clear mat.
    assert (KD11 : forall a, aview segs (w_H W5) (ms_mem ms) a = aview segs (w_H W5) mem5 a)
      by (intros a; exact (pw_run_kept E3 (w_H W5) mem5 (ms_mem ms) HFr a)).
    assert (HRUN11 : pw_run B MT c pos ly5 S5 W5 (ms_mem ms) md11 B2)
      by (apply (pw_run_win B MT c pos ly5 S5 W5 mem5 md10 B2 (ms_mem ms) md11 RT OK HRUN10 HJ10);
          [intros a _ _; exact (KD11 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
    pw_reg HS5 (Z_to_bv 5 2) (w64 (pw_sp1 c)) U2
      ltac:(cbn [sv_denot]; rewrite (EE3 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V2).
    pw_reg HS5 (Z_to_bv 5 3) (w64 (as_gp B)) U3
      ltac:(cbn [sv_denot]; rewrite (EE3 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V3).
    pw_reg HS5 (Z_to_bv 5 4) (w64 (as_tp B)) U4
      ltac:(cbn [sv_denot]; rewrite (EE3 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V4).
    pw_reg HS5 (Z_to_bv 5 8) (w64 (pw_SP c)) U8
      ltac:(cbn [sv_denot]; rewrite (EE3 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V8).
    pw_reg HS5 (Z_to_bv 5 9) (w64 (pw_sp1 c)) U9
      ltac:(cbn [sv_denot]; rewrite (EE3 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V9).
    pw_reg HS5 (Z_to_bv 5 18) (w64 (pw_F c pos)) U18
      ltac:(cbn [sv_denot]; rewrite (EE3 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V18).
    pw_reg HS5 (Z_to_bv 5 19) (w64 POLL_S) U19 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) U20
      ltac:(cbn [sv_denot]; rewrite (EE3 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V20).
    pw_reg HS5 (Z_to_bv 5 21) (w64 PW_SH64) U21 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 22) (w64 (POLL_S + 80)) U22 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 23) (w64 (POLL_S + 88)) U23 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 24) (w64 (POLL_S + 64)) U24 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) U25
      ltac:(cbn [sv_denot]; rewrite (EE3 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V25).
    pw_reg HS5 (Z_to_bv 5 27) (w64 PW_SH80) U27 ltac:(reflexivity).
    pw_reg HS5 (Z_to_bv 5 13) (w64 now2) U13
      ltac:(cbn [sv_denot]; rewrite (EE3 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact S26').
    pmkst HS5.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (@cfg_at fx segs (BASE + PW_TICK) rg mm mdx) Qx) end.
    apply (TICK RT KEEP OK pos ly5 S5 W5 (ms_mem ms) md11 (ms_regs ms) B2 now2 B3 r3 HRUN11).
    * unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
        [ exact U2 | exact U3 | exact U4 | exact U8 | exact U9 | exact U18 | exact U19 | exact U20 | exact U21
        | exact U22 | exact U23 | exact U24 | exact U27 | exact U25 ].
    * exact U13.
    * rewrite Enow2. exact HNR.
    * exact HTK.
    * exact HDR.
    * exact HDRX3.
Qed.

End s.

Theorem pw_recv1_piece : forall fx rc B MT, @pw_recv1_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_recv1_holds fx rc B MT). Qed.
