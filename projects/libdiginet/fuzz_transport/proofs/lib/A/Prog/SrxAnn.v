(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 275 of its 337 lines of code are new or changed and 1077 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcLoopCall.v, with its module paths and module names changed; 138 of its 195 lines of code are new or changed and 280 lines of the source are left out. *)
(* SrxAnn: the on_announce arm of the image-A walk of diginet_session_rx, Theorem srx_ann_ok : srx_ann_stmt
   (SrxCut.v), code +0x3dc .. +0x3ec (0x87970 .. 0x87980).

   What the code does. +0x3dc `addi a0, s4, 0`: a0 := s; +0x3e0 `addi a1, s6, 0`: a1 := f = F + 32; +0x3e4
   `addi a2, s3, 0`: a2 := now; +0x3e8 `jal on_announce`: ra := the address of +0x3ec, pc := 0x87a74; +0x3ec
   `j +0x480`: to the tick cut. No store, no load, no instrumented access, no error path.

   One run of the token engine (DgnTransportPaLib.v paj_run_tok over the G journal, TransportGRunA.v paj_run_x) from
   a symbolic state with no region and no fact covers the three moves and stops at the call. The callee's contract
   (on_announce_cg.v transport_on_announce_cg, a premise through srx_calls) is applied in the same G journal with the
   own class-1 frame live: f and the bytes at buf by SrxArmKit.v srxa_dframe, TF at on_announce's window by
   srxa_tframe_call, the world srx_w1 Bx now and its invariants (1) and (4) from the cut, the model equation from
   srx_after by srx_sw_ann. Its post folds into the cut's facts by srxa_after (every byte on_announce stores is a byte
   of G: srxa_onann_G; a row of srx_wr b). A second run takes `j +0x480` to the tick cut srx_tick_at, with the
   switch's world Bs = srx_w1 Bx now, its result B2 and the tick equation from srx_after. *)
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
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut SrxArmKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of the call, +0x3ec: `j +0x480`. *)
Definition SRXA_RET : Z := SRX_ANN + 0x10.

Section ann. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma srxa_ann : @srx_ann_stmt fx rc B MT.
Proof.
unfold srx_ann_stmt. intros TICK. unfold srx_ann_at, srx_arm_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HDF HFB Htw Hgf Hinv Hpre Hst Hafter Hcmd HREGS.
cbv beta in Hcmd.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HCALLS as (_ & _ & _ & _ & _ & HANN & _ & _ & _ & _).
pose proof (srxa_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
  as (Wm & Wa & Wb & Wc & Wd & We & Wf & Wg).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hwin0 & Hhi0 & Hnow & Hbuf & Hgb
  & Hsrcb & Howb & Hboff & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hapart & Hinv0 & Hnd0 & Hc1 & Hc4 & Hc5 & Hc0
  & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hgb2 & Hsrcb2 & HTF2 & Hrom2 & Hnd2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof Hpre as (Hcode & _).
assert (EV0 : SRX_EV = 0) by exact srx_ev_zero.
assert (EA0 : ONANN_EV = 0) by reflexivity.
assert (He0 : e = 0) by lia. subst e.
(* the model: the switch at srx_w1 Bx now is on_announce's call, then the tick *)
assert (HLs : length (srx_w1 Bx now) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
unfold srx_after in Hafter. rewrite (srx_sw_ann timg_A TF (srx_w1 Bx now) b now Hcmd) in Hafter.
revert Hafter.
destruct (TSS.on_announce_m timg_A TF (srx_w1 Bx now) b now) as [[B2 []]|] eqn:EA; intros Hafter;
  cbv beta iota in Hafter; [|discriminate Hafter].
(* +0x3dc .. +0x3e8: the three moves, up to the call *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof (srxa_entry SRX_ANN W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (srxa_E regs2)) by apply srxa_env.
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew (srxa_E regs2) n = YK11.getr regs2 r0)
  by (intros n r0 Hn; apply srxa_ew; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (srxa_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK SRXA_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?msx) =>
  set (ms1 := msx) in * end.
(* the run stores nothing; HJ1 is now the journal after it *)
lazymatch goal with HFx : frame_of ?Ex ?rsx mem2 (ms_mem ms1) |- _ =>
  assert (Emem : ms_mem ms1 = mem2) by exact (frame_of_read_only Ex rsx mem2 (ms_mem ms1) eq_refl HFx) end.
rewrite Emem in HJ1.
(* the registers at the call *)
assert (HPR : aregs_preserved regs2 (ms_regs ms1)).
{ lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
    apply (aregs_preserved_of_st_ok sg Hh Ex ssx msx regs2 [] HS (srxa_agree regs2));
    vm_compute; reflexivity end. }
srxa_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SRXA_RET)) Q1 ltac:(apply codeptr_val; exact HEI).
srxa_reg HS (10%bv : bv 5) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
srxa_reg HS (11%bv : bv 5) (w64 (F + SRX_F)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
srxa_reg HS (12%bv : bv 5) (w64 now) Q12
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
assert (Q2 : YK11.getr (ms_regs ms1) 2 = w64 sp1) by exact (eq_trans (HPR 2 ltac:(hnf; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by exact (eq_trans (eq_trans (HPR 3 ltac:(hnf; lia)) R3) Hgp).
assert (Q4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by exact (eq_trans (eq_trans (HPR 4 ltac:(hnf; lia)) R4) Htp).
assert (USP : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (EBR : BASE + SRXA_RET = 555392) by (vm_compute; reflexivity).
(* the premises of on_announce's contract *)
assert (Pret : YK0s.ret_ok (YK11.getr (ms_regs ms1) 1)).
{ rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport));
    [unfold SRXA_RET, SRX_ANN, AF_diginet_session_rx; lia | reflexivity]. }
assert (Pra : 4096 <= raZ (ms_regs ms1)) by (unfold raZ; rewrite Q1, EBR, unsigned_lit_small by lia; lia).
assert (Psp16 : spZ (ms_regs ms1) mod 16 = 0) by (rewrite USP; exact Wm).
assert (Pwin1 : sp0 - STK <= spZ (ms_regs ms1) - ONANN_STK) by (rewrite USP; lia).
assert (Pwin2 : spZ (ms_regs ms1) <= sp0) by (rewrite USP; lia).
assert (PDF : trans_dframe_at B ly2 S2 W2 mem2 (ms_regs ms1) ONANN_STK (F + SRX_F) buf b fj)
  by exact (srxa_dframe B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs ms1) buf now r b fj TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 ONANN_STK HFIX HCUR HRD HDF HFB Hcode USP ltac:(lia)).
assert (PTF : trans_tframe_at B ly2 S2 W2 mem2 (ms_regs ms1) ONANN_STK TF)
  by exact (srxa_tframe_call B ly2 S2 W2 mem2 regs (ms_regs ms1) SRX_STK ONANN_STK TF HTF2
    ltac:(rewrite USP; lia) ltac:(rewrite USP; lia)).
assert (PAP : onann_apart TF (srx_w1 Bx now) b).
{ intros x Hx. apply Hapart. do 5 right. left. exists (srx_w1 Bx now). exact Hx. }
pose proof Hinv as (PI1 & _ & PI4 & _ & _ & PI6 & _).
assert (PC4 : count_cid ONANN_CID (frames S2) < fs_frames ONANN_CID).
{ rewrite Hfrs. change (count_cid ONANN_CID ((SRX_CID, pos) :: frames Sc)) with (0 + count_cid ONANN_CID (frames Sc)).
  lia. }
assert (PC2 : count_cid WAKE_CID (frames S2) + 2 < fs_frames WAKE_CID).
{ change WAKE_CID with ONDATA_CID. rewrite Hfrs.
  change (count_cid ONDATA_CID ((SRX_CID, pos) :: frames Sc)) with (0 + count_cid ONDATA_CID (frames Sc)). lia. }
assert (PEV : st_nev S + (k + 0) + ONANN_EV <= EV_MAX) by lia.
(* +0x3e8: the call, at the pc the contract names *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_on_announce) rg mm mdx) Qx) end.
rewrite Emem.
pose proof (HANN fx) as HAf. unfold transport_on_announce_cg in HAf.
eapply SRr_bind.
{ exact (HAf STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 _ (k + 0) (ms_regs ms1)
    (F + SRX_F) buf now b fj TF (srx_w1 Bx now) B2 HJ1 Pret Pra Q3 Q4 Q10 Q11 Q12 Psp16 Pwin1 Pwin2 Hnow PDF Htw Hgf
    EA PTF Htfg Hrom2 PAP PI1 PI4 PI6 PC4 PC2 PEV). }
(* +0x3ec: the post of the call *)
intros W3 c3 _ HPOST.
unfold transport_onann_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3 & Hgf3).
rewrite USP in HK3.
destruct (srxa_after B MT LAWS HRU HRE MTL FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
  Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 ly3 S3 W3 mem3 md3 e3 ONANN_STK (onann_wr (srx_w1 Bx now) b) HFIX HCUR HTF2
  Hrom2 ltac:(lia) ltac:(lia) HJ3 Hfr3 Hperm3 HK3 Hmo3
  ltac:(intros a Ha; do 5 right; left; exists (srx_w1 Bx now); exact Ha)
  (srxa_onann_G (srx_w1 Bx now) b) ltac:(lia)) as (HCUR3 & HTF3 & Hrom3).
pose proof HCUR3 as (HJ3' & _).
rewrite Q1.
(* +0x3ec: `j +0x480`, to the tick cut *)
pose proof (srxa_entry SRXA_RET W3 regs3 mem3) as HS3.
assert (HEI3 : img_env VAL A_LIM (srxa_E regs3)) by apply srxa_env.
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) (srxa_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3' SHOK3 SRXA_B0 SRX_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms4 := msx) in * end.
lazymatch goal with HFx : frame_of ?Ex ?rsx mem3 (ms_mem ms4) |- _ =>
  assert (Emem4 : ms_mem ms4 = mem3) by exact (frame_of_read_only Ex rsx mem3 (ms_mem ms4) eq_refl HFx) end.
rewrite Emem4 in HJ3'.
assert (HPR4 : aregs_preserved regs3 (ms_regs ms4)).
{ lazymatch type of HS3 with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    apply (aregs_preserved_of_st_ok sg Hh Ex (abs_ss vl ssx) msx regs3 [] HS3 (srxa_agree regs3));
    vm_compute; reflexivity end. }
assert (HPall : aregs_preserved regs2 (ms_regs ms4))
  by exact (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ HPR HP3) HPR4).
pmkst HS3. rewrite Emem4.
exact (TICK LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  (srx_w1 Bx now) B2 pos sp1 F ly3 S3 W3 mem3 _ (0 + e3) (ms_regs ms4) HFIX (conj HJ3' (proj2 HCUR3)) HTF3 Hrom3
  Htw3 Hgf3 HLs Hinv
  (eq_trans (srx_sw_ann timg_A TF (srx_w1 Bx now) b now Hcmd) EA) Hafter
  (srxa_regs_base regs regs2 (ms_regs ms4) now sp1 F HREGS HPall)).
Qed.

End ann.

Theorem srx_ann_ok : forall fx rc B MT, @srx_ann_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxa_ann fx rc B MT). Qed.
