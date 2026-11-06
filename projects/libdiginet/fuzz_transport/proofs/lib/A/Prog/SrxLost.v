(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_ntc.v, with its module paths and module names changed; 161 of its 235 lines of code are new or changed and 1052 lines of the source are left out. *)
(* SrxLost: the lost arm of diginet_session_rx's image-A walk, srx_lost_ok : srx_lost_stmt (SrxCut.v), code +0x43c ..
   +0x448 (0x879d0 .. 0x879dc). Run 1 (PaRun token engine, from the arm cut with no region) moves a1 = 7
   (DIGINET_R_DESK_DISCONNECT), a0 = s and takes `jal session_lost` (+0x444, return address +0x448); it stores nothing,
   so the memory at the call is the cut's (SrxCallKit.v srxk_mem_eq). session_lost is called through its contract
   transport_session_lost_cg in the walk's own G journal with the class-1 frame live: the heap frame at
   session_lost's window, slost_apart from srx_apart (slost_wr at DIGINET_R_DESK_DISCONNECT is a row of srx_wr), the
   class-2 count from srx_fix. Run 2 is the `j` to the tick cut (+0x480), where the switch's result is session_lost's
   world (srx_sw_lost, the state test of the cut), the heap frame and the read-only bytes are carried across
   session_lost's acall_kept_g, and srx_cur is folded with it (srxk_cur_call). No error path in this range. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut SrxCallKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxl_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "srxl_reg: no match for" T; fail
  end.

(* A register the run keeps: its value is the cut's (EE reads the valuation's atoms). *)
Ltac srxl_keep HS EE regs0 nn zn H :=
  srxl_reg HS (Z_to_bv 5 zn) (YK11.getr regs0 (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma srxl_lost : @srx_lost_stmt fx rc B MT.
Proof.
unfold srx_lost_stmt. intros TICK. unfold srx_lost_at, srx_arm_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HFRD HFB HTW HGF HINV HPRE HST HAFT HCMD HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & _ & _ & _ & _ & _ & HLOST & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf0 & Hgb0 &
  Hsrc0 & Hoffb & Hbg & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hap & Hinv0 & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hgb2 & Hsrc2 & HTF2 & Hrom2 & _).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof HCMD as (HCMD1 & HCMD2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (He0 : e = 0) by (rewrite srx_ev_zero in He; lia). subst e.
destruct (srxk_sp1 (spZ regs) sp1 Hsp16 Esp1) as (Hsp1 & Hsp1m).
destruct (srxk_ceil B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
pose proof srxk_stk_le as (HS176 & _ & HSA & _).
assert (EVA : SLOST_EV = 0) by reflexivity.
unfold SRX_FBYTES in HFc, HFapp.
(* the model: the switch is session_lost's, the call's result the tick's at session_lost's world *)
destruct (TSS.session_lost_m timg_A TF (srx_w1 Bx now) TS0.DIGINET_R_DESK_DISCONNECT) as [[B2 []]|] eqn:EOA;
  pose proof (eq_trans (srx_sw_lost timg_A TF (srx_w1 Bx now) b now HCMD1 HCMD2) EOA) as ESW;
  [| exfalso; rewrite (srxk_after_none _ _ _ _ _ ESW) in HAFT; discriminate HAFT].
assert (HTM : TSS.diginet_session_tick_m timg_A TF B2 now = Some (Bw', r))
  by (rewrite <- (srxk_after _ _ _ _ _ _ ESW); exact HAFT).
(* +0x43c .. +0x444: a1 = 7, a0 = s, `jal session_lost` *)
pose proof (srxk_entry W2 regs2 mem2 SRX_LOST) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof HJ2 as HJ.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into ms end.
pose proof (srxk_mem_eq _ _ _ HF) as EM.
clear HF HFr HG.
srxl_reg HS (Z_to_bv 5 10) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
srxl_reg HS (Z_to_bv 5 11) (w64 TS0.DIGINET_R_DESK_DISCONNECT) Q11 ltac:(reflexivity).
srxl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26488)) Q1 ltac:(apply codeptr_val; exact HEI).
srxl_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
srxl_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
srxl_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
srxl_keep HS EE regs2 8%nat 8 Q8. srxl_keep HS EE regs2 9%nat 9 Q9.
srxl_keep HS EE regs2 18%nat 18 Q18. srxl_keep HS EE regs2 19%nat 19 Q19.
srxl_keep HS EE regs2 20%nat 20 Q20. srxl_keep HS EE regs2 21%nat 21 Q21.
srxl_keep HS EE regs2 22%nat 22 Q22. srxl_keep HS EE regs2 25%nat 25 Q25.
srxl_keep HS EE regs2 26%nat 26 Q26. srxl_keep HS EE regs2 27%nat 27 Q27.
pmkst HS.
rewrite EM in HJ |- *.
set (regsC := ms_regs ms) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBN : BASE + 26488 = 0x879dc) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_session_lost) rg mm mdx) Qx) end.
(* the facts session_lost's contract asks, at the call *)
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (HWL : spZ regs - SRX_STK <= sp1 - SLOST_STK) by lia.
assert (HAPA : slost_apart TF (srx_w1 Bx now) TS0.DIGINET_R_DESK_DISCONNECT).
{ intros x Hx fr Hfr. apply (Hap x); [|exact Hfr]. right; right; right; right; right; right; right; right; left.
  exists (srx_w1 Bx now). exact Hx. }
assert (HCNT : count_cid SLOST_CID (frames S2) < fs_frames SLOST_CID).
{ rewrite Hfrs, srxk_count by (vm_compute; discriminate). change SLOST_CID with ONDATA_CID. lia. }
(* the call of session_lost (G form, the same journal) *)
eapply SRr_bind.
{ exact (HLOST fx STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 md1 (k + 0) regsC
    TS0.DIGINET_R_DESK_DISCONNECT TF (srx_w1 Bx now) B2 HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBN; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11
    ltac:(rewrite USPC; exact (srxk_al16 sp1 Hsp1m))
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    HTW HGF EOA ltac:(unfold TS0.DIGINET_R_DESK_DISCONNECT; lia)
    (srxk_tf_win B ly2 S2 W2 mem2 regs regsC SRX_STK SLOST_STK TF ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       HTF2)
    Hrom2 HAPA HCNT
    ltac:(rewrite EVA; rewrite srx_ev_zero in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_slost_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3 &
  Hgf3).
assert (He30 : e3 = 0) by (rewrite EVA in He3; lia). subst e3.
rewrite USPC in HK3.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (HEw : forall a, slost_wr (srx_w1 Bx now) TS0.DIGINET_R_DESK_DISCONNECT a ->
  srx_wr b a /\ inG TG.G_HARNESS a).
{ intros a Ha. split; [|exact (srxk_slost_wr_G _ _ _ Ha)].
  right; right; right; right; right; right; right; right; left. exists (srx_w1 Bx now). exact Ha. }
(* +0x448: `j` to the tick cut *)
rewrite Q1.
pose proof (srxk_entry W3 regs3 mem3 26488) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E3 n = YK11.getr regs3 rr)
  by (intros n rr Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HJ3 as HJ4.
paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) SRX_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into ms4 end.
pose proof (srxk_mem_eq _ _ _ HF) as EM4.
clear HF HFr HG.
srxl_keep HS3 EE3 regs3 2%nat 2 T2. srxl_keep HS3 EE3 regs3 3%nat 3 T3. srxl_keep HS3 EE3 regs3 4%nat 4 T4.
srxl_keep HS3 EE3 regs3 8%nat 8 T8. srxl_keep HS3 EE3 regs3 9%nat 9 T9.
srxl_keep HS3 EE3 regs3 18%nat 18 T18. srxl_keep HS3 EE3 regs3 19%nat 19 T19.
srxl_keep HS3 EE3 regs3 20%nat 20 T20. srxl_keep HS3 EE3 regs3 21%nat 21 T21.
srxl_keep HS3 EE3 regs3 22%nat 22 T22. srxl_keep HS3 EE3 regs3 25%nat 25 T25.
srxl_keep HS3 EE3 regs3 26%nat 26 T26. srxl_keep HS3 EE3 regs3 27%nat 27 T27.
pmkst HS3.
rewrite EM4 in HJ4 |- *.
replace (k + 0 + 0) with (k + 0) in HJ4 by lia.
(* the tick cut's facts *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
destruct (srxk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (ELF2 & ELO2 & EHI2).
destruct (srxk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (ELF4 & ELO4 & EHI4).
assert (HCUR4 : srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md4 0)
  by exact (srxk_cur_call B MT LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md4 (sp1 - SLOST_STK) sp1
    (slost_wr (srx_w1 Bx now) TS0.DIGINET_R_DESK_DISCONNECT)
    HFIX HCUR HJ4 Hfr3 Hperm3 HK3 Hmo3 HEw ltac:(lia) ltac:(unfold SRX_FRAME; lia)).
assert (HTF4 : trans_tframe_at B ly3 S3 W3 mem3 regs SRX_STK TF)
  by exact (srxk_tf_kept B LAWS HGX HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md4 regs SRX_STK (sp1 - SLOST_STK) sp1
    (slost_wr (srx_w1 Bx now) TS0.DIGINET_R_DESK_DISCONNECT) TF HAR2 HAR4 Hperm3 Hfr3
    ltac:(rewrite ELF4, ELF2; reflexivity)
    ltac:(rewrite ELO4, ELO2; reflexivity) ltac:(rewrite EHI4, EHI2; reflexivity) HK3
    (fun a Ha => proj2 (HEw a Ha)) (fun x Hx => Hap x (proj1 (HEw x Hx))) Htfg ltac:(lia) ltac:(lia) HTF2).
assert (HROM4 : trans_rom_view_rd W3 mem3) by exact (srxk_rom_kept B HRU HRE _ _ _ _ _ _ _ _ _ HK3 Hrom2).
assert (HLEN : length (srx_w1 Bx now) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTW).
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (HREGS4 : srx_regs_base regs (ms_regs ms4) now sp1 F).
{ unfold srx_regs_base, srx_regs_core. split; [split|].
  - exact (eq_trans T2 (eq_trans (CH 2 ltac:(hnf; lia)) (eq_trans Q2 eq_refl))).
  - split; [exact (eq_trans T3 (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans Q3 (eq_sym Hgp))))|].
    split; [exact (eq_trans T4 (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans Q4 (eq_sym Htp))))|].
    split; [exact (eq_trans T8 (eq_trans (CH 8 ltac:(hnf; lia)) (eq_trans Q8 R8)))|].
    split; [exact (eq_trans T9 (eq_trans (CH 9 ltac:(hnf; lia)) (eq_trans Q9 R9)))|].
    split; [exact (eq_trans T18 (eq_trans (CH 18 ltac:(hnf; lia)) (eq_trans Q18 R18)))|].
    split; [exact (eq_trans T19 (eq_trans (CH 19 ltac:(hnf; lia)) (eq_trans Q19 R19)))|].
    split; [exact (eq_trans T20 (eq_trans (CH 20 ltac:(hnf; lia)) (eq_trans Q20 R20)))|].
    split; [exact (eq_trans T25 (eq_trans (CH 25 ltac:(hnf; lia)) (eq_trans Q25 R25)))|].
    split; [exact (eq_trans T26 (eq_trans (CH 26 ltac:(hnf; lia)) (eq_trans Q26 R26)))|].
    exact (eq_trans T27 (eq_trans (CH 27 ltac:(hnf; lia)) (eq_trans Q27 R27))).
  - split; [exact (eq_trans T21 (eq_trans (CH 21 ltac:(hnf; lia)) (eq_trans Q21 R21)))|].
    exact (eq_trans T22 (eq_trans (CH 22 ltac:(hnf; lia)) (eq_trans Q22 R22))). }
exact (TICK LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  (srx_w1 Bx now) B2 pos sp1 F ly3 S3 W3 mem3 md4 0 (ms_regs ms4) HFIX HCUR4 HTF4 HROM4 Htw3 Hgf3 HLEN HINV ESW HTM
  HREGS4).
Qed.

End l.

Theorem srx_lost_ok : forall fx rc B MT, @srx_lost_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxl_lost fx rc B MT). Qed.
