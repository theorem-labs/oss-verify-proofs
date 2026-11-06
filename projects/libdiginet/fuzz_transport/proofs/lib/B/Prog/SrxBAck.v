(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 185 of its 247 lines of code are new or changed and 703 lines of the source are left out. *)
(* SrxBAck: the ack arm of diginet_session_rx's image-B walk, srxb_ack_ok : srxb_ack_stmt (SrxBCut.v), code +0x408 ..
   +0x414 (0x87b8c .. 0x87b98), image A's SrxAck.v at image B's names. Run 1 (PaRun token engine at image B's listing,
   from the arm cut with no region) moves a0 = s, a1 = f and takes `jal on_ack` (+0x410, return address +0x414); it
   stores nothing, so the memory at the call is the cut's (SrxBCallKit.v srxbk_mem_eq). on_ack is called through its
   contract transport_on_ack_cg (lib/B/Prog/on_ack_cg.v) in the walk's own G journal with the class-1 frame live:
   trans_dframe_at of f and buf from the cut's srxb_rd, srxb_fbytes and decode_rd_ok, the heap frame at on_ack's
   window, onack_apart from srx_apart (onack_wr is a row of srx_wr), the class-2 count from srxb_fix. Run 2 is the `j`
   to the tick cut (+0x4c0), where the switch's result is on_ack's world (srxb_sw_ack), the heap frame and the
   read-only bytes are carried across on_ack's acall_kept_g, and srxb_cur is folded with it (srxbk_cur_call). No error
   path in this range. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import maybe_online_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut SrxBCallKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxba_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "srxba_reg: no match for" T; fail
  end.

(* A register the run keeps: its value is the cut's (EE reads the valuation's atoms). *)
Ltac srxba_keep HS EE regs0 nn zn H :=
  srxba_reg HS (Z_to_bv 5 zn) (YK11.getr regs0 (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma srxba_ack : @srxb_ack_stmt fx rc B MT.
Proof.
unfold srxb_ack_stmt. intros TICK. unfold srxb_ack_at, srxb_arm_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HFRD HFB HTW HGF HINV HPRE HST HAFT HCMD HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & _ & _ & _ & _ & HACK & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf0 & Hgb0 &
  Hsrc0 & Hoffb & Hbg & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hap & Hinv0 & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hgb2 & Hsrc2 & HTF2 & Hrom2 & _).
pose proof HFB as (Hfj & Hfb).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof HPRE as (Hcode & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (He0 : e = 0) by (rewrite srx_ev_zero in He; lia). subst e.
destruct (srxbk_sp1 (spZ regs) sp1 Hsp16 Esp1) as (Hsp1 & Hsp1m).
destruct (srxbk_ceil B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
pose proof srxbk_stk_le as (HS176 & HSA & _).
assert (EVA : ONACK_EV = 0) by reflexivity.
unfold SRXB_FBYTES in HFc, HFapp.
(* the model: the switch is on_ack's, the call's result the tick's at on_ack's world *)
destruct (TSS.on_ack_m timg_B TF (srx_w1 Bx now) b) as [[B2 []]|] eqn:EOA;
  pose proof (eq_trans (srxb_sw_ack timg_B TF (srx_w1 Bx now) b now HCMD) EOA) as ESW;
  [| exfalso; rewrite (srxbk_after_none _ _ _ _ _ ESW) in HAFT; discriminate HAFT].
assert (HTM : TSS.diginet_session_tick_m timg_B TF B2 now = Some (Bw', r))
  by (rewrite <- (srxbk_after _ _ _ _ _ _ ESW); exact HAFT).
(* +0x408 .. +0x410: a0 = s, a1 = f, `jal on_ack` *)
pose proof (srxbk_entry W2 regs2 mem2 SRXB_ACK) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof HJ2 as HJ.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into ms end.
pose proof (srxbk_mem_eq _ _ _ HF) as EM.
clear HF HFr HG.
srxba_reg HS (Z_to_bv 5 10) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
srxba_reg HS (Z_to_bv 5 11) (w64 (F + SRX_F)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
srxba_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26872)) Q1 ltac:(apply codeptr_val; exact HEI).
srxba_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
srxba_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
srxba_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
srxba_keep HS EE regs2 8%nat 8 Q8. srxba_keep HS EE regs2 9%nat 9 Q9.
srxba_keep HS EE regs2 18%nat 18 Q18. srxba_keep HS EE regs2 19%nat 19 Q19.
srxba_keep HS EE regs2 20%nat 20 Q20. srxba_keep HS EE regs2 21%nat 21 Q21.
srxba_keep HS EE regs2 22%nat 22 Q22. srxba_keep HS EE regs2 25%nat 25 Q25.
srxba_keep HS EE regs2 26%nat 26 Q26. srxba_keep HS EE regs2 27%nat 27 Q27.
pmkst HS.
rewrite EM in HJ |- *.
set (regsC := ms_regs ms) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBN : BASE + 26872 = 0x87b98) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_on_ack) rg mm mdx) Qx) end.
(* the facts on_ack's contract asks, at the call *)
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (HWL : spZ regs - SRX_STK <= sp1 - ONACK_STK) by lia.
assert (HDF : trans_dframe_at B ly2 S2 W2 mem2 regsC ONACK_STK (F + SRX_F) buf b fj).
{ split; [exact Hcode|]. split; [exact Hbuf0|]. split; [exact Hgb2|]. split; [exact Hsrc2|].
  split; [unfold decode_off_win in Hoffb |- *; rewrite USPC; destruct Hoffb as [Ho | Ho]; [left | right]; lia|].
  split; [exact Hbg|]. split; [unfold SRX_F; lia|].
  split; [unfold SRX_F; rewrite Z.add_mod, (srxbk_al64_8 F HF64) by lia; reflexivity|].
  split; [exact Hfj|]. split; [exact Hfb|].
  split; [exists SRX_CID, pos; split; [exact Hin2|]; rewrite EF2; unfold SRX_F, FRAME_F_SIZE;
          change (fs_frame_bytes SRX_CID) with 128; lia|].
  split; [exact HFRD|].
  unfold decode_off_win. rewrite USPC. left. unfold SRX_F, FRAME_F_SIZE. lia. }
assert (HAPA : onack_apart TF (srx_w1 Bx now) b).
{ intros x Hx fr Hfr. apply (Hap x); [|exact Hfr]. right; right; right; right; right; right; left.
  exists (srx_w1 Bx now). exact Hx. }
assert (HCNT : count_cid ONACK_CID (frames S2) + 1 < fs_frames ONACK_CID).
{ rewrite Hfrs, srxbk_count by (vm_compute; discriminate). change ONACK_CID with ONDATA_CID. lia. }
(* the call of on_ack (G form, the same journal) *)
eapply SRr_bind.
{ exact (HACK fx STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 md1 (k + 0) regsC
    (F + SRX_F) buf b fj TF (srx_w1 Bx now) B2 HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBN; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11
    ltac:(rewrite USPC; exact (srxbk_al16 sp1 Hsp1m))
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    HDF HTW HGF EOA
    (srxbk_tf_win B ly2 S2 W2 mem2 regs regsC SRX_STK ONACK_STK TF ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       HTF2)
    Htfg Hrom2 HAPA HCNT
    ltac:(rewrite EVA; rewrite srx_ev_zero in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_onack_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3 &
  Hgf3).
assert (He30 : e3 = 0) by (rewrite EVA in He3; lia). subst e3.
rewrite USPC in HK3.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (HEw : forall a, onack_wr (srx_w1 Bx now) b a -> srx_wr b a /\ inG TG.G_HARNESS_B a).
{ intros a Ha. split; [|exact (srxbk_onack_wr_G _ _ _ Ha)].
  right; right; right; right; right; right; left. exists (srx_w1 Bx now). exact Ha. }
(* +0x414: `j` to the tick cut *)
rewrite Q1.
pose proof (srxbk_entry W3 regs3 mem3 26872) as HS3.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E3 n = YK11.getr regs3 rr)
  by (intros n rr Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HJ3 as HJ4.
paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) SRXB_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into ms4 end.
pose proof (srxbk_mem_eq _ _ _ HF) as EM4.
clear HF HFr HG.
srxba_keep HS3 EE3 regs3 2%nat 2 T2. srxba_keep HS3 EE3 regs3 3%nat 3 T3. srxba_keep HS3 EE3 regs3 4%nat 4 T4.
srxba_keep HS3 EE3 regs3 8%nat 8 T8. srxba_keep HS3 EE3 regs3 9%nat 9 T9.
srxba_keep HS3 EE3 regs3 18%nat 18 T18. srxba_keep HS3 EE3 regs3 19%nat 19 T19.
srxba_keep HS3 EE3 regs3 20%nat 20 T20. srxba_keep HS3 EE3 regs3 21%nat 21 T21.
srxba_keep HS3 EE3 regs3 22%nat 22 T22. srxba_keep HS3 EE3 regs3 25%nat 25 T25.
srxba_keep HS3 EE3 regs3 26%nat 26 T26. srxba_keep HS3 EE3 regs3 27%nat 27 T27.
pmkst HS3.
rewrite EM4 in HJ4 |- *.
replace (k + 0 + 0) with (k + 0) in HJ4 by lia.
(* the tick cut's facts *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
destruct (srxbk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (ELF2 & ELO2 & EHI2).
destruct (srxbk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (ELF4 & ELO4 & EHI4).
assert (HCUR4 : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md4 0)
  by exact (srxbk_cur_call B MT LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md4 (sp1 - ONACK_STK) sp1 (onack_wr (srx_w1 Bx now) b)
    HFIX HCUR HJ4 Hfr3 Hperm3 HK3 Hmo3 HEw ltac:(lia) ltac:(unfold SRX_FRAME; lia)).
assert (HTF4 : trans_tframe_at B ly3 S3 W3 mem3 regs SRX_STK TF)
  by exact (srxbk_tf_kept B LAWS HGX HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md4 regs SRX_STK (sp1 - ONACK_STK) sp1
    (onack_wr (srx_w1 Bx now) b) TF HAR2 HAR4 Hperm3 Hfr3 ltac:(rewrite ELF4, ELF2; reflexivity)
    ltac:(rewrite ELO4, ELO2; reflexivity) ltac:(rewrite EHI4, EHI2; reflexivity) HK3
    (fun a Ha => proj2 (HEw a Ha)) (fun x Hx => Hap x (proj1 (HEw x Hx))) Htfg ltac:(lia) ltac:(lia) HTF2).
assert (HROM4 : trans_rom_view_rd W3 mem3) by exact (srxbk_rom_kept B HRU HRE _ _ _ _ _ _ _ _ _ HK3 Hrom2).
assert (HLEN : length (srx_w1 Bx now) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTW).
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (HREGS4 : srxb_regs_base regs (ms_regs ms4) now sp1 F).
{ unfold srxb_regs_base, srxb_regs_core. split; [split|].
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

End a.

Theorem srxb_ack_ok : forall fx rc B MT, @srxb_ack_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxba_ack fx rc B MT). Qed.
