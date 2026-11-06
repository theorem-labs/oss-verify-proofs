(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_ntc.v, with its module paths and module names changed; 144 of its 219 lines of code are new or changed and 1051 lines of the source are left out. *)
(* SrxTick: the tick piece of diginet_session_rx's image-A walk, srx_tick_ok : srx_tick_stmt (SrxCut.v), code +0x480 ..
   +0x48c (0x87a14 .. 0x87a20). Run 1 (PaRun token engine, from the tick cut with no region) moves a0 = s, a1 = now
   and takes `jal diginet_session_tick` (+0x488, return address +0x48c); it stores nothing, so the memory at the call
   is the cut's (SrxCallKit.v srxk_mem_eq). diginet_session_tick is called through its contract
   transport_diginet_session_tick_cg in the walk's own G journal with the class-1 frame live: the cut's world B2 (the
   world the switch left), the model premise (the cut's tick equation), the heap frame at the tick's window, the four
   run invariants at B2 (srx_inv_stmt's third conjunct from the cut's srx_inv at the switch's world), tick_apart from
   srx_apart (tick_wr is a row of srx_wr), the class-5, class-0 and class-2 counts from srx_fix. Run 2 is the `j` to the
   release cut (+0x1d4) with a0 = the tick's result r; srx_cur is folded with the tick's acall_kept_g
   (srxk_cur_call). No error path in this range. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
on_data_cg send_data_cg diginet_body_check_cg.
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
Ltac srxt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "srxt_reg: no match for" T; fail
  end.

(* A register the run keeps: its value is the cut's (EE reads the valuation's atoms). *)
Ltac srxt_keep HS EE regs0 nn zn H :=
  srxt_reg HS (Z_to_bv 5 zn) (YK11.getr regs0 (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma srxt_tick : @srx_tick_stmt fx rc B MT.
Proof.
unfold srx_tick_stmt. intros INV REL. unfold srx_tick_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bs B2 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HTF2 Hrom2 HTW HGF HLEN HINVs HSW HTM HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HTICK).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf0 & Hgb0 &
  Hsrc0 & Hoffb & Hbg & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hap & Hinv0 & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (He0 : e = 0) by (rewrite srx_ev_zero in He; lia). subst e.
destruct (srxk_sp1 (spZ regs) sp1 Hsp16 Esp1) as (Hsp1 & Hsp1m).
destruct (srxk_ceil B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
pose proof srxk_stk_le as (HS176 & _ & _ & HSA).
assert (EVA : TICK_EV = 0) by reflexivity.
unfold SRX_FBYTES in HFc, HFapp.
(* the run invariants at the switch's world B2 *)
pose proof (proj2 (proj2 INV) TF Bs b now B2 HLEN HINVs HSW) as HINV2.
pose proof HINV2 as (I1 & I2 & I4 & I5a & I5b & Incmd & Iqd).
(* +0x480 .. +0x488: a0 = s, a1 = now, `jal diginet_session_tick` *)
pose proof (srxk_entry W2 regs2 mem2 SRX_TICK) as HS.
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
pose proof (srxk_mem_eq _ _ _ HF) as EM.
clear HF HFr HG.
srxt_reg HS (Z_to_bv 5 10) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
srxt_reg HS (Z_to_bv 5 11) (w64 now) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
srxt_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26556)) Q1 ltac:(apply codeptr_val; exact HEI).
srxt_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
srxt_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
srxt_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
srxt_keep HS EE regs2 8%nat 8 Q8. srxt_keep HS EE regs2 9%nat 9 Q9.
srxt_keep HS EE regs2 18%nat 18 Q18. srxt_keep HS EE regs2 19%nat 19 Q19.
srxt_keep HS EE regs2 20%nat 20 Q20. srxt_keep HS EE regs2 21%nat 21 Q21.
srxt_keep HS EE regs2 22%nat 22 Q22. srxt_keep HS EE regs2 25%nat 25 Q25.
srxt_keep HS EE regs2 26%nat 26 Q26. srxt_keep HS EE regs2 27%nat 27 Q27.
pmkst HS.
rewrite EM in HJ |- *.
set (regsC := ms_regs ms) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBN : BASE + 26556 = 0x87a20) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_diginet_session_tick) rg mm mdx) Qx) end.
(* the facts diginet_session_tick's contract asks, at the call *)
assert (HWL : spZ regs - SRX_STK <= sp1 - TICK_STK) by lia.
assert (HAPT : tick_apart TF B2).
{ intros x Hx fr Hfr. apply (Hap x); [|exact Hfr]. right; right; right; right; right; right; right; right; right.
  exists B2. exact Hx. }
assert (HC5 : count_cid TICK_CID (frames S2) < fs_frames TICK_CID)
  by (rewrite Hfrs, srxk_count by (vm_compute; discriminate); exact Hc5).
assert (HC0 : count_cid SENDDATA_CID (frames S2) < fs_frames SENDDATA_CID)
  by (rewrite Hfrs, srxk_count by (vm_compute; discriminate); exact Hc0).
assert (HC2 : count_cid TRANS_BC_CID (frames S2) < fs_frames TRANS_BC_CID).
{ rewrite Hfrs, srxk_count by (vm_compute; discriminate). change TRANS_BC_CID with ONDATA_CID. lia. }
(* the call of diginet_session_tick (G form, the same journal) *)
eapply SRr_bind.
{ exact (HTICK fx STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem2 md1 (k + 0) regsC
    now r TF B2 Bw' HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBN; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11
    ltac:(rewrite USPC; exact (srxk_al16 sp1 Hsp1m))
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    Hnow HTW HGF HTM
    (srxk_tf_win B ly2 S2 W2 mem2 regs regsC SRX_STK TICK_STK TF ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       HTF2)
    Hrom2 HAPT I1 I2 Iqd I4 Incmd I5a I5b HC5 HC0 HC2
    ltac:(rewrite EVA; rewrite srx_ev_zero in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_tick_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HA0 & Htw3 &
  Hgf3).
assert (He30 : e3 = 0) by (rewrite EVA in He3; lia). subst e3.
rewrite USPC in HK3.
assert (HEw : forall a, tick_wr B2 a -> srx_wr b a /\ inG TG.G_HARNESS a).
{ intros a Ha. split; [|exact (srxk_tick_wr_G _ _ Ha)].
  right; right; right; right; right; right; right; right; right. exists B2. exact Ha. }
(* +0x48c: `j` to the release cut *)
rewrite Q1.
pose proof (srxk_entry W3 regs3 mem3 26556) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E3 n = YK11.getr regs3 rr)
  by (intros n rr Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HJ3 as HJ4.
paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) SRX_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into ms4 end.
pose proof (srxk_mem_eq _ _ _ HF) as EM4.
clear HF HFr HG.
srxt_keep HS3 EE3 regs3 2%nat 2 T2. srxt_keep HS3 EE3 regs3 3%nat 3 T3. srxt_keep HS3 EE3 regs3 4%nat 4 T4.
srxt_keep HS3 EE3 regs3 8%nat 8 T8. srxt_keep HS3 EE3 regs3 9%nat 9 T9. srxt_keep HS3 EE3 regs3 10%nat 10 T10.
srxt_keep HS3 EE3 regs3 18%nat 18 T18. srxt_keep HS3 EE3 regs3 19%nat 19 T19.
srxt_keep HS3 EE3 regs3 20%nat 20 T20. srxt_keep HS3 EE3 regs3 21%nat 21 T21.
srxt_keep HS3 EE3 regs3 22%nat 22 T22. srxt_keep HS3 EE3 regs3 25%nat 25 T25.
srxt_keep HS3 EE3 regs3 26%nat 26 T26. srxt_keep HS3 EE3 regs3 27%nat 27 T27.
pmkst HS3.
rewrite EM4 in HJ4 |- *.
replace (k + 0 + 0) with (k + 0) in HJ4 by lia.
(* the release cut's facts *)
assert (HCUR4 : srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md4 0)
  by exact (srxk_cur_call B MT LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md4 (sp1 - TICK_STK) sp1 (tick_wr B2)
    HFIX HCUR HJ4 Hfr3 Hperm3 HK3 Hmo3 HEw ltac:(lia) ltac:(unfold SRX_FRAME; lia)).
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (HREGS4 : srx_regs_rel regs (ms_regs ms4) now sp1 F r).
{ unfold srx_regs_rel, srx_regs_base, srx_regs_core. split; [split; [split|]|].
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
    exact (eq_trans T22 (eq_trans (CH 22 ltac:(hnf; lia)) (eq_trans Q22 R22))).
  - exact (eq_trans T10 HA0). }
exact (REL LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
  ly3 S3 W3 mem3 md4 0 (ms_regs ms4) HFIX HCUR4 Htw3 Hgf3 HREGS4).
Qed.

End t.

Theorem srx_tick_ok : forall fx rc B MT, @srx_tick_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxt_tick fx rc B MT). Qed.
