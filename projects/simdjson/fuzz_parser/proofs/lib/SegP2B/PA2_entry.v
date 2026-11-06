(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad AsanCtrl AsanEmbed HarnessP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_kz PA2_reg APS2_iface A2Lib PA2_t0e PA2_stksh.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require B2E_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma shadow_cells2 : forall m A, 0x671000 <= A -> A + 2 < 2^64 -> rw_cells bsegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  forall i, 0 <= i < 2 -> m (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A H1 H2 HC i Hi. pose proof (rw_cells_bytes_at _ _ _ _ HC) as (_ & _ & HB). cbn [cells_bytes cbytes app] in HB.
  specialize (HB (Z.to_nat i) ltac:(cbn; lia)). rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by lia; lia). unfold wa in HB. rewrite HB.
  assert (i = 0 \/ i = 1) as [-> | ->] by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sval0_byte : forall b : byte, sval b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  change (256 `div` 2) with 128 in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma clean_shadow : forall m lo hi X cnt, unpoisoned m lo hi -> lo <= 8 * X -> 8 * (X + cnt) <= hi ->
  forall i, 0 <= i < cnt -> m (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m lo hi X cnt (H0 & H1 & HU) HL HH i Hi.
  destruct (HU (X + i) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hg).
  replace (Z.min (8 * (X + i) + 8) hi - 8 * (X + i)) with 8 in Hg by lia.
  unfold gran_ok in Hg. assert (Hs : sval b = 0) by lia. rewrite (sval0_byte b Hs) in Hb.
  unfold wa, ASHOFF in Hb. replace (SH + X + i) with (2147450880 + (X + i)) by lia. exact Hb.
Qed.


(* [comment removed for export] *)
Section E.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rstk : region) (d idx : list Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x24 x88 : word) (jtp jsb joc jia : list byte) (cls FA FN : Z).
  Hypothesis AH : AHEAP AI L RNG st LB m.
  Hypothesis ND : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia].
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * zlength idx + 16 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + zlength d + 64 <= ACP + ncp.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at bsegs m BUF (s1buf d).
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Sn : 1 <= zlength idx <= zlength d.
  Hypothesis HIDX : rw_cells bsegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  Hypothesis HO8 : rw_cells bsegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells bsegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO24 : rw_cells bsegs m (THIS + 24) [C4 x24].
  Hypothesis HO40 : rw_cells bsegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells bsegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells bsegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  Hypothesis HDSH : rw_cells bsegs m (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HTB : rw_cells bsegs m TPA [CB (Z.to_nat ntp) jtp].
  Hypothesis HSB : rw_cells bsegs m SBA [CB (Z.to_nat nsb) jsb].
  Hypothesis HOC : rw_cells bsegs m AOC [CB 8192 joc].
  Hypothesis HIA : rw_cells bsegs m AIA [CB 1024 jia].
  Hypothesis HCIMG : client_img m.
  Hypothesis HSTK : stk bsegs m lo (u sp).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis HCL : rclean m rstk.
  Hypothesis HCL1 : r_lo rstk <= lo.
  Hypothesis HCL2 : u sp <= r_hi rstk.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis HMI : mem_inv bsegs m.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.

  Lemma u_rngA : forall (w : word), 0 <= u w < 18446744073709551616.
  Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

  Lemma a2e_kn_of :
    know_ok bsegs (mkEZ (ZL_t0e (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                           (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) (zlength d) (ASI / 8) (zlength idx) (TPA / 8) (ntp / 8)
                           (SBA / 8) nsb (AOC / 8) (AIA / 8) 0 0 0 (BUF mod 8) ((zlength d + BUF mod 8 + 64) / 8)
                           ((4 * zlength idx + 12 + 7) / 8) (nsb / 8)
                           [u t0; u t1; u t2; u a2; u a3; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]))
            m B2E_defs.T0_kn.
  Proof.
    unfold STAGE2_STACK_A in Hlo2. atop_facts. pose proof (u_rngA sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & HTOP & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ith) as (_ & _ & _ & At & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isi) as (_ & _ & Ai1 & Ai & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Icp) as (_ & _ & _ & Ac & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Itp) as (_ & _ & _ & Ap & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isb) as (_ & _ & _ & As & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ioc) as (_ & _ & _ & Ao & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Iia) as (_ & _ & _ & Aa & _).
    set (LEN := zlength d) in *. set (NN := zlength idx) in *.
    pose proof (e16_of_16 (u sp) Hsp16) as E_SP. pose proof (e8_of_16 THIS At) as E_T8. pose proof (e8_of_8 DOC Hda) as E_DOC8.
    assert (E_B8 : BUF = 8 * (BUF / 8) + BUF mod 8) by (apply Z.div_mod; lia).
    pose proof (e8_of_16 ASI Ai) as E_I8. pose proof (e8_of_16 TPA Ap) as E_TB8. pose proof (e8_of_16 SBA As) as E_SB8.
    pose proof (e8_of_16 AOC Ao) as E_OC8. pose proof (e8_of_16 AIA Aa) as E_IA8.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (clear - Hntp8; Z.div_mod_to_equations; lia).
    pose proof (Z.mod_pos_bound BUF 8 ltac:(lia)) as RBO.
    assert (H_BG : 8 <= (LEN + BUF mod 8 + 64) / 8 <= 131080 /\ 0 <= LEN + BUF mod 8 + 64 - 8 * ((LEN + BUF mod 8 + 64) / 8) <= 7)
      by (clear - Hlen Sn RBO; Z.div_mod_to_equations; lia).
    assert (H_IG : 2 <= (4 * NN + 12 + 7) / 8 <= 0x200000 /\ 0 <= 8 * ((4 * NN + 12 + 7) / 8) - (4 * NN + 12) <= 7)
      by (clear - Hlen Sn; Z.div_mod_to_equations; lia).
    assert (H_SG : 7 <= nsb / 8 <= 2097152 /\ 0 <= nsb - 8 * (nsb / 8) <= 7) by (clear - Hnsb Sn; Z.div_mod_to_equations; lia).
    assert (H_IGB : ASI + 8 * ((4 * NN + 12 + 7) / 8) <= 140737479966720) by (clear - Hnsi Ai1 Hlen Sn; atop_facts; Z.div_mod_to_equations; lia).
    assert (M_LO : 0x671000 <= lo <= u sp - 8640) by (clear - Hlo1 Hlo2; lia).
    pose proof (a2_reg_of AI L RNG st LB m (u sp) lo 8640 d idx cls FA FN pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF
                  nim nsi ncp ntp nsb noc nia AH ND Ith Hnim Isi ltac:(clear - Hnsi; lia) Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 Hfk3
                  Hntp8 Hntp Hnsb3 Hnsb Hlen Sn Hlo1 ltac:(clear - Hlo2; lia) ltac:(lia) ltac:(clear - Hsptop HTOP; lia)) as REG.
    unfold a2_reg in REG.
    (* [comment removed for export] *)
    set (SP16 := u sp / 16) in *. set (T8 := THIS / 8) in *. set (DOC8 := DOC / 8) in *. set (B8 := BUF / 8) in *.
    set (BO := BUF mod 8) in *. set (I8 := ASI / 8) in *. set (TB8 := TPA / 8) in *. set (CAPT := ntp / 8) in *.
    set (SB8 := SBA / 8) in *. set (OC8 := AOC / 8) in *. set (IA8 := AIA / 8) in *.
    set (BG := (LEN + BO + 64) / 8) in *. set (IG := (4 * NN + 12 + 7) / 8) in *. set (SG := nsb / 8) in *.
    clearbody SP16 T8 DOC8 B8 BO I8 TB8 CAPT SB8 OC8 IA8 BG IG SG.
    (* [comment removed for export] *)
    assert (S_T8 : forall i, 0 <= i < 12 -> m (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Ith); clear - E_T8 Hnim; lia).
    assert (S_DOC8 : forall i, 0 <= i < 2 -> m (Z_to_bv 64 (SH + DOC8 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. assert (ESH : Z.shiftr DOC 3 = DOC8) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - E_DOC8; Z.div_mod_to_equations; lia).
      assert (HFN : 0 <= FN) by (unfold ablk in Hfk3; lia). pose proof (fake_band FA FN Hfk3 HFN) as (_ & Hf0 & Hf1).
      assert (HD0 : 0x671000 <= 8 * DOC8 /\ 8 * DOC8 + 16 <= 0x7FFFFF800000) by (rewrite <- E_DOC8; clear - Hfk1 Hfk2 Hf0 Hf1; atop_facts; lia).
      rewrite ESH in HDSH. pose proof (shadow_cells2 m (DOC8 + 2147450880) ltac:(clear - HD0; lia) ltac:(clear - HD0; lia) HDSH i Hi) as HS0.
      replace (SH + DOC8 + i) with (DOC8 + 2147450880 + i) by lia. exact HS0. }
    assert (S_B8 : forall i, 0 <= i < BG -> m (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Icp); clear - E_B8 Hb1 Hb2 H_BG RBO Ac; lia).
    assert (S_I8 : forall i, 0 <= i < IG -> m (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Isi); clear - E_I8 H_IG Hnsi; lia).
    assert (S_TB8 : forall i, 0 <= i < CAPT -> m (Z_to_bv 64 (SH + TB8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Itp); clear - E_TB8 HCAPT; lia).
    assert (S_SB8 : forall i, 0 <= i < SG -> m (Z_to_bv 64 (SH + SB8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Isb); clear - E_SB8 H_SG; lia).
    assert (S_OC8 : forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (SH + OC8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Ioc); clear - E_OC8 Hnoc; lia).
    assert (S_IA8 : forall i, 0 <= i < 128 -> m (Z_to_bv 64 (SH + IA8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH Iia); clear - E_IA8 Hnia; lia).
    assert (S_STK : forall i, 0 <= i < 1080 -> m (Z_to_bv 64 (SH + 2 * SP16 - 1080 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. destruct HCL as [(U & _) _].
      replace (SH + 2 * SP16 - 1080 + i) with (SH + (2 * SP16 - 1080) + i) by lia.
      eapply (clean_shadow m (r_lo rstk) (r_hi rstk) (2 * SP16 - 1080) 1080 U); clear - E_SP HCL1 HCL2 Hlo2 Hi; lia. }
    (* [comment removed for export] *)
    assert (W_STKSH : wr_at bsegs m (SH + 2 * SP16 - 1080) 1080) by (apply (wstk_of_rclean m rstk SP16 HCL); clear - E_SP HCL1 HCL2 Hlo1 Hlo2; atop_facts; lia).
    (* [comment removed for export] *)
    destruct (client_rt_of_aheap AI L RNG st LB m AH) as (M_GOT & _ & _ & M_SHB & M_SUAR & _ & _).
    pose proof (client_got_of_aheap AI L RNG st LB m AH HMI) as M_SUARG.
    pose proof (got_nothrow_cell AI L RNG st LB m AH HMI) as M_NT.
    assert (M_FMIN : rw_cells bsegs m 0x1174c0 [C4 (Z_to_bv 64 8388608)])
      by (destruct (client_img_x m HCIMG) as (_ & X & _); exact X).
    assert (W_TB : wr_at bsegs m TPA (8 * CAPT)) by (rewrite HCAPT; exact (rw_cells_wr_at _ _ _ _ ntp HTB ltac:(cbn; lia))).
    assert (W_SB : wr_at bsegs m SBA nsb) by exact (rw_cells_wr_at _ _ _ _ nsb HSB ltac:(cbn; lia)).
    assert (W_OC : wr_at bsegs m AOC 8192) by exact (rw_cells_wr_at _ _ _ _ 8192 HOC ltac:(cbn; lia)).
    assert (W_IA : wr_at bsegs m AIA 1024) by exact (rw_cells_wr_at _ _ _ _ 1024 HIA ltac:(cbn; lia)).
    assert (W_IDX : wr_at bsegs m ASI (4 * NN + 12))
      by (apply (rw_cells_wr_at _ _ _ _ _ HIDX); cbn [cells_size csize]; unfold NN, zlength in *; lia).
    assert (S_IMG : forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0))
      by (destruct (client_img_x m HCIMG) as (_ & _ & _ & _ & HIMG); exact (img_sh_pts m HIMG)).
    assert (M_BUFl : Z.of_nat (length (s1buf d)) = LEN + 64) by (unfold s1buf, LEN, zlength; rewrite length_map, length_app, repeat_length; lia).
    assert (M_BUFz : forall i, 0 <= i < 64 -> nth_error (s1buf d) (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. unfold s1buf. rewrite nth_error_map. rewrite nth_error_app2 by (unfold LEN, zlength; lia).
      rewrite nth_error_repeat by (unfold LEN, zlength; lia). reflexivity. }
    destruct_a2_reg REG.
    (* [comment removed for export] *)
    assert (H_TP : u tp = 0x64e9f0) by (rewrite HTP, u_Z_to_bv; reflexivity).
    eapply t0e_kn; eassumption.
  Qed.
End E.
End CANSEC.
