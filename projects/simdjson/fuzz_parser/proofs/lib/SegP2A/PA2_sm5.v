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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz PA2_reg APS2_iface A2Lib PA2_entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0 PA2_t0b PA2_t0c.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma acr_blk : forall CI LB SP b A n, In b LB -> ab_addr b <= A -> A + n <= ab_addr b + ab_size b -> aclient_range CI LB SP A n.
Proof. intros. right; left. exists b. split; [assumption | lia]. Qed.
Lemma acr_fake : forall CI LB SP cls FA FN A n, In (mkABlock (ABFake cls) FA FN) LB -> FA <= A -> A + n <= FA + FN ->
  aclient_range CI LB SP A n.
Proof. intros. left; right; right. exists cls, FA, FN. split; [assumption | lia]. Qed.
Lemma acr_stack : forall CI LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
Proof. intros. left; left. lia. Qed.
Lemma acr_img : forall CI LB SP iv A n, In iv CI -> fst iv <= A -> A + n <= snd iv -> aclient_range CI LB SP A n.
Proof. intros. left; right; left. exists iv. split; [assumption | lia]. Qed.

(* [comment removed for export] *)
Lemma shadow_pres : forall CI LB SP m m' X cnt, aheap_pres CI LB SP m m' -> 0 <= X -> 8 * (X + cnt) <= 2^47 ->
  (forall i, 0 <= i < cnt -> (ATOP <= 8 * (X + i) < 2^47) \/ in_ranges CI (8 * (X + i)) \/ in_fake LB (8 * (X + i))) ->
  (forall i, 0 <= i < cnt -> m (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0)) ->
  forall i, 0 <= i < cnt -> m' (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0).
Proof.
  intros CI LB SP m m' X cnt HP H0 H1 HC HZ i Hi.
  assert (E : SH + X + i = shad (8 * (X + i))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  specialize (HZ i Hi). rewrite E in HZ |- *.
  change (Z_to_bv 64 (shad (8 * (X + i)))) with (wa (shad (8 * (X + i)))) in HZ |- *.
  rewrite (aheap_pres_shadow CI LB SP m m' (8 * (X + i)) HP (HC i Hi)); [exact HZ|].
  rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
Lemma zero_cells32 : forall m A, rw_cells asegs m A (repeat (C8 (Z_to_bv 64 0)) 32) -> 0x665000 <= A -> A + 256 < 2^64 ->
  forall i, 0 <= i < 256 -> m (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A HC H1 H2 i Hi. pose proof (rw_cells_bytes_at _ _ _ _ HC) as (_ & _ & HB).
  assert (EQ : cells_bytes (repeat (C8 (Z_to_bv 64 0)) 32) = repeat (Z_to_bv 8 0) 256) by (vm_compute; reflexivity).
  rewrite EQ in HB. rewrite repeat_length in HB. specialize (HB (Z.to_nat i) ltac:(lia)).
  rewrite nth_error_repeat in HB by lia. rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by lia; lia). exact HB.
Qed.

(* [comment removed for export] *)
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m1 m2 : amem)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo SPAX F : Z) (d idx : list Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x24 x88 j0 j1 j2 : word) (junk : list byte) (cls FA FN : Z) (rest : list Z).
  (* [comment removed for export] *)
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
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Sn : 1 <= zlength idx <= zlength d.
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  (* [comment removed for export] *)
  Hypothesis Hbuf : bytes_at asegs m1 BUF (s1buf d).
  Hypothesis HO8 : rw_cells asegs m1 (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells asegs m1 (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO24 : rw_cells asegs m1 (THIS + 24) [C4 x24].
  Hypothesis HO40 : rw_cells asegs m1 (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells asegs m1 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells asegs m1 DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis S_DOC1 : forall i, 0 <= i < 2 -> m1 (Z_to_bv 64 (SH + DOC / 8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis HFM1 : rw_cells asegs m1 AFMIN [C4 (Z_to_bv 64 8388608)].
  Hypothesis HFMCI : exists iv, In iv CI /\ fst iv <= AFMIN /\ AFMIN + 4 <= snd iv.
  Hypothesis S_STK1 : forall i, 0 <= i < 1076 -> m1 (Z_to_bv 64 (SH + 2 * (u sp / 16) - 1076 + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_SAVED1 : forall k, 0 <= k < 13 ->
    bytes_at asegs m1 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0))).
  Hypothesis M_Z1 : bytes_at asegs m1 (u sp - 384) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis HIMG1 : img_sh m1.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  (* [comment removed for export] *)
  Hypothesis HSTK1 : stk asegs m1 lo (u sp).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsp47 : u sp <= 2^47.
  Hypothesis HSPA1 : SPAX mod 32 = 0.
  Hypothesis HSPA2 : 384 <= u sp - SPAX <= 415.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  (* [comment removed for export] *)
  Hypothesis MI2 : mem_inv asegs m2.
  Hypothesis STK2 : stk asegs m2 lo SPAX.
  Hypothesis PRES : aheap_pres CI LB SPAX m1 m2.
  Hypothesis AH2 : AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2.
  Hypothesis HFm : F mod 2048 = 0.
  Hypothesis HFb : ablk F (F + 2048).
  Hypothesis HFt : F + 2048 <= ATOP.
  Hypothesis HFc : rw_cells asegs m2 F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))].
  Hypothesis HFs : rw_cells asegs m2 (shad F) (repeat (C8 (Z_to_bv 64 0)) 32).

  Lemma a2t0_kn :
    know_ok asegs (mkEZ (PA2_t0c.ZL_t0'' (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                           (u s9) (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) (zlength d) (ASI / 8) (zlength idx) (TPA / 8) (ntp / 8)
                           (SBA / 8) nsb (AOC / 8) (AIA / 8) (F / 2048) ((u sp - 384 - SPAX) / 16) (fflag L 5 F) (BUF mod 8)
                           ((zlength d + BUF mod 8 + 64) / 8) ((4 * zlength idx + 12 + 7) / 8) (nsb / 8) rest))
            m2 A2_defs.T0_kn.
  Proof.
    unfold STAGE2_STACK_A in Hlo2. atop_facts. pose proof (u_rngA sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH2) as (_ & _ & HTOP & _).
    assert (HAH2 : AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2) by exact AH2.
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Ith)) as (_ & _ & _ & At & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Isi)) as (_ & _ & Ai1 & Ai & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Icp)) as (_ & _ & _ & Ac & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Itp)) as (_ & _ & _ & Ap & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Isb)) as (_ & _ & _ & As & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Ioc)) as (_ & _ & _ & Ao & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH2 (or_intror Iia)) as (_ & _ & _ & Aa & _).
    set (LEN := zlength d) in *. set (NN := zlength idx) in *.
    pose proof (e16_of_16 (u sp) Hsp16) as E_SP. pose proof (e8_of_16 THIS At) as E_T8. pose proof (e8_of_8 DOC Hda) as E_DOC8.
    assert (E_B8 : BUF = 8 * (BUF / 8) + BUF mod 8) by (apply Z.div_mod; lia).
    pose proof (e8_of_16 ASI Ai) as E_I8. pose proof (e8_of_16 TPA Ap) as E_TB8. pose proof (e8_of_16 SBA As) as E_SB8.
    pose proof (e8_of_16 AOC Ao) as E_OC8. pose proof (e8_of_16 AIA Aa) as E_IA8.
    assert (E_F11 : F = 2048 * (F / 2048)) by (clear - HFm; Z.div_mod_to_equations; lia).
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (clear - Hntp8; Z.div_mod_to_equations; lia).
    pose proof (Z.mod_pos_bound BUF 8 ltac:(lia)) as RBO.
    assert (H_BG : 8 <= (LEN + BUF mod 8 + 64) / 8 <= 131080 /\ 0 <= LEN + BUF mod 8 + 64 - 8 * ((LEN + BUF mod 8 + 64) / 8) <= 7)
      by (clear - Hlen Sn RBO; Z.div_mod_to_equations; lia).
    assert (H_IG : 2 <= (4 * NN + 12 + 7) / 8 <= 0x200000 /\ 0 <= 8 * ((4 * NN + 12 + 7) / 8) - (4 * NN + 12) <= 7)
      by (clear - Hlen Sn; Z.div_mod_to_equations; lia).
    assert (H_SG : 7 <= nsb / 8 <= 2097152 /\ 0 <= nsb - 8 * (nsb / 8) <= 7) by (clear - Hnsb Sn; Z.div_mod_to_equations; lia).
    assert (H_IGB : ASI + 8 * ((4 * NN + 12 + 7) / 8) <= 140737479966720) by (clear - Hnsi Ai1 Hlen Sn; atop_facts; Z.div_mod_to_equations; lia).
    assert (H_SPA : 0 <= (u sp - 384 - SPAX) / 16 <= 1 /\ (u sp - 384 - 16 * ((u sp - 384 - SPAX) / 16)) mod 32 = 0)
      by (clear - Hsp16 HSPA1 HSPA2; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (M_LO : 0x665000 <= lo <= u sp - 8608) by (clear - Hlo1 Hlo2; lia).
    pose proof (a2_reg_of AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2 (u sp) lo 8608 d idx cls FA FN pim psi pcp ptp psb poc pia
                  THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia AH2 ND (or_intror Ith) Hnim (or_intror Isi) ltac:(clear - Hnsi; lia)
                  (or_intror Icp) Hb1 Hb2 (or_intror Itp) (or_intror Isb) (or_intror Ioc) Hnoc (or_intror Iia) Hnia (or_intror Ifk) Hfk1 Hfk2 Hfk3
                  Hntp8 Hntp Hnsb3 Hnsb Hlen Sn Hlo1 ltac:(clear - Hlo2; lia) ltac:(lia) ltac:(clear - Hsp47; lia)) as REG.
    pose proof (a2_regF_of AI L RNG st LB m2 (u sp) lo 8608 d idx cls FA FN F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF
                  nim nsi ncp ntp nsb noc nia AH2 Ith Hnim Isi ltac:(clear - Hnsi; lia) Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 Hntp8
                  ltac:(clear - Hnsb; lia) HFb HFt Hlo1 ltac:(clear - Hlo2; lia) ltac:(lia)) as REGF.
    unfold a2_reg in REG. unfold a2_regF in REGF.
    assert (ESF : shad F = SH + 256 * (F / 2048)) by (rewrite shad_div; unfold ASHOFF; clear - HFm; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    set (SP16 := u sp / 16) in *. set (T8 := THIS / 8) in *. set (DOC8 := DOC / 8) in *. set (B8 := BUF / 8) in *.
    set (BO := BUF mod 8) in *. set (I8 := ASI / 8) in *. set (TB8 := TPA / 8) in *. set (CAPT := ntp / 8) in *.
    set (SB8 := SBA / 8) in *. set (OC8 := AOC / 8) in *. set (IA8 := AIA / 8) in *.
    set (BG := (LEN + BO + 64) / 8) in *. set (IG := (4 * NN + 12 + 7) / 8) in *. set (SG := nsb / 8) in *.
    set (F11 := F / 2048) in *. set (PB := (u sp - 384 - SPAX) / 16) in *.
    clearbody SP16 T8 DOC8 B8 BO I8 TB8 CAPT SB8 OC8 IA8 BG IG SG F11 PB.
    destruct_a2_reg REG. destruct_a2_regF REGF.
    (* [comment removed for export] *)
    assert (S_T8 : forall i, 0 <= i < 12 -> m2 (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Ith)); clear - E_T8 Hnim; lia).
    assert (S_DOC8 : forall i, 0 <= i < 2 -> m2 (Z_to_bv 64 (SH + DOC8 + i)) = Some (Z_to_bv 8 0)).
    { apply (shadow_pres CI LB SPAX m1 m2 DOC8 2 PRES ltac:(clear - E_DOC8 H_DOC; lia) ltac:(clear - E_DOC8 H_DOC; lia)); [| exact S_DOC1].
      intros i Hi. right; right. exists cls, FA, FN. split; [exact Ifk | clear - E_DOC8 Hfk1 Hfk2 Hi; lia]. }
    assert (S_B8 : forall i, 0 <= i < BG -> m2 (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Icp)); clear - E_B8 Hb1 Hb2 H_BG RBO Ac; lia).
    assert (S_I8 : forall i, 0 <= i < IG -> m2 (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Isi)); clear - E_I8 H_IG Hnsi; lia).
    assert (S_TB8 : forall i, 0 <= i < CAPT -> m2 (Z_to_bv 64 (SH + TB8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Itp)); clear - E_TB8 HCAPT; lia).
    assert (S_SB8 : forall i, 0 <= i < SG -> m2 (Z_to_bv 64 (SH + SB8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Isb)); clear - E_SB8 H_SG; lia).
    assert (S_OC8 : forall i, 0 <= i < 1024 -> m2 (Z_to_bv 64 (SH + OC8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Ioc)); clear - E_OC8 Hnoc; lia).
    assert (S_IA8 : forall i, 0 <= i < 128 -> m2 (Z_to_bv 64 (SH + IA8 + i)) = Some (Z_to_bv 8 0))
      by (eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH2 (or_intror Iia)); clear - E_IA8 Hnia; lia).
    assert (S_STK : forall i, 0 <= i < 1076 -> m2 (Z_to_bv 64 (SH + 2 * SP16 - 1076 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. replace (SH + 2 * SP16 - 1076 + i) with (SH + (2 * SP16 - 1076) + i) by lia.
      apply (shadow_pres CI LB SPAX m1 m2 (2 * SP16 - 1076) 1076 PRES ltac:(clear - E_SP H_SP; lia) ltac:(clear - E_SP H_SP; lia)); [| | lia].
      - intros i' Hi'. left. clear - E_SP Hlo1 Hlo2 Hi' H_SP. lia.
      - intros i' Hi'. replace (SH + (2 * SP16 - 1076) + i') with (SH + 2 * SP16 - 1076 + i') by lia. apply S_STK1; lia. }
    assert (S_F : forall i, 0 <= i < 256 -> m2 (Z_to_bv 64 (SH + 256 * F11 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite <- ESF. apply (zero_cells32 m2 (shad F) HFs); [rewrite ESF; clear - E_F11 H_F; lia | rewrite ESF; clear - E_F11 H_F; lia | lia]. }
    assert (M_SHF : wr_at asegs m2 (SH + 256 * F11) 256).
    { rewrite <- ESF. exact (rw_cells_wr_at _ _ _ _ 256 HFs ltac:(cbn; lia)). }
    (* [comment removed for export] *)
    assert (M_O8 : rw_cells asegs m2 (THIS + 8) [C4 (Z_to_bv 64 NN)])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HO8 | eapply (acr_blk CI LB SPAX _ _ _ Ith); cbn; lia]).
    assert (M_O16 : rw_cells asegs m2 (THIS + 16) [C8 (Z_to_bv 64 ASI)])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HO16 | eapply (acr_blk CI LB SPAX _ _ _ Ith); cbn; lia]).
    assert (M_O24 : rw_cells asegs m2 (THIS + 24) [C4 x24])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HO24 | eapply (acr_blk CI LB SPAX _ _ _ Ith); cbn; lia]).
    assert (M_O40 : rw_cells asegs m2 (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HO40 | eapply (acr_blk CI LB SPAX _ _ _ Ith); cbn; lia]).
    assert (M_O56 : rw_cells asegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 x88])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HO56 | eapply (acr_blk CI LB SPAX _ _ _ Ith); cbn; lia]).
    assert (M_DOC : rw_cells asegs m2 DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)])
      by (eapply aheap_pres_rw_cells; [exact PRES | exact HDOC | eapply (acr_fake CI LB SPAX _ _ _ _ _ Ifk); cbn; lia]).
    assert (M_BUF : bytes_at asegs m2 BUF (s1buf d)).
    { assert (EL : Z.of_nat (length (s1buf d)) = LEN + 64) by (unfold s1buf, LEN, zlength; rewrite length_map, length_app, repeat_length; lia).
      eapply aheap_pres_bytes_at; [exact PRES | exact Hbuf | eapply (acr_blk CI LB SPAX _ _ _ Icp); cbn [ab_addr ab_size]; rewrite ?EL;
        clear - Hb1 Hb2; lia]. }
    assert (M_FMIN : rw_cells asegs m2 AFMIN [C4 (Z_to_bv 64 8388608)]).
    { destruct HFMCI as (iv & Hiv & Hv1 & Hv2).
      eapply aheap_pres_rw_cells; [exact PRES | exact HFM1 | eapply (acr_img CI LB SPAX iv); [exact Hiv | lia | cbn; lia]]. }
    assert (M_SAVED : forall k, 0 <= k < 13 ->
      bytes_at asegs m2 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
    { intros k Hk. eapply aheap_pres_bytes_at; [exact PRES | exact (M_SAVED1 k Hk) | apply acr_stack; rewrite ?length_word_to_le_bytes; lia]. }
    assert (M_Z384 : bytes_at asegs m2 (u sp - 384) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { eapply aheap_pres_bytes_at; [exact PRES | exact M_Z1 | apply acr_stack; rewrite ?length_word_to_le_bytes; lia]. }
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror Itp)) as (_ & _ & _ & _ & _ & W_TB0 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror Isb)) as (_ & _ & _ & _ & _ & W_SB0 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror Ioc)) as (_ & _ & _ & _ & _ & W_OC0 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror Iia)) as (_ & _ & _ & _ & _ & W_IA0 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror Isi)) as (_ & _ & _ & _ & _ & W_IDX0 & _).
    assert (W_TB : wr_at asegs m2 TPA (8 * CAPT)) by (rewrite HCAPT; exact W_TB0).
    assert (W_SB : wr_at asegs m2 SBA nsb) by exact W_SB0.
    assert (W_OC : wr_at asegs m2 AOC 8192) by (destruct W_OC0 as (X0 & X1 & XW); split; [lia|]; split; [lia|]; intros; apply XW; lia).
    assert (W_IA : wr_at asegs m2 AIA 1024) by (destruct W_IA0 as (X0 & X1 & XW); split; [lia|]; split; [lia|]; intros; apply XW; lia).
    assert (W_IDX : wr_at asegs m2 ASI (4 * NN + 12)) by (destruct W_IDX0 as (X0 & X1 & XW); split; [lia|]; split; [lia|]; intros; apply XW; lia).
    destruct (client_rt_of_aheap AI L RNG st _ m2 AH2) as (M_GOT & _ & _ & M_SHB & M_SUAR & _ & _).
    pose proof (client_got_of_aheap AI L RNG st _ m2 AH2 MI2) as M_SUARG.
    pose proof (got_nothrow_cell AI L RNG st _ m2 AH2 MI2) as M_NT.
    assert (S_IMG : forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m2 (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0))
      by exact (img_sh_pts m2 (img_sh_pres AI LB SPAX m1 m2 HCI HIMG1 PRES)).
    assert (M_BUFl : Z.of_nat (length (s1buf d)) = LEN + 64) by (unfold s1buf, LEN, zlength; rewrite length_map, length_app, repeat_length; lia).
    assert (M_BUFz : forall i, 0 <= i < 64 -> nth_error (s1buf d) (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. unfold s1buf. rewrite nth_error_map. rewrite nth_error_app2 by (unfold LEN, zlength; lia).
      rewrite nth_error_repeat by (unfold LEN, zlength; lia). reflexivity. }
    assert (M_STK : stk asegs m2 lo (u sp)).
    { apply (stk_merge asegs m2 lo SPAX (u sp)); [exact STK2 | | lia].
      destruct (stk_split asegs m1 lo SPAX (u sp) HSTK1 ltac:(lia)) as [_ SU].
      eapply aheap_pres_stk; [exact PRES | exact SU | lia | lia]. }
    (* [comment removed for export] *)
    assert (H_TP : u tp = 0x642e70) by (rewrite HTP, u_Z_to_bv; reflexivity).
    eapply PA2_t0c.t0_kn; eassumption.
  Qed.
End T.
End CANSEC.
