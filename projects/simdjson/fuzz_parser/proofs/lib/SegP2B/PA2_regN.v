(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase AMalloc_iface AU_iface AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_kz PA2_reg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a2_regC (FXA zsp F THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB COPY n : Z) : Prop :=
  (0x671000 <= COPY /\ COPY + n <= ATOPM /\ COPY + n + FXA <= zsp) /\ DJ 0x7fff7000 0x100000001000 COPY n /\
  DJ THIS 96 COPY n /\ DJ DOC 16 COPY n /\ DJ BUF (LEN + 64) COPY n /\ DJ IDX (4 * N + 12) COPY n /\ DJ TBASE (8 * CAPT) COPY n /\
  DJ SBASE CAPS COPY n /\ DJ OCB 8192 COPY n /\ DJ IAB 1024 COPY n /\ DJ F 2048 COPY n /\ COPY mod 16 = 0.

Ltac destruct_a2_regC H :=
  destruct H as (H_COPY & HB_COPY & DC1 & DC2 & DC3 & DC4 & DC5 & DC6 & DC7 & DC8 & DC9 & HCm).

Section RN.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.

  Lemma a2_regC_of : forall L RNG st LB m (zsp lo FXA : Z) (d idx : list Z) (cls FA FN F : Z) (p : aptr) (COPY n : Z)
      (pim psi pcp ptp psb poc pia : aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z),
    AHEAP AI L RNG st (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB) m ->
    In (HB pim THIS nim) LB -> 96 <= nim -> In (HB psi ASI nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (HB ptp TPA ntp) LB -> In (HB psb SBA nsb) LB -> In (HB poc AOC noc) LB -> 8192 <= noc -> In (HB pia AIA nia) LB -> 1024 <= nia ->
    In (mkABlock (ABFake cls) FA FN) LB -> FA <= DOC -> DOC + 16 <= FA + FN ->
    ntp mod 8 = 0 -> nsb <= 2^24 ->
    ATOP + 4096 <= lo -> lo <= zsp - FXA -> 0 <= FXA ->
    a2_regC FXA zsp F THIS DOC BUF (zlength d) ASI (zlength idx) TPA (ntp / 8) SBA nsb AOC AIA COPY n.
  Proof.
    intros until nia. intros AH Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hd1 Hd2 Hntp8 Hnsb Hlo1 Hlo2 HF.
    atop_facts.
    assert (ND : List.NoDup (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB)) by exact (AI_blocks_nodup AI _ _ _ _ _ AH).
    apply NoDup_cons_iff in ND as [NI _].
    assert (DJC : forall b, In b (mkABlock (ABFake 5) F 2048 :: LB) -> DJ (ab_addr b) (ab_size b) COPY n).
    { intros b Hb. unfold DJ.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_intror Hb) (or_introl eq_refl)
                   ltac:(intros E; subst b; exact (NI Hb))) as D. cbn [ab_addr ab_size] in D. lia. }
    pose proof (DJC _ (or_intror Ith)) as Ct. pose proof (DJC _ (or_intror Isi)) as Ci. pose proof (DJC _ (or_intror Icp)) as Cc.
    pose proof (DJC _ (or_intror Itp)) as Cp. pose proof (DJC _ (or_intror Isb)) as Cs. pose proof (DJC _ (or_intror Ioc)) as Co.
    pose proof (DJC _ (or_intror Iia)) as Ca. pose proof (DJC _ (or_intror Ifk)) as Ck. pose proof (DJC _ (or_introl eq_refl)) as CF.
    cbn [ab_addr ab_size] in *. clear DJC NI.
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH (or_introl eq_refl)) as (UC & RC1 & RC2 & RC3 & RC4).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH (or_intror (or_intror Itp))) as (_ & _ & _ & _ & P1).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH (or_intror (or_intror Isb))) as (_ & _ & _ & _ & P2).
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    assert (Z0d : 0 <= zlength d) by (unfold zlength; lia). assert (Z0i : 0 <= zlength idx) by (unfold zlength; lia).
    unfold a2_regC.
    split; [lia|]. split; [exact UC|].
    split; [eapply DJ_sub; [exact Ct | lia..]|]. split; [eapply DJ_sub; [exact Ck | lia..]|].
    split; [eapply DJ_sub; [exact Cc | lia..]|]. split; [eapply DJ_sub; [exact Ci | lia..]|].
    split; [eapply DJ_sub; [exact Cp | lia..]|]. split; [eapply DJ_sub; [exact Cs | lia..]|].
    split; [eapply DJ_sub; [exact Co | lia..]|]. split; [eapply DJ_sub; [exact Ca | lia..]|].
    split; [exact CF | exact RC3].
  Qed.
End RN.
