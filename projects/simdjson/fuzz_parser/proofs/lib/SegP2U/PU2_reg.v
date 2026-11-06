(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad HarnessP ProgP SjStage1 SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw PC_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_t0 PU2_entry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition s2_reg (zsp DOC THIS BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB : Z) : Prop :=
  (1 <= LEN <= 1048512) /\ (1 <= N <= LEN) /\ (N + 3 <= CAPT <= 16777216) /\ (LEN + 60 <= CAPS <= 16777216) /\
  (5 * LEN + 182 <= 3 * CAPS) /\ (0x7fff00000000 <= zsp <= 2 ^ 47) /\ (zsp mod 16 = 0) /\
  (zsp <= DOC /\ DOC + 16 <= 2 ^ 64 - 16 /\ DOC mod 8 = 0) /\
  (16 <= THIS /\ THIS mod 16 = 0 /\ THIS + 96 <= ATOPM /\ THIS + 96 + 2976 <= zsp) /\
  (16 <= BUF /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + 2976 <= zsp) /\
  (16 <= IDX /\ IDX mod 16 = 0 /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + 2976 <= zsp) /\
  (16 <= TBASE /\ TBASE mod 16 = 0 /\ TBASE + 8 * CAPT <= ATOPM /\ TBASE + 8 * CAPT + 2976 <= zsp) /\
  (16 <= SBASE /\ SBASE mod 16 = 0 /\ SBASE + CAPS <= ATOPM /\ SBASE + CAPS + 2976 <= zsp) /\
  (16 <= OCB /\ OCB mod 16 = 0 /\ OCB + 8192 <= ATOPM /\ OCB + 8192 + 2976 <= zsp) /\
  (16 <= IAB /\ IAB mod 16 = 0 /\ IAB + 1024 <= ATOPM /\ IAB + 1024 + 2976 <= zsp) /\
  DJ 0x10000 0xa3000 THIS 96 /\ DJ 0x10000 0xa3000 BUF (LEN + 64) /\ DJ 0x10000 0xa3000 IDX (4 * N + 12) /\
  DJ 0x10000 0xa3000 TBASE (8 * CAPT) /\ DJ 0x10000 0xa3000 SBASE CAPS /\ DJ 0x10000 0xa3000 OCB 8192 /\
  DJ 0x10000 0xa3000 IAB 1024 /\
  DJ THIS 96 BUF (LEN + 64) /\ DJ THIS 96 IDX (4 * N + 12) /\ DJ THIS 96 TBASE (8 * CAPT) /\ DJ THIS 96 SBASE CAPS /\
  DJ THIS 96 OCB 8192 /\ DJ THIS 96 IAB 1024 /\
  DJ BUF (LEN + 64) IDX (4 * N + 12) /\ DJ BUF (LEN + 64) TBASE (8 * CAPT) /\ DJ BUF (LEN + 64) SBASE CAPS /\
  DJ BUF (LEN + 64) OCB 8192 /\ DJ BUF (LEN + 64) IAB 1024 /\
  DJ IDX (4 * N + 12) TBASE (8 * CAPT) /\ DJ IDX (4 * N + 12) SBASE CAPS /\ DJ IDX (4 * N + 12) OCB 8192 /\
  DJ IDX (4 * N + 12) IAB 1024 /\
  DJ TBASE (8 * CAPT) SBASE CAPS /\ DJ TBASE (8 * CAPT) OCB 8192 /\ DJ TBASE (8 * CAPT) IAB 1024 /\
  DJ SBASE CAPS OCB 8192 /\ DJ SBASE CAPS IAB 1024 /\ DJ OCB 8192 IAB 1024.

Ltac destruct_s2_reg H :=
  destruct H as (H_LEN & H_N & H_CAPT & H_CAPS & H_CAPS3 & H_SP & H_SPa & H_DOC & H_THIS & H_BUF & H_IDX & H_TB & H_SB & H_OC & H_IA &
                 HU_THIS & HU_BUF & HU_IDX & HU_TB & HU_SB & HU_OC & HU_IA &
                 D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21).

(* [comment removed for export] *)
Definition copy_reg (zsp THIS BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY : Z) : Prop :=
  (0 <= V /\ V + 1 <= LEN) /\
  (16 <= COPY /\ COPY mod 16 = 0 /\ COPY + (LEN - V + 64) <= ATOPM /\ COPY + (LEN - V + 64) + 2976 <= zsp) /\
  DJ 0x10000 0xa3000 COPY (LEN - V + 64) /\
  DJ THIS 96 COPY (LEN - V + 64) /\ DJ BUF (LEN + 64) COPY (LEN - V + 64) /\ DJ IDX (4 * N + 12) COPY (LEN - V + 64) /\
  DJ TBASE (8 * CAPT) COPY (LEN - V + 64) /\ DJ SBASE CAPS COPY (LEN - V + 64) /\ DJ OCB 8192 COPY (LEN - V + 64) /\
  DJ IAB 1024 COPY (LEN - V + 64).

Ltac destruct_copy_reg H :=
  destruct H as (H_V & H_CP & HU_CP & D22 & D23 & D24 & D25 & D26 & D27 & D28).

Section R.
  Context {rc : runConstT}.

  Lemma s2_reg_of : forall (s : PState) (LB : list block) (m : word -> option byte) (sp : word) (lo B : Z) (d idx : list Z)
      (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z),
    RHEAP s LB m ->
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (psi, ASI, nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (pcp, ACP, ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB -> In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    ntp mod 8 = 0 -> 8 * (zlength idx + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    zlength d + 64 <= 2^20 -> 1 <= zlength idx <= zlength d ->
    bv_unsigned sp <= DOC -> DOC + 16 <= B -> DOC mod 8 = 0 -> B <= 2 ^ 64 - 160 ->
    ATOP <= lo -> lo <= bv_unsigned sp - 2976 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
    s2_reg (u sp) DOC THIS BUF (zlength d) ASI (zlength idx) ATP (ntp / 8) ASB nsb AOC AIA.
  Proof.
    intros until nia. intros HR ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hlen Sn
      Hspd Hdb Hda HB Hlo1 Hlo2 Hsp16 Hsp47.
    atop_facts. pose proof (u_rng' sp) as Rsp.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ith) as (Rt1 & Rt2 & Rt3 & Rt4 & Rt5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Isi) as (Ri1 & Ri2 & Ri3 & Ri4 & Ri5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Icp) as (Rc1 & Rc2 & Rc3 & Rc4 & Rc5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Itp) as (Rp1 & Rp2 & Rp3 & Rp4 & Rp5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Isb) as (Rs1 & Rs2 & Rs3 & Rs4 & Rs5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ioc) as (Ro1 & Ro2 & Ro3 & Ro4 & Ro5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Iia) as (Ra1 & Ra2 & Ra3 & Ra4 & Ra5); cbn [blk_addr blk_size fst snd] in *.
    pose proof (DJ_hull _ _ Rt5 Rt3) as UT. pose proof (DJ_hull _ _ Ri5 Ri3) as UI. pose proof (DJ_hull _ _ Rc5 Rc3) as UC.
    pose proof (DJ_hull _ _ Rp5 Rp3) as UP. pose proof (DJ_hull _ _ Rs5 Rs3) as US. pose proof (DJ_hull _ _ Ro5 Ro3) as UO.
    pose proof (DJ_hull _ _ Ra5 Ra3) as UA.
    clear Rt5 Ri5 Rc5 Rp5 Rs5 Ro5 Ra5.
    destruct (nodup7 _ _ _ _ _ _ _ ND) as (N12 & N13 & N14 & N15 & N16 & N17 & N23 & N24 & N25 & N26 & N27 & N34 & N35 & N36 & N37 &
                                           N45 & N46 & N47 & N56 & N57 & N67).
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Icp N13) as B_tc. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Isi N12) as B_ti.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Itp N14) as B_tp. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Isb N15) as B_ts.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Ioc N16) as B_to. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ith Iia N17) as B_ta.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Icp Isi (not_eq_sym N23)) as B_ci. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Icp Itp N34) as B_cp.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Icp Isb N35) as B_cs. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Icp Ioc N36) as B_co.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Icp Iia N37) as B_ca.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isi Itp N24) as B_ip. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isi Isb N25) as B_is.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isi Ioc N26) as B_io. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isi Iia N27) as B_ia.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Itp Isb N45) as B_ps. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Itp Ioc N46) as B_po.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Itp Iia N47) as B_pa. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isb Ioc N56) as B_so.
    pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Isb Iia N57) as B_sa. pose proof (blocks_DJ _ _ _ _ _ _ _ _ _ HR Ioc Iia N67) as B_oa.
    clear N12 N13 N14 N15 N16 N17 N23 N24 N25 N26 N27 N34 N35 N36 N37 N45 N46 N47 N56 N57 N67 ND HR Ith Isi Icp Itp Isb Ioc Iia.
    set (LEN := zlength d) in *. set (NN := zlength idx) in *.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    set (CAPT := ntp / 8) in *.
    unfold s2_reg.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hsp16|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    Ltac dj H := split; [eapply DJ_sub; [exact H | lia..]|].
    dj UT. dj UC. dj UI. dj UP. dj US. dj UO. dj UA.
    dj B_tc. dj B_ti. dj B_tp. dj B_ts. dj B_to. dj B_ta.
    dj B_ci. dj B_cp. dj B_cs. dj B_co. dj B_ca.
    dj B_ip. dj B_is. dj B_io. dj B_ia.
    dj B_ps. dj B_po. dj B_pa.
    dj B_so. dj B_sa.
    eapply DJ_sub; [exact B_oa | lia..].
  Qed.

  Lemma copy_reg_of : forall (s1 : PState) (LB : list block) (m : word -> option byte) (zsp : Z) (c : bptr) (COPY : Z)
      (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA BUF nim nsi ncp ntp nsb noc nia LEN NN V : Z),
    RHEAP s1 ((c, COPY, LEN - V + 64) :: LB) m -> rblock_range COPY (LEN - V + 64) ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (psi, ASI, nsi) LB -> 4 * NN + 12 <= nsi ->
    In (pcp, ACP, ncp) LB -> ACP <= BUF -> BUF + LEN + 64 <= ACP + ncp ->
    In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB -> In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    ntp mod 8 = 0 -> 0 <= V -> V + 1 <= LEN -> ATOP + 2976 <= zsp ->
    copy_reg zsp THIS BUF LEN ASI NN ATP (ntp / 8) ASB nsb AOC AIA V COPY.
  Proof.
    intros until V. intros HR2 BR Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 HV1 HV2 HZ.
    atop_facts.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    pose proof BR as (Rn1 & Rn2 & Rn3 & Rn4 & Rn5).
    pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Ith) as Bt. pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Icp) as Bc.
    pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Isi) as Bi. pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Itp) as Bp.
    pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Isb) as Bs. pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Ioc) as Bo.
    pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Iia) as Ba. cbn [blk_addr blk_size fst snd] in Bt, Bc, Bi, Bp, Bs, Bo, Ba.
    unfold copy_reg.
    split; [lia|]. split; [lia|]. split; [exact (DJ_hull _ _ Rn5 Rn3)|].
    split; [unfold DJ; clear - Bt Hnim; lia|]. split; [unfold DJ; clear - Bc Hb1 Hb2; lia|].
    split; [unfold DJ; clear - Bi Hnsi; lia|]. split; [unfold DJ; rewrite HCAPT; clear - Bp; lia|].
    split; [unfold DJ; clear - Bs; lia|]. split; [unfold DJ; clear - Bo Hnoc; lia|]. unfold DJ; clear - Ba Hnia; lia.
  Qed.
End R.
