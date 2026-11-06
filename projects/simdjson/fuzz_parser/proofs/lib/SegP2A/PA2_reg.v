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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation SH := 2147450880%Z (only parsing).

(* [comment removed for export] *)
Definition a2_reg (FXA zsp THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB : Z) : Prop :=
  (1 <= LEN <= 1048512) /\ (1 <= N <= LEN) /\ (N + 3 <= CAPT <= 16777216) /\ (LEN + 60 <= CAPS <= 16777216) /\
  (5 * LEN + 182 <= 3 * CAPS) /\ (0x7fff00000000 <= zsp <= 2 ^ 47) /\
  (0x665000 <= THIS /\ THIS + 96 <= ATOPM /\ THIS + 96 + FXA <= zsp) /\
  (0x665000 <= DOC /\ DOC + 16 <= ATOPM /\ DOC + 16 + FXA <= zsp) /\
  (0 <= BUF mod 8 <= 7 /\ 0x665000 <= BUF - BUF mod 8 /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + FXA <= zsp) /\
  (0x665000 <= IDX /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + FXA <= zsp) /\
  (0x665000 <= TBASE /\ TBASE + 8 * CAPT <= ATOPM /\ TBASE + 8 * CAPT + FXA <= zsp) /\
  (0x665000 <= SBASE /\ SBASE + CAPS <= ATOPM /\ SBASE + CAPS + FXA <= zsp) /\
  (0x665000 <= OCB /\ OCB + 8192 <= ATOPM /\ OCB + 8192 + FXA <= zsp) /\
  (0x665000 <= IAB /\ IAB + 1024 <= ATOPM /\ IAB + 1024 + FXA <= zsp) /\
  DJ 0x7fff7000 0x100000001000 THIS 96 /\ DJ 0x7fff7000 0x100000001000 DOC 16 /\ DJ 0x7fff7000 0x100000001000 BUF (LEN + 64) /\
  DJ 0x7fff7000 0x100000001000 IDX (4 * N + 12) /\ DJ 0x7fff7000 0x100000001000 TBASE (8 * CAPT) /\
  DJ 0x7fff7000 0x100000001000 SBASE CAPS /\ DJ 0x7fff7000 0x100000001000 OCB 8192 /\ DJ 0x7fff7000 0x100000001000 IAB 1024 /\
  DJ THIS 96 DOC 16 /\ DJ THIS 96 BUF (LEN + 64) /\ DJ THIS 96 IDX (4 * N + 12) /\ DJ THIS 96 TBASE (8 * CAPT) /\
  DJ THIS 96 SBASE CAPS /\ DJ THIS 96 OCB 8192 /\ DJ THIS 96 IAB 1024 /\
  DJ DOC 16 BUF (LEN + 64) /\ DJ DOC 16 IDX (4 * N + 12) /\ DJ DOC 16 TBASE (8 * CAPT) /\ DJ DOC 16 SBASE CAPS /\
  DJ DOC 16 OCB 8192 /\ DJ DOC 16 IAB 1024 /\
  DJ BUF (LEN + 64) IDX (4 * N + 12) /\ DJ BUF (LEN + 64) TBASE (8 * CAPT) /\ DJ BUF (LEN + 64) SBASE CAPS /\
  DJ BUF (LEN + 64) OCB 8192 /\ DJ BUF (LEN + 64) IAB 1024 /\
  DJ IDX (4 * N + 12) TBASE (8 * CAPT) /\ DJ IDX (4 * N + 12) SBASE CAPS /\ DJ IDX (4 * N + 12) OCB 8192 /\ DJ IDX (4 * N + 12) IAB 1024 /\
  DJ TBASE (8 * CAPT) SBASE CAPS /\ DJ TBASE (8 * CAPT) OCB 8192 /\ DJ TBASE (8 * CAPT) IAB 1024 /\
  DJ SBASE CAPS OCB 8192 /\ DJ SBASE CAPS IAB 1024 /\ DJ OCB 8192 IAB 1024.

Ltac destruct_a2_reg H :=
  destruct H as (H_LEN & H_N & H_CAPT & H_CAPS & H_CAPS3 & H_SP & H_THIS & H_DOC & H_BUF & H_IDX & H_TB & H_SB & H_OC & H_IA &
                 HB_THIS & HB_DOC & HB_BUF & HB_IDX & HB_TB & HB_SB & HB_OC & HB_IA &
                 D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 &
                 D23 & D24 & D25 & D26 & D27 & D28).

(* [comment removed for export] *)
Definition a2_regF (FXA zsp F THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB : Z) : Prop :=
  (0x665000 <= F /\ F + 2048 <= ATOPM /\ F + 2048 + FXA <= zsp) /\ DJ 0x7fff7000 0x100000001000 F 2048 /\
  DJ THIS 96 F 2048 /\ DJ DOC 16 F 2048 /\ DJ BUF (LEN + 64) F 2048 /\ DJ IDX (4 * N + 12) F 2048 /\ DJ TBASE (8 * CAPT) F 2048 /\
  DJ SBASE CAPS F 2048 /\ DJ OCB 8192 F 2048 /\ DJ IAB 1024 F 2048.

Ltac destruct_a2_regF H :=
  destruct H as (H_F & HB_F & DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7 & DF8).

Section R.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.

  Lemma DJ_sym : forall a n b k, DJ a n b k -> DJ b k a n.
  Proof. unfold DJ. intros. lia. Qed.
  Lemma DJ_sub : forall a n b k a' n' b' k', DJ a n b k -> a <= a' -> a' + n' <= a + n -> b <= b' -> b' + k' <= b + k -> 0 <= n' -> 0 <= k' ->
    DJ a' n' b' k'.
  Proof. unfold DJ. intros. lia. Qed.

  (* [comment removed for export] *)
  Lemma hh_DJ : forall L RNG st LB m p A n q B k, AHEAP AI L RNG st LB m -> In (HB p A n) LB -> In (HB q B k) LB -> p <> q ->
    DJ A n B k.
  Proof. intros. unfold DJ. eapply heap_blk_disj; eauto. Qed.
  Lemma hf_DJ : forall L RNG st LB m p A n cls FA FN, AHEAP AI L RNG st LB m -> In (HB p A n) LB -> In (mkABlock (ABFake cls) FA FN) LB ->
    DJ A n FA FN.
  Proof. intros. unfold DJ. eapply heap_fake_disj; eauto. Qed.
  Lemma hb_band : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    DJ 0x7fff7000 0x100000001000 A n /\ 0x665000 <= A /\ A + n <= ATOP /\ A mod 16 = 0 /\ 1 <= n.
  Proof.
    intros L RNG st LB m p A n AH HIN. pose proof (heap_blk_ablk AI _ _ _ _ _ _ _ _ AH HIN) as (Hb & Ha & Hn).
    unfold DJ. atop_facts. lia.
  Qed.
  Lemma fake_band : forall FA FN, ablk FA (FA + FN) -> 0 <= FN -> DJ 0x7fff7000 0x100000001000 FA FN /\ 0x665000 <= FA /\ FA + FN <= ATOP.
  Proof. intros FA FN HA HN. unfold ablk, AIMG_HI, KLS, DJ in *. atop_facts. lia. Qed.

  (* [comment removed for export] *)
  Lemma shadow_zero_in_blk : forall L RNG st LB m p A n X cnt, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    A <= 8 * X -> 8 * (X + cnt) <= A + n ->
    forall i, 0 <= i < cnt -> m (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros L RNG st LB m p A n X cnt AH HIN H1 H2 i Hi.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (B1 & B2 & B3 & B4) & _ & _ & BSH & _).
    pose proof (ablk_lin _ _ B1) as BL.
    assert (HA : exists q, A = 8 * q) by (exists (A / 8); pose proof (Z.div_mod A 16 ltac:(lia)); Z.div_mod_to_equations; lia).
    destruct HA as (q & HA).
    specialize (BSH (X - q + i) ltac:(lia) ltac:(lia)).
    replace (shad A) with (SH + q) in BSH by (rewrite HA; symmetry; apply shad_8; lia).
    replace (8 * (X - q + i) + 8 <=? n) with true in BSH by (symmetry; apply Z.leb_le; lia).
    unfold wa in BSH. replace (SH + q + (X - q + i)) with (SH + X + i) in BSH by lia. exact BSH.
  Qed.

  Lemma nodup7 : forall {T} (a b c d e f g : T), List.NoDup [a; b; c; d; e; f; g] ->
    a <> b /\ a <> c /\ a <> d /\ a <> e /\ a <> f /\ a <> g /\ b <> c /\ b <> d /\ b <> e /\ b <> f /\ b <> g /\
    c <> d /\ c <> e /\ c <> f /\ c <> g /\ d <> e /\ d <> f /\ d <> g /\ e <> f /\ e <> g /\ f <> g.
  Proof.
    intros T a b c d e f g H.
    repeat match goal with H : List.NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H as [? H] end.
    repeat match goal with H : ~ In _ _ |- _ => cbn [In] in H end.
    repeat split; intros E; subst; tauto.
  Qed.

  Lemma a2_reg_of : forall L RNG st LB m (zsp : Z) (lo FXA : Z) (d idx : list Z) (cls FA FN : Z)
      (pim psi pcp ptp psb poc pia : aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z),
    AHEAP AI L RNG st LB m ->
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (HB pim THIS nim) LB -> 96 <= nim -> In (HB psi ASI nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (HB ptp TPA ntp) LB -> In (HB psb SBA nsb) LB -> In (HB poc AOC noc) LB -> 8192 <= noc -> In (HB pia AIA nia) LB -> 1024 <= nia ->
    In (mkABlock (ABFake cls) FA FN) LB -> FA <= DOC -> DOC + 16 <= FA + FN -> ablk FA (FA + FN) ->
    ntp mod 8 = 0 -> 8 * (zlength idx + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    zlength d + 64 <= 2^20 -> 1 <= zlength idx <= zlength d ->
    ATOP + 4096 <= lo -> lo <= zsp - FXA -> 0 <= FXA -> zsp <= 2^47 ->
    a2_reg FXA zsp THIS DOC BUF (zlength d) ASI (zlength idx) TPA (ntp / 8) SBA nsb AOC AIA.
  Proof.
    intros until nia. intros AH ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hd1 Hd2 Hfa Hntp8 Hntp Hnsb3 Hnsb Hlen Sn
      Hlo1 Hlo2 HF Hsp.
    atop_facts.
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Ith) as (UT & Rt1 & Rt2 & Rt3 & Rt4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Isi) as (UI & Ri1 & Ri2 & Ri3 & Ri4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Icp) as (UC & Rc1 & Rc2 & Rc3 & Rc4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Itp) as (UP & Rp1 & Rp2 & Rp3 & Rp4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Isb) as (US & Rs1 & Rs2 & Rs3 & Rs4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Ioc) as (UO & Ro1 & Ro2 & Ro3 & Ro4).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH Iia) as (UA & Ra1 & Ra2 & Ra3 & Ra4).
    pose proof (fake_band FA FN Hfa ltac:(pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Ifk) as BB; cbn [ab_size] in BB; lia)) as (UF & Rf1 & Rf2).
    destruct (nodup7 _ _ _ _ _ _ _ ND) as (N12 & N13 & N14 & N15 & N16 & N17 & N23 & N24 & N25 & N26 & N27 & N34 & N35 & N36 & N37 &
                                           N45 & N46 & N47 & N56 & N57 & N67).
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Icp N13) as B_tc. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Isi N12) as B_ti.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Itp N14) as B_tp. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Isb N15) as B_ts.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Ioc N16) as B_to. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Iia N17) as B_ta.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Isi (not_eq_sym N23)) as B_ci. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Itp N34) as B_cp.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Isb N35) as B_cs. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Ioc N36) as B_co.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Iia N37) as B_ca.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isi Itp N24) as B_ip. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isi Isb N25) as B_is.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isi Ioc N26) as B_io. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isi Iia N27) as B_ia.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Itp Isb N45) as B_ps. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Itp Ioc N46) as B_po.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Itp Iia N47) as B_pa. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isb Ioc N56) as B_so.
    pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isb Iia N57) as B_sa. pose proof (hh_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ioc Iia N67) as B_oa.
    pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ith Ifk) as F_t. pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Icp Ifk) as F_c.
    pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isi Ifk) as F_i. pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Itp Ifk) as F_p.
    pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Isb Ifk) as F_s. pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Ioc Ifk) as F_o.
    pose proof (hf_DJ _ _ _ _ _ _ _ _ _ _ _ AH Iia Ifk) as F_a.
    clear N12 N13 N14 N15 N16 N17 N23 N24 N25 N26 N27 N34 N35 N36 N37 N45 N46 N47 N56 N57 N67 ND AH Ith Isi Icp Itp Isb Ioc Iia Ifk Hfa.
    set (LEN := zlength d) in *. set (NN := zlength idx) in *.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    set (CAPT := ntp / 8) in *.
    assert (HBO : 0 <= BUF mod 8 <= 7 /\ BUF - BUF mod 8 >= ACP) by (pose proof (Z.mod_pos_bound BUF 8 ltac:(lia)); split; [lia|];
      pose proof (Z.div_mod BUF 8 ltac:(lia)); pose proof (Z.div_mod ACP 16 ltac:(lia)); Z.div_mod_to_equations; lia).
    unfold a2_reg.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    Ltac dj H := split; [eapply DJ_sub; [exact H | lia..]|].
    dj UT. dj UF. dj UC. dj UI. dj UP. dj US. dj UO. dj UA.
    split; [apply DJ_sub with THIS nim FA FN; [exact F_t | lia..]|].
    dj B_tc. dj B_ti. dj B_tp. dj B_ts. dj B_to. dj B_ta.
    split; [apply DJ_sym; apply DJ_sub with ACP ncp FA FN; [exact F_c | lia..]|].
    split; [apply DJ_sym; apply DJ_sub with ASI nsi FA FN; [exact F_i | lia..]|].
    split; [apply DJ_sym; apply DJ_sub with TPA ntp FA FN; [exact F_p | lia..]|].
    split; [apply DJ_sym; apply DJ_sub with SBA nsb FA FN; [exact F_s | lia..]|].
    split; [apply DJ_sym; apply DJ_sub with AOC noc FA FN; [exact F_o | lia..]|].
    split; [apply DJ_sym; apply DJ_sub with AIA nia FA FN; [exact F_a | lia..]|].
    dj B_ci. dj B_cp. dj B_cs. dj B_co. dj B_ca.
    dj B_ip. dj B_is. dj B_io. dj B_ia.
    dj B_ps. dj B_po. dj B_pa.
    dj B_so. dj B_sa.
    eapply DJ_sub; [exact B_oa | lia..].
  Qed.
  Lemma a2_regF_of : forall L RNG st LB m (zsp lo FXA : Z) (d idx : list Z) (cls FA FN F : Z)
      (pim psi pcp ptp psb poc pia : aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z),
    AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m ->
    In (HB pim THIS nim) LB -> 96 <= nim -> In (HB psi ASI nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (HB ptp TPA ntp) LB -> In (HB psb SBA nsb) LB -> In (HB poc AOC noc) LB -> 8192 <= noc -> In (HB pia AIA nia) LB -> 1024 <= nia ->
    In (mkABlock (ABFake cls) FA FN) LB -> FA <= DOC -> DOC + 16 <= FA + FN ->
    ntp mod 8 = 0 -> nsb <= 2^24 ->
    ablk F (F + 2048) -> F + 2048 <= ATOP -> ATOP + 4096 <= lo -> lo <= zsp - FXA -> 0 <= FXA ->
    a2_regF FXA zsp F THIS DOC BUF (zlength d) ASI (zlength idx) TPA (ntp / 8) SBA nsb AOC AIA.
  Proof.
    intros until nia. intros AH Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hd1 Hd2 Hntp8 Hnsb HFa HFt Hlo1 Hlo2 HF.
    atop_facts.
    assert (ND : List.NoDup (mkABlock (ABFake 5) F 2048 :: LB)) by exact (AI_blocks_nodup AI _ _ _ _ _ AH).
    apply NoDup_cons_iff in ND as [NI _].
    assert (DJF : forall b, In b LB -> DJ (ab_addr b) (ab_size b) F 2048).
    { intros b Hb. unfold DJ.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_intror Hb) (or_introl eq_refl)
                   ltac:(intros E; subst b; exact (NI Hb))) as D. cbn [ab_addr ab_size] in D. lia. }
    pose proof (DJF _ Ith) as Ft. pose proof (DJF _ Isi) as Fi. pose proof (DJF _ Icp) as Fc. pose proof (DJF _ Itp) as Fp.
    pose proof (DJF _ Isb) as Fs. pose proof (DJF _ Ioc) as Fo. pose proof (DJF _ Iia) as Fa. pose proof (DJF _ Ifk) as Fk.
    cbn [ab_addr ab_size] in *. clear DJF NI.
    pose proof (fake_band F 2048 HFa ltac:(lia)) as (UF & _).
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    assert (Z0d : 0 <= zlength d) by (unfold zlength; lia). assert (Z0i : 0 <= zlength idx) by (unfold zlength; lia).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH (or_intror Itp)) as (_ & _ & _ & _ & P1).
    pose proof (hb_band _ _ _ _ _ _ _ _ AH (or_intror Isb)) as (_ & _ & _ & _ & P2).
    unfold a2_regF.
    split; [unfold ablk, AIMG_HI, KLS in *; lia|]. split; [exact UF|].
    split; [eapply DJ_sub; [exact Ft | lia..]|]. split; [eapply DJ_sub; [exact Fk | lia..]|].
    split; [eapply DJ_sub; [exact Fc | lia..]|]. split; [eapply DJ_sub; [exact Fi | lia..]|].
    split; [eapply DJ_sub; [exact Fp | lia..]|]. split; [eapply DJ_sub; [exact Fs | lia..]|].
    split; [eapply DJ_sub; [exact Fo | lia..]|]. eapply DJ_sub; [exact Fa | lia..].
  Qed.
End R.
