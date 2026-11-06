(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad HarnessP ProgP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw PU_iface PC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPU_sum PFFU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import S2TabU U2_defs U2_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_t0 PU2_t0b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

(* [comment removed for export] *)
Lemma u32bytes_eq : forall l, S2G2.u32bytes l = SjS1Bytes.u32bytes l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [S2G2.u32bytes SjS1Bytes.u32bytes]. rewrite IH. reflexivity. Qed.
Lemma bufbytes_eq : forall d, S2G2.bufbytes d = s1buf d.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mbytes_of_bytes_at_heap : forall m A bs, bytes_at usegs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> u (Z_to_bv 64 (A + i)) + 1 <= 0x10000 \/ 0xb3000 <= u (Z_to_bv 64 (A + i))) ->
  mbytes m A bs.
Proof.
  intros m A bs (H0 & H1 & HB) HR i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (apply HR; exact Hi). unfold wa in HB. rewrite HB.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma DJ_sub : forall a n b k a' n' b' k', DJ a n b k -> a <= a' -> a' + n' <= a + n -> b <= b' -> b' + k' <= b + k -> 0 <= n' -> 0 <= k' ->
  DJ a' n' b' k'.
Proof. unfold DJ. intros. lia. Qed.
Lemma DJ_sym : forall a n b k, DJ a n b k -> DJ b k a n.
Proof. unfold DJ. intros. lia. Qed.
Lemma DJ_hull : forall A n, (A + n <= 0x10000 \/ 0xb3000 <= A) -> 0 <= n -> DJ 0x10000 0xa3000 A n.
Proof. unfold DJ. intros. lia. Qed.

Lemma nodup7 : forall {T} (a b c d e f g : T), List.NoDup [a; b; c; d; e; f; g] ->
  a <> b /\ a <> c /\ a <> d /\ a <> e /\ a <> f /\ a <> g /\ b <> c /\ b <> d /\ b <> e /\ b <> f /\ b <> g /\
  c <> d /\ c <> e /\ c <> f /\ c <> g /\ d <> e /\ d <> f /\ d <> g /\ e <> f /\ e <> g /\ f <> g.
Proof.
  intros T a b c d e f g H.
  inversion H as [|? ? Na H1]; subst. inversion H1 as [|? ? Nb H2]; subst. inversion H2 as [|? ? Nc H3]; subst.
  inversion H3 as [|? ? Nd H4]; subst. inversion H4 as [|? ? Ne H5]; subst. inversion H5 as [|? ? Nf H6]; subst.
  cbn [In] in *. repeat split; intros ->; tauto.
Qed.



Section E.
  Context {rc : runConstT}.
(* [comment removed for export] *)
  Lemma blocks_DJ : forall s LB m p1 A1 n1 p2 A2 n2, RHEAP s LB m -> In (p1, A1, n1) LB -> In (p2, A2, n2) LB -> p1 <> p2 ->
  DJ A1 n1 A2 n2.
  Proof.
    intros s LB m p1 A1 n1 p2 A2 n2 HR I1 I2 NE.
    exact (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof s LB m (p1, A1, n1) (p2, A2, n2) HR I1 I2 NE).
  Qed.
  Hypothesis SFPS_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPSU.
  Hypothesis PFFS_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFSU.

  Definition ZLe (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA : Z) : list Z :=
    ZL0 (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
        THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA
        (u t0) (u t1) (u t2) (u a2) (u a3) (u a4) (u a5) (u a6) (u a7) (u t3) (u t4) (u t5) (u t6).

  Lemma u_rng' : forall (w : word), 0 <= u w < M64.
  Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

  Lemma t0_regs : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA,
    regs_ok (mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                       THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA)) T0_regs
      (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Proof.
    intros. apply regs_ok_mkR.
    transitivity (map (fun n => Z_to_bv 64 (nth n (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                                   THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA) 0))
       [0; 1; 2; 3; 28; 29; 30; 4; 5; 16; 17; 31; 32; 33; 34; 35; 36; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 37; 38; 39; 40]%nat).
    { reflexivity. }
    cbn [map nth ZLe ZL0]. rewrite !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Lemma s1buf_length : forall d, Z.of_nat (length (s1buf d)) = zlength d + 64.
  Proof. intros d. unfold s1buf, zlength. rewrite length_map, length_app, repeat_length. lia. Qed.
  Lemma s1buf_zero : forall d i, 0 <= i < 64 -> nth_error (s1buf d) (Z.to_nat (zlength d + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros d i Hi. unfold s1buf. rewrite nth_error_map. rewrite nth_error_app2 by (unfold zlength; lia).
    rewrite nth_error_repeat by (unfold zlength; lia). reflexivity.
  Qed.

  Lemma p2_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B : Z) (d idx : list Z)
         (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
         (x24 x88 : word) (jtp jsb joc jia : list byte),
    RHEAP s LB m ->
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (psi, ASI, nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (pcp, ACP, ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB -> In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    ntp mod 8 = 0 -> 8 * (zlength idx + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    bytes_at usegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    scan d = (true, idx) ->
    rw_cells usegs m ASI [CB (4 * (length idx + 3)) (SjS1Bytes.u32bytes (idx ++ [zlength d; zlength d; 0]))] ->
    rw_cells usegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))] -> rw_cells usegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells usegs m (THIS + 24) [C4 x24] ->
    rw_cells usegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88] ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] -> bv_unsigned sp <= DOC -> DOC + 16 <= B -> DOC mod 8 = 0 ->
    rw_cells usegs m ATP [CB (Z.to_nat ntp) jtp] -> rw_cells usegs m ASB [CB (Z.to_nat nsb) jsb] ->
    rw_cells usegs m AOC [CB 8192 joc] -> rw_cells usegs m AIA [CB 1024 jia] ->
    rw_cells usegs m PFMIN fmin_cells -> rw_cells usegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PS2_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
    mem_inv usegs m -> frm0 fc ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 DOC ->
    ExecF.evtF SG (SX.fp_of (SP.p_A U2)
                     (mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                THIS DOC BUF (zlength d) ASI (zlength idx) ATP (ntp / 8) ASB nsb AOC AIA)))
      (SLib.xpostH SG (gp2 SG d (idx ++ [zlength d; zlength d; 0])) MMU.hmH MMU.hmA U2
         (mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    THIS DOC BUF (zlength d) ASI (zlength idx) ATP (ntp / 8) ASB nsb AOC AIA)) m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PSTAGE2) fc None m (seg_rom usegs)).
  Proof.
    intros until jia. intros HR ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hbuf Hd Hlen Hscan HIDX
      HO8 HO16 HO24 HO40 HO56 HDOC Hspd Hdb Hda HTB HSB HOC HIA HFM HGOT HAUX Hspb HSTK Hlo1 Hlo2 Hsp16 Hsp47 HMI HFRM -> ->.
    pose proof (scan_S1OUT d idx Hscan) as S1. pose proof (s1_n _ _ _ S1) as Sn.
    unfold PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in Hlo2. atop_facts.
    assert (HAUXB : B <= 2 ^ 64 - 160) by (destruct HAUX as (av & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & Hav & _); lia).
    clear HAUX.
    pose proof (u_rng' sp) as Rsp.
    (* [comment removed for export] *)
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
    clear N12 N13 N14 N15 N16 N17 N23 N24 N25 N26 N27 N34 N35 N36 N37 N45 N46 N47 N56 N57 N67 ND.
    set (LEN := zlength d) in *. set (NN := zlength idx) in *. set (CAPT := ntp / 8).
    assert (HCAPT : 8 * CAPT = ntp) by (unfold CAPT; pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    (* [comment removed for export] *)
    assert (H_LEN : 1 <= LEN <= 1048512) by lia.
    assert (H_N : 1 <= NN <= LEN) by lia.
    assert (H_CAPT : NN + 3 <= CAPT <= 16777216) by lia.
    assert (H_CAPS : LEN + 60 <= nsb <= 16777216) by lia.
    assert (H_CAPS3 : 5 * LEN + 182 <= 3 * nsb) by lia.
    assert (H_SP : 0x7fff00000000 <= u sp <= 2 ^ 47) by lia.
    assert (H_DOC : u sp <= DOC /\ DOC + 16 <= 2 ^ 64 - 16 /\ DOC mod 8 = 0) by lia.
    assert (H_THIS : 16 <= THIS /\ THIS mod 16 = 0 /\ THIS + 96 <= ATOPM /\ THIS + 96 + 2976 <= u sp) by lia.
    assert (H_BUF : 16 <= BUF /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + 2976 <= u sp) by lia.
    assert (H_IDX : 16 <= ASI /\ ASI mod 16 = 0 /\ ASI + 4 * NN + 12 <= ATOPM /\ ASI + 4 * NN + 12 + 2976 <= u sp) by lia.
    assert (H_TB : 16 <= ATP /\ ATP mod 16 = 0 /\ ATP + 8 * CAPT <= ATOPM /\ ATP + 8 * CAPT + 2976 <= u sp) by lia.
    assert (H_SB : 16 <= ASB /\ ASB mod 16 = 0 /\ ASB + nsb <= ATOPM /\ ASB + nsb + 2976 <= u sp) by lia.
    assert (H_OC : 16 <= AOC /\ AOC mod 16 = 0 /\ AOC + 8192 <= ATOPM /\ AOC + 8192 + 2976 <= u sp) by lia.
    assert (H_IA : 16 <= AIA /\ AIA mod 16 = 0 /\ AIA + 1024 <= ATOPM /\ AIA + 1024 + 2976 <= u sp) by lia.
    assert (HU_THIS : DJ 0x10000 0xa3000 THIS 96) by (eapply DJ_sub; [exact UT | lia..]).
    assert (HU_BUF : DJ 0x10000 0xa3000 BUF (LEN + 64)) by (eapply DJ_sub; [exact UC | lia..]).
    assert (HU_IDX : DJ 0x10000 0xa3000 ASI (4 * NN + 12)) by (eapply DJ_sub; [exact UI | lia..]).
    assert (HU_TB : DJ 0x10000 0xa3000 ATP (8 * CAPT)) by (eapply DJ_sub; [exact UP | lia..]).
    assert (HU_SB : DJ 0x10000 0xa3000 ASB nsb) by (eapply DJ_sub; [exact US | lia..]).
    assert (HU_OC : DJ 0x10000 0xa3000 AOC 8192) by (eapply DJ_sub; [exact UO | lia..]).
    assert (HU_IA : DJ 0x10000 0xa3000 AIA 1024) by (eapply DJ_sub; [exact UA | lia..]).
    assert (D1 : DJ THIS 96 BUF (LEN + 64)) by (eapply DJ_sub; [exact B_tc | lia..]).
    assert (D2 : DJ THIS 96 ASI (4 * NN + 12)) by (eapply DJ_sub; [exact B_ti | lia..]).
    assert (D3 : DJ THIS 96 ATP (8 * CAPT)) by (eapply DJ_sub; [exact B_tp | lia..]).
    assert (D4 : DJ THIS 96 ASB nsb) by (eapply DJ_sub; [exact B_ts | lia..]).
    assert (D5 : DJ THIS 96 AOC 8192) by (eapply DJ_sub; [exact B_to | lia..]).
    assert (D6 : DJ THIS 96 AIA 1024) by (eapply DJ_sub; [exact B_ta | lia..]).
    assert (D7 : DJ BUF (LEN + 64) ASI (4 * NN + 12)) by (eapply DJ_sub; [exact B_ci | lia..]).
    assert (D8 : DJ BUF (LEN + 64) ATP (8 * CAPT)) by (eapply DJ_sub; [exact B_cp | lia..]).
    assert (D9 : DJ BUF (LEN + 64) ASB nsb) by (eapply DJ_sub; [exact B_cs | lia..]).
    assert (D10 : DJ BUF (LEN + 64) AOC 8192) by (eapply DJ_sub; [exact B_co | lia..]).
    assert (D11 : DJ BUF (LEN + 64) AIA 1024) by (eapply DJ_sub; [exact B_ca | lia..]).
    assert (D12 : DJ ASI (4 * NN + 12) ATP (8 * CAPT)) by (eapply DJ_sub; [exact B_ip | lia..]).
    assert (D13 : DJ ASI (4 * NN + 12) ASB nsb) by (eapply DJ_sub; [exact B_is | lia..]).
    assert (D14 : DJ ASI (4 * NN + 12) AOC 8192) by (eapply DJ_sub; [exact B_io | lia..]).
    assert (D15 : DJ ASI (4 * NN + 12) AIA 1024) by (eapply DJ_sub; [exact B_ia | lia..]).
    assert (D16 : DJ ATP (8 * CAPT) ASB nsb) by (eapply DJ_sub; [exact B_ps | lia..]).
    assert (D17 : DJ ATP (8 * CAPT) AOC 8192) by (eapply DJ_sub; [exact B_po | lia..]).
    assert (D18 : DJ ATP (8 * CAPT) AIA 1024) by (eapply DJ_sub; [exact B_pa | lia..]).
    assert (D19 : DJ ASB nsb AOC 8192) by (eapply DJ_sub; [exact B_so | lia..]).
    assert (D20 : DJ ASB nsb AIA 1024) by (eapply DJ_sub; [exact B_sa | lia..]).
    assert (D21 : DJ AOC 8192 AIA 1024) by (eapply DJ_sub; [exact B_oa | lia..]).
    clear UT UI UC UP US UO UA B_tc B_ti B_tp B_ts B_to B_ta B_ci B_cp B_cs B_co B_ca B_ip B_is B_io B_ia B_ps B_po B_pa B_so B_sa B_oa.
    (* [comment removed for export] *)
    assert (M_O40 : rw_cells usegs m (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by exact HO40.
    assert (M_TB : rw_cells usegs m ATP [CB (Z.to_nat (8 * CAPT)) jtp]) by (rewrite HCAPT; exact HTB).
    assert (M_IDX : rw_cells usegs m ASI [CB (Z.to_nat (4 * NN + 12)) (SjS1Bytes.u32bytes (idx ++ [LEN; LEN; 0]))]).
    { replace (Z.to_nat (4 * NN + 12)) with (4 * (length idx + 3))%nat by (unfold NN, zlength; lia). exact HIDX. }
    assert (M_FMIN : rw_cells usegs m 0x80f30 [C4 (Z_to_bv 64 8388608)]) by exact HFM.
    assert (M_GOT : rw_cells usegs m 0x7fb20 [C8 (Z_to_bv 64 0x1b8d0)]) by exact HGOT.
    assert (M_LO : lo <= u sp - 2976) by lia.
    (* [comment removed for export] *)
    apply (SLib.prog_evtH SG (gp2 SG d (idx ++ [LEN; LEN; 0])) gfp2 (SVX.gvc_enrich SVX.bc_enrich (wvc_ok SG 1048512 0x13768)) (gp2_frame SG d _)
             (SVX.gvc_enrich_ok SG _ SVX.bc_enrich (wvc_ok SG 1048512 0x13768) (SVX.bc_enrich_ok SG) (wvc_ok_sound SG d _ 1048512 ltac:(lia) 0x13768 ltac:(lia) d2v_img_ubsan))
             MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF U2 U2_IT 4000 true U2_hints T0 (fun _ => True)
             (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ u2_cert) (SP.itab_ranges_sound SG _) ltac:(intros TA [])
             ltac:(intros Sm [<-|[<-|[]]]; [apply SFPS_ok | apply PFFS_ok])
             ltac:(intros; exact I) ltac:(intros; unfold SP.wins_client; apply Forall_forall; intros; exact I)
             ltac:(intros E0 _ w Hw; destruct Hw) ltac:(intros; constructor) ltac:(left; reflexivity)).
    - reflexivity.
    - exact I.
    - exact I.
    - exact HMI.
    - apply rfull_mkR.
    - apply t0_regs.
    - eapply (t0_kn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ THIS DOC BUF LEN ASI NN ATP CAPT ASB nsb AOC AIA) with (m := m) (lo := lo)
        (jbuf := s1buf d) (jidx := SjS1Bytes.u32bytes (idx ++ [LEN; LEN; 0])) (jtp := jtp) (jsb := jsb) (joc := joc) (jia := jia)
        (x24 := x24) (x88 := x88); try eassumption.
      + exact (s1buf_length d).
      + exact (s1buf_zero d).
    - (* [comment removed for export] *)
      unfold SG.gholds. cbn [ST.t_ghost T0]. constructor; [|constructor; [|constructor]];
        cbn [ST.g_id ST.g_args map gp2 edenot mkEZ ev vBUF vLEN vIDX vN V nth ZLe ZL0]; rewrite !u_Z_to_bv, !Z.mod_small by lia.
      + split; [reflexivity|]. split; [lia|]. split; [exact Hd|]. rewrite bufbytes_eq.
        apply mbytes_of_bytes_at_heap; [exact Hbuf|]. intros i Hi. rewrite s1buf_length in Hi.
        rewrite u_Z_to_bv, Z.mod_small by lia. clear - HU_BUF Hi. unfold DJ in HU_BUF. lia.
      + assert (ZL3 : zlength (idx ++ [LEN; LEN; 0]) = NN + 3) by (unfold NN; rewrite zlength_app; reflexivity).
        rewrite ZL3. replace (NN + 3 - 3) with NN by lia.
        split; [reflexivity|]. split; [exact S1|]. split; [lia|]. rewrite u32bytes_eq.
        destruct (cb_bytes m _ _ _ M_IDX) as [BI LI]. rewrite Z2Nat.id in LI by lia.
        apply mbytes_of_bytes_at_heap; [exact BI|]. intros i Hi. rewrite LI in Hi.
        rewrite u_Z_to_bv, Z.mod_small by lia. clear - HU_IDX Hi. unfold DJ in HU_IDX. lia.
    - exact HMI.
    - exact HFRM.
  Qed.
End E.
