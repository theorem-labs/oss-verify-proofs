From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_w4s3b AF_huf_x2t_h1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2hb_c1_pref : forall (T DT c nb lv : Z) (dt : list Z) (w2 : list byte),
  0 <= c -> 4 * c + 8 <= zlen dt -> Forall isbyte dt -> x2pref T c dt -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 -> length w2 = 2%nat ->
  x2pref T (c + 1) (map bv_unsigned (replay1 DT (replay1 DT (map (Z_to_bv 8) dt) (DT + 4 * c + 4) w2) (DT + 4 * c + 6)
                                       (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c nb lv dt w2 HC HL HBY PRE HNB HT12 HLV LW u Hu. unfold c2ok.
  assert (HU : u < c \/ u = c) by lia. destruct HU as [HU|HU].
  - destruct (x2hb_znth_old dt (4 * u + 6) ltac:(lia) HBY) as [N6 R6].
    destruct (x2hb_znth_old dt (4 * u + 7) ltac:(lia) HBY) as [N7 R7].
    rewrite (x2hb_znth_map _ (4 * u + 6) (Z_to_bv 8 (Znth (4 * u + 6) dt))).
    2: { rewrite x2hb_r1_out by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         rewrite x2hb_r1_out by (rewrite ?length_map, ?LW; lia). exact N6. }
    rewrite (x2hb_znth_map _ (4 * u + 7) (Z_to_bv 8 (Znth (4 * u + 7) dt))).
    2: { rewrite x2hb_r1_out by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         rewrite x2hb_r1_out by (rewrite ?length_map, ?LW; lia). exact N7. }
    rewrite !x2hb_bv8, !Z.mod_small by lia. apply PRE; lia.
  - subst u.
    rewrite (x2hb_znth_map _ (4 * c + 6) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (nb + 256 * lv))))).
    2: { rewrite x2hb_r1_in by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         replace (Z.to_nat (DT + (4 * c + 6) - (DT + 4 * c + 6))) with O by lia. reflexivity. }
    rewrite (x2hb_znth_map _ (4 * c + 7) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (nb + 256 * lv)) ≫ 8))).
    2: { rewrite x2hb_r1_in by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         replace (Z.to_nat (DT + (4 * c + 7) - (DT + 4 * c + 6))) with 1%nat by lia. reflexivity. }
    rewrite !x2hb_bv8, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    rewrite (Z.mod_small (nb + 256 * lv)) by (split; [lia|]; apply (Z.lt_le_trans _ (2 ^ 16)); [lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

Ltac x2hb_ev2 tb sv :=
  lazymatch goal with |- edenot ?E (EAlu ALU_SRL (EAlu ALU_OR ?X ?Y) (ELit ?sh)) = _ =>
    let RS := fresh "RS" in
    lazymatch X with EMd M_MUL (ELit 256) (EVar ?j) => kx_range (EVar j) RS end;
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let EX := fresh "EX" in let EY := fresh "EY" in
      pose proof (ez_ok zv E (kE_atoms zv xs) X) as EX;
      pose proof (ez_ok zv E (kE_atoms zv xs) Y) as EY;
      let na := eval vm_compute in (length zv) in
      cbv [ez] in EX, EY; change (length zv) with na in EX, EY; cbv [nth Nat.ltb Nat.leb] in EX, EY;
      change (edenot E (EAlu ALU_SRL (EAlu ALU_OR X Y) (ELit sh)))
        with (alu64 ALU_SRL (alu64 ALU_OR (edenot E X) (edenot E Y)) (Z_to_bv 64 sh));
      rewrite EX, EY; clear EX EY
    end;
    lazymatch type of RS with _ <= bv_unsigned ?w <= _ =>
      let s2 := fresh "s2" in set (s2 := bv_unsigned w) in *; clearbody s2;
      rewrite alu_or; unfold v_or; rewrite srl_lit_ez; f_equal;
      rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      rewrite (Z.mod_small (256 * s2)) by lia;
      rewrite (Z.mod_small (65536 * tb + sv + 33554432)) by lia;
      rewrite Z.lor_comm;
      rewrite Z.mod_small by (apply (x2hb_w_range _ _ tb sv s2); lia);
      change (2 ^ (16 mod 64)) with 65536;
      apply (x2hb_w_hi _ _ tb sv s2); lia
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Section C1.
Variables (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : amem) (SPF DT SYM pos cnt bg nb T mtl : Z) (syb j0 : list byte).
Hypothesis HY : x2hb_hyps RNG SPF DT SYM mtl.
Hypothesis UDT : unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))).
Hypothesis USY : unpoisoned m0 SYM (SYM + 256).
Hypothesis ART0 : x2hb_art m0.
Hypothesis HP : 0 <= pos.
Hypothesis HB : 0 <= bg.
Hypothesis HBC : bg + cnt <= 256.
Hypothesis HC : 1 <= cnt.
Hypothesis HNB : 0 <= nb <= T.
Hypothesis HT : 1 <= T <= 12.
Hypothesis HM : 1 <= mtl <= 12.
Hypothesis HROOM : pos + cnt <= 2 ^ mtl.

Definition C1POST := x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + cnt).

Definition C1S (k : Z) (m : amem) (y6 y7 y28 y29 y30 y31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) y6 y7 x8 x9 (Z_to_bv 64 (DT + 4 * pos + 4 + 4 * k))
          (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt))) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (DT + 4 * pos + 4 + 4 * k))
          (Z_to_bv 64 5) (Z_to_bv 64 (-1)) (Z_to_bv 64 (65536 * nb + 16777216))
          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
     F (Z_to_bv 64 0x8d820) fc None m (seg_rom bsegs).

Ltac c1_es := unfold estart; cbn [a_base a_off]; w4ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite Z.mod_small by lia; lia.

Lemma c1l1_body : forall k m dt y6 y7 y28 y29 y30 y31,
  0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (pos + k) dt ->
  (forall m' dt' z6 z7 z28 z29 z30 z31, k + 1 < cnt ->
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + (k + 1)) dt' ->
     evtF bsegs RNG C1POST (C1S (k + 1) m' z6 z7 z28 z29 z30 z31)) ->
  evtF bsegs RNG C1POST (C1S k m y6 y7 y28 y29 y30 y31).
Proof.
  intros k m dt y6 y7 y28 y29 y30 y31 HK I PRE KH.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  assert (USYm : unpoisoned m SYM (SYM + 256)) by (eapply x2hb_unp_syM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN.
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  unfold C1S, ASHOFF.
  assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
  - kx_runFm [0x8d820; 0x8dbd8] 60%nat
      [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
       KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 1 256; KZRange k 0 255; KZRange (bg + k) 0 255;
       KZRange (cnt - k - 2) 0 255; KZRange (2 ^ mtl - pos - k - 1) 0 4096; KZRange nb 0 12; KZWr (DT + 4 * pos + 4 + 4 * k) 4]
      [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)]
      [(DT + 4 * pos + 4 + 4 * k, 4); (SYM + bg + k, 1)].
    1: (unfold KHIGH; lia).
    kx_post_regs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
     lazymatch lg with [SE ?a1 ?w1 ?v1; SE ?a2 ?w2 ?v2] =>
      assert (EA1 : estart E a1 = DT + 4 * pos + 4 * k + 6) by c1_es;
      assert (EA2 : estart E a2 = DT + 4 * pos + 4 * k + 4) by c1_es;
      assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256)) by (w4ez; reflexivity);
      pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
      pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
      pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
      pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
      pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
      pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM';
      cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
      rewrite ?EA1, ?EA2 in SYB', FR', MI', MU';
      cbn [replay] in DTC'; rewrite EA1, EA2, EV1 in DTC'
     end
    end.
    destruct WDT as (_ & _ & WV).
    specialize (SYB' ltac:(repeat split; lia)).
    specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
    specialize (MI' ltac:(repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
      lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
    specialize (MU' ltac:(repeat split; cbn; lia)).
    replace (DT + 4 * pos + 4 * k + 4) with (DT + 4 * (pos + k) + 4) in DTC' by lia.
    replace (DT + 4 * pos + 4 * k + 6) with (DT + 4 * (pos + k) + 6) in DTC' by lia.
    replace (nb + 256) with (nb + 256 * 1) in DTC' by lia.
    lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
    assert (PRE' : x2pref T (pos + (k + 1)) (map bv_unsigned bs1)).
    { replace (pos + (k + 1)) with (pos + k + 1) by lia. unfold bs1.
      apply x2hb_c1_pref; try assumption; try lia; apply length_wtlb. }
    destruct (x2hb_dt_of bs1) as [DTE DTBY'].
    rewrite <- DTE in DTC'.
    assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
      by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
    unfold C1S, ASHOFF in KH.
    replace (DT + (4 * pos + 4 * k) + 8) with (DT + 4 * pos + 4 + 4 * (k + 1)) by lia.
    replace (k + (SYM + bg) + 1) with (SYM + bg + (k + 1)) by lia.
    eapply KH; [lia | | exact PRE'].
    unfold X2HBFR. eapply XHb_close; eassumption.
  - rewrite <- CK.
    kx_runFm [0x8d820; 0x8dbd8] 60%nat
      [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
       KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange k 0 255; KZRange (bg + k) 0 255;
       KZRange (2 ^ mtl - pos - k - 1) 0 4096; KZRange nb 0 12; KZWr (DT + 4 * pos + 4 + 4 * k) 4]
      [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)]
      [(DT + 4 * pos + 4 + 4 * k, 4); (SYM + bg + k, 1)].
    1: (unfold KHIGH; lia).
    kx_post_regs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
     lazymatch lg with [SE ?a1 ?w1 ?v1; SE ?a2 ?w2 ?v2] =>
      assert (EA1 : estart E a1 = DT + 4 * pos + 4 * k + 6) by c1_es;
      assert (EA2 : estart E a2 = DT + 4 * pos + 4 * k + 4) by c1_es;
      assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256)) by (w4ez; reflexivity);
      pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
      pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
      pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
      pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
      pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
      pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM';
      cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
      rewrite ?EA1, ?EA2 in SYB', FR', MI', MU';
      cbn [replay] in DTC'; rewrite EA1, EA2, EV1 in DTC'
     end
    end.
    destruct WDT as (_ & _ & WV).
    specialize (SYB' ltac:(repeat split; lia)).
    specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
    specialize (MI' ltac:(repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
      lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
    specialize (MU' ltac:(repeat split; cbn; lia)).
    replace (DT + 4 * pos + 4 * k + 4) with (DT + 4 * (pos + k) + 4) in DTC' by lia.
    replace (DT + 4 * pos + 4 * k + 6) with (DT + 4 * (pos + k) + 6) in DTC' by lia.
    replace (nb + 256) with (nb + 256 * 1) in DTC' by lia.
    lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
    assert (PRE' : x2pref T (pos + (k + 1)) (map bv_unsigned bs1)).
    { replace (pos + (k + 1)) with (pos + k + 1) by lia. unfold bs1.
      apply x2hb_c1_pref; try assumption; try lia; apply length_wtlb. }
    destruct (x2hb_dt_of bs1) as [DTE DTBY'].
    rewrite <- DTE in DTC'.
    assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
      by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
    rewrite CK in PRE'. unfold C1POST.
    eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma c1l1_loop : forall n k m dt y6 y7 y28 y29 y30 y31,
  Z.of_nat n = cnt - k -> 0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + k) dt -> evtF bsegs RNG C1POST (C1S k m y6 y7 y28 y29 y30 y31).
Proof.
  induction n as [|n IH]; intros k m dt y6 y7 y28 y29 y30 y31 HN HK I PRE; [lia|].
  eapply c1l1_body; [exact HK | exact I | exact PRE |].
  intros m' dt' z6 z7 z28 z29 z30 z31 HK' I' PRE'. eapply IH; [lia | lia | exact I' | exact PRE'].
Qed.

Lemma c1l1_head : forall m dt x7 x28 x29 x30 x31 bs,
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG C1POST (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                           SPF DT SYM pos bg cnt nb bs 1 1 1 0x8d7f8).
Proof.
  intros m dt x7 x28 x29 x30 x31 bs I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  kx_runFm [0x8d820; 0x8dbd8] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256]
    (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  kx_post_regs. cbn [mem_denot].
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?v6 ?v7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?v28 ?v29 ?v30 ?v31) _ _ _ _ _ _) =>
    pose proof (c1l1_loop (Z.to_nat cnt) 0 m dt v6 v7 v28 v29 v30 v31 ltac:(lia) ltac:(lia) I ltac:(rewrite Z.add_0_r; exact PRE)) as L0
  end.
  unfold C1S, ASHOFF in L0. rewrite !Z.mul_0_r, !Z.add_0_r in L0.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?g16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  lazymatch type of L0 with evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?l16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace l16 with g16 in L0 by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity)
  end end.
  exact L0.
Qed.

Variable bs : Z.
Hypothesis HBS : 0 <= bs < 256.

Definition C2S (k : Z) (m : amem) (y6 y7 y28 y29 y30 y31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) y6 y7 x8 x9 (Z_to_bv 64 (DT + 4 * pos + 4 + 4 * k))
          (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt))) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (DT + 4 * pos + 4 + 4 * k))
          (Z_to_bv 64 (65536 * nb + bs + 33554432)) (Z_to_bv 64 4) (Z_to_bv 64 (-1))
          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
     F (Z_to_bv 64 0x8da0c) fc None m (seg_rom bsegs).

Lemma c1l2_body : forall k m dt y6 y7 y28 y29 y30 y31,
  0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (pos + k) dt ->
  (forall m' dt' z6 z7 z28 z29 z30 z31, k + 1 < cnt ->
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + (k + 1)) dt' ->
     evtF bsegs RNG C1POST (C2S (k + 1) m' z6 z7 z28 z29 z30 z31)) ->
  evtF bsegs RNG C1POST (C2S k m y6 y7 y28 y29 y30 y31).
Proof.
  intros k m dt y6 y7 y28 y29 y30 y31 HK I PRE KH.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  assert (USYm : unpoisoned m SYM (SYM + 256)) by (eapply x2hb_unp_syM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN.
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  unfold C2S, ASHOFF.
  assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
  - kx_runFm [0x8da0c; 0x8dbd8] 60%nat
      [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
       KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 1 256; KZRange k 0 255; KZRange (bg + k) 0 255;
       KZRange (cnt - k - 2) 0 255; KZRange (2 ^ mtl - pos - k - 1) 0 4096; KZRange nb 0 12; KZRange bs 0 255;
       KZWr (DT + 4 * pos + 4 + 4 * k) 4]
      [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)]
      [(DT + 4 * pos + 4 + 4 * k, 4); (SYM + bg + k, 1)].
    1: (unfold KHIGH; lia).
    kx_post_regs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
     lazymatch lg with [SE ?a1 ?w1 ?v1; SE ?a2 ?w2 ?v2] =>
      assert (EA1 : estart E a1 = DT + 4 * pos + 4 * k + 6) by c1_es;
      assert (EA2 : estart E a2 = DT + 4 * pos + 4 * k + 4) by c1_es;
      assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256 * 2)) by (x2hb_ev2 nb bs);
      pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
      pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
      pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
      pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
      pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
      pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM';
      cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
      rewrite ?EA1, ?EA2 in SYB', FR', MI', MU';
      cbn [replay] in DTC'; rewrite EA1, EA2, EV1 in DTC'
     end
    end.
    destruct WDT as (_ & _ & WV).
    specialize (SYB' ltac:(repeat split; lia)).
    specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
    specialize (MI' ltac:(repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
      lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
    specialize (MU' ltac:(repeat split; cbn; lia)).
    replace (DT + 4 * pos + 4 * k + 4) with (DT + 4 * (pos + k) + 4) in DTC' by lia.
    replace (DT + 4 * pos + 4 * k + 6) with (DT + 4 * (pos + k) + 6) in DTC' by lia.
    lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
    assert (PRE' : x2pref T (pos + (k + 1)) (map bv_unsigned bs1)).
    { replace (pos + (k + 1)) with (pos + k + 1) by lia. unfold bs1.
      apply x2hb_c1_pref; try assumption; try lia; apply length_wtlb. }
    destruct (x2hb_dt_of bs1) as [DTE DTBY'].
    rewrite <- DTE in DTC'.
    assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
      by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
    unfold C2S, ASHOFF in KH.
    replace (DT + (4 * pos + 4 * k) + 8) with (DT + 4 * pos + 4 + 4 * (k + 1)) by lia.
    replace (k + (SYM + bg) + 1) with (SYM + bg + (k + 1)) by lia.
    eapply KH; [lia | | exact PRE'].
    unfold X2HBFR. eapply XHb_close; eassumption.
  - rewrite <- CK.
    kx_runFm [0x8da0c; 0x8dbd8] 60%nat
      [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
       KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange k 0 255; KZRange (bg + k) 0 255;
       KZRange (2 ^ mtl - pos - k - 1) 0 4096; KZRange nb 0 12; KZRange bs 0 255; KZWr (DT + 4 * pos + 4 + 4 * k) 4]
      [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 4 * k, 4)]
      [(DT + 4 * pos + 4 + 4 * k, 4); (SYM + bg + k, 1)].
    1: (unfold KHIGH; lia).
    kx_post_regs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
     lazymatch lg with [SE ?a1 ?w1 ?v1; SE ?a2 ?w2 ?v2] =>
      assert (EA1 : estart E a1 = DT + 4 * pos + 4 * k + 6) by c1_es;
      assert (EA2 : estart E a2 = DT + 4 * pos + 4 * k + 4) by c1_es;
      assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256 * 2)) by (x2hb_ev2 nb bs);
      pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
      pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
      pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
      pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
      pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
      pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM';
      cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
      rewrite ?EA1, ?EA2 in SYB', FR', MI', MU';
      cbn [replay] in DTC'; rewrite EA1, EA2, EV1 in DTC'
     end
    end.
    destruct WDT as (_ & _ & WV).
    specialize (SYB' ltac:(repeat split; lia)).
    specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
    specialize (MI' ltac:(repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
      lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
    specialize (MU' ltac:(repeat split; cbn; lia)).
    replace (DT + 4 * pos + 4 * k + 4) with (DT + 4 * (pos + k) + 4) in DTC' by lia.
    replace (DT + 4 * pos + 4 * k + 6) with (DT + 4 * (pos + k) + 6) in DTC' by lia.
    lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
    assert (PRE' : x2pref T (pos + (k + 1)) (map bv_unsigned bs1)).
    { replace (pos + (k + 1)) with (pos + k + 1) by lia. unfold bs1.
      apply x2hb_c1_pref; try assumption; try lia; apply length_wtlb. }
    destruct (x2hb_dt_of bs1) as [DTE DTBY'].
    rewrite <- DTE in DTC'.
    assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
      by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
    rewrite CK in PRE'. unfold C1POST.
    eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma c1l2_loop : forall n k m dt y6 y7 y28 y29 y30 y31,
  Z.of_nat n = cnt - k -> 0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + k) dt -> evtF bsegs RNG C1POST (C2S k m y6 y7 y28 y29 y30 y31).
Proof.
  induction n as [|n IH]; intros k m dt y6 y7 y28 y29 y30 y31 HN HK I PRE; [lia|].
  eapply c1l2_body; [exact HK | exact I | exact PRE |].
  intros m' dt' z6 z7 z28 z29 z30 z31 HK' I' PRE'. eapply IH; [lia | lia | exact I' | exact PRE'].
Qed.

Lemma c1l2_head : forall m dt x7 x28 x29 x30 x31,
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG C1POST (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                           SPF DT SYM pos bg cnt nb bs 2 1 1 0x8d7f8).
Proof.
  intros m dt x7 x28 x29 x30 x31 I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  kx_runFm [0x8da0c; 0x8dbd8] 40%nat
    [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256; KZRange bs 0 255; KZRange nb 0 12]
    (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  kx_post_regs. cbn [mem_denot].
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ ?v6 ?v7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?v28 ?v29 ?v30 ?v31) _ _ _ _ _ _) =>
    pose proof (c1l2_loop (Z.to_nat cnt) 0 m dt v6 v7 v28 v29 v30 v31 ltac:(lia) ltac:(lia) I ltac:(rewrite Z.add_0_r; exact PRE)) as L0
  end.
  unfold C2S, ASHOFF in L0. rewrite !Z.mul_0_r, !Z.add_0_r in L0.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?g17 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  lazymatch type of L0 with evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?l17 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace l17 with g17 in L0 by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity)
  end end.
  exact L0.
Qed.
End C1.

Lemma c1_zero : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bg <= 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 pos)
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg 0 nb bs lvl 1 1 0x8d7f8).
Proof.
  intros until dt. intros HY HL HB I PRE.
  open_hyhb HY. open_xhb I. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  destruct HL as [HL|HL]; subst lvl.
  all: kx_runFm [0x8dbd8] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1)]
         (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR | eassumption ..].
Qed.

Lemma x2hb_c1 : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m0 SYM (SYM + 256) -> x2hb_art m0 ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 ->
  pos + cnt <= 2 ^ mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl 1 1 0x8d7f8).
Proof.
  intros until dt. intros HY UDT USY ART0 HP HB HC0 HBC HNB HT HM HROOM HL HBS I PRE.
  assert (CZ : cnt = 0 \/ 1 <= cnt) by lia. destruct CZ as [CZ|CZ].
  - subst cnt. rewrite Z.add_0_r. eapply c1_zero; [exact HY | exact HL | lia | exact I | exact PRE].
  - destruct HL as [HL|HL]; subst lvl.
    + eapply c1l1_head; first [eassumption | lia].
    + eapply c1l2_head; first [eassumption | lia].
Qed.
End CANSEC1.
