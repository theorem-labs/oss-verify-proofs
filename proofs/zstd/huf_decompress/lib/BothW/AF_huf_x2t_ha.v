From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_w4s3b AF_huf_x2t_h1 AF_huf_x2t_hd.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2hb_c2_pref : forall (T DT c nb lv : Z) (dt : list Z) (w2 w4 : list byte),
  0 <= c -> 4 * c + 12 <= zlen dt -> Forall isbyte dt -> x2pref T c dt -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 ->
  length w2 = 2%nat -> length w4 = 2%nat ->
  x2pref T (c + 2) (map bv_unsigned
    (replay1 DT (replay1 DT (replay1 DT (replay1 DT (map (Z_to_bv 8) dt) (DT + 4 * c + 4) w2) (DT + 4 * c + 6)
                                          (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))
                            (DT + 4 * c + 8) w4)
             (DT + 4 * c + 10) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c nb lv dt w2 w4 HC HL HBY PRE HNB HT HLV L2 L4.
  set (b1 := replay1 DT (replay1 DT (map (Z_to_bv 8) dt) (DT + 4 * c + 4) w2) (DT + 4 * c + 6)
                     (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))).
  assert (P1 : x2pref T (c + 1) (map bv_unsigned b1)) by (unfold b1; apply x2hb_c1_pref; try assumption; lia).
  destruct (x2hb_dt_of b1) as [E1 B1].
  rewrite <- E1.
  replace (DT + 4 * c + 8) with (DT + 4 * (c + 1) + 4) by lia.
  replace (DT + 4 * c + 10) with (DT + 4 * (c + 1) + 6) by lia.
  replace (c + 2) with (c + 1 + 1) by lia.
  apply x2hb_c1_pref; try assumption; try lia.
  unfold b1. rewrite length_map, !replay1_length, length_map. lia.
Qed.

Ltac x2hb_fpre := unfold flat, estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  cbn [Z.of_N]; change (2 ^ (3 mod 64)) with 8 in *.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2hb_sh0 : forall (m : amem) lo hi G, unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi ->
  0 <= ASHOFF + G -> ASHOFF + G + 1 <= 2 ^ 64 -> bytes_at bsegs m (ASHOFF + G) [Z_to_bv 8 0].
Proof.
  intros m lo hi G U H1 H2 H3 H4. split; [exact H3|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error]. unfold mrd. replace (ASHOFF + G + Z.of_nat 0) with (ASHOFF + G) by lia.
  erewrite unpoisoned_full; [reflexivity | exact U | lia | lia].
Qed.

Section C2.
Variables (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : amem) (SPF DT SYM pos cnt bg nb T mtl bs lvl : Z) (syb j0 : list byte).
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
Hypothesis HROOM : pos + 2 * cnt <= 2 ^ mtl.
Hypothesis HBS : 0 <= bs < 256.
Hypothesis HL : lvl = 1 \/ lvl = 2.

Definition C2POST := x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 2 * cnt).

Definition C2S (k : Z) (m : amem) (y8 y9 y17 y18 y19 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 1) (Z_to_bv 64 (-5)) y8 y9
          (Z_to_bv 64 (DT + 4 * pos + 4 + 8 * k)) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt)))
          (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (DT + 4 * pos + 4 + 8 * k)) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) y17
          y18 y19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (-1)) (Z_to_bv 64 (65536 * nb + 16777216 * lvl))
          (Z_to_bv 64 (ASHOFF + (DT + 4 * pos + 4 + 8 * k) / 8)) (Z_to_bv 64 (-9)))
     F (Z_to_bv 64 (APX2HB + 148)) fc None m (seg_rom bsegs).

Ltac c2_es := unfold estart; cbn [a_base a_off]; w4ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite Z.mod_small by lia; lia.

Ltac c2_zl :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR; Z.div_mod_to_equations; lia.

Ltac c2_clrk h :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR h.

Ltac c2_zs :=
  let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in let CK := ident:(CK) in
  let P2 := ident:(P2) in
  clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia.

Ltac c2_zf :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in
  clear - SHD DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia.

Ltac c2_flat := lazymatch goal with |- flat _ _ _ /\ _ =>
  x2hb_fpre; repeat (rewrite (Z.mod_small _ (2 ^ 64)) by c2_zs); first [ c2_zf | c2_zl ] end.

Ltac c2_acc :=
  lazymatch goal with |- accP ?RN ?E (?a, ?n) =>
    unfold accP; cbn [fst snd];
    rewrite (flat_u E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                               unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c2_zl);
    unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    lazymatch goal with R : rng RN ?lo 1 |- _ => let R3 := fresh "R3" in destruct R as (_ & _ & R3); apply R3; c2_zl end
  end.

Ltac c2_region :=
  lazymatch goal with |- region_ok ?sg ?mm ?E (zr_reg ?r) =>
    let r' := eval vm_compute in (zr_reg r) in change (region_ok sg mm E r'); unfold region_ok; cbn [fst snd];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      unfold estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      split; [c2_zl|]; split; [c2_zl|];
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3;
      lazymatch goal with |- _ (Z_to_bv 64 ?x) <> None =>
        replace x with (A + Z.of_nat 0) by (c2_clrk Hi; Z.div_mod_to_equations; lia) end;
      rewrite SH3; discriminate
    end
  end.

Ltac c2_kword :=
  lazymatch goal with |- kentry_ok ?sg ?E ?mm (zk_ent (ZKWord ?za 1 (ZL 0))) =>
    let k' := eval vm_compute in (zk_ent (ZKWord za 1 (ZL 0))) in change (kentry_ok sg E mm k'); cbn [kentry_ok];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ /\ flat E ?a _ /\ _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      let FL := fresh "FL" in
      assert (FL : flat E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                                   unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c2_zl);
      split; [lia|]; split; [exact FL|];
      let FU := fresh "FU" in pose proof (flat_u E a 1 FL) as FU;
      replace (adenot E a) with (Z_to_bv 64 (A + Z.of_nat 0));
      [ rewrite rdn_unfold; cbv beta iota;
        specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3; rewrite SH3;
        rewrite rdn_unfold; cbv beta iota; cbn [edenot]; reflexivity
      | apply bv_eq; rewrite FU; unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c2_zl ]
    end
  end.

Ltac c2_side := first [ lazymatch goal with |- KHIGH + 112 <= _ <= _ => unfold KHIGH; lia end
                      | c2_flat | c2_acc | c2_region | c2_kword ].

Ltac c2_evh := w4ez; first [ f_equal; lia
                           | apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
                             rewrite ?Z.mod_small by lia; lia ].

Ltac c2_bveq := apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity.

Ltac c2_feq := first [ reflexivity | c2_bveq | f_equal; lia ].

Ltac c2_setup :=
  let I := ident:(I) in let m := ident:(m) in let k := ident:(k) in let HY' := ident:(HY') in
  let KLO := ident:(KLO) in let RSDT := ident:(RSDT) in let RSSY := ident:(RSSY) in let DTLEN := ident:(DTLEN) in
  let SYLEN := ident:(SYLEN) in let DTC := ident:(DTC) in let ABD := ident:(ABD) in let DTL := ident:(DTL) in
  let DTH := ident:(DTH) in let HK := ident:(HK) in let CK := ident:(CK) in let UDTm := ident:(UDTm) in
  let P2 := ident:(P2) in let LDT := ident:(LDT) in let LSY := ident:(LSY) in let WDT := ident:(WDT) in
  let SHD := ident:(SHD) in let qc := ident:(qc) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  let RQ := ident:(RQ) in let SH0 := ident:(SH0) in let dt := ident:(dt) in let USYm := ident:(USYm) in
  pose proof HY as HY'; open_hyhb HY'; open_xhb I;
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption);
  assert (USYm : unpoisoned m SYM (SYM + 256)) by (eapply x2hb_unp_syM; eassumption);
  unfold KHIGH in KLO; unfold shspan in RSDT, RSSY;
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN);
  assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN;
  pose proof (proj2 DTC) as WDT; rewrite LDT in WDT;
  pose proof (ablk_shad_disj _ _ ABD ltac:(lia)) as SHD; rewrite !shad_div in SHD;
  unfold C2S;
  remember ((DT + 4 * pos + 4 + 8 * k) / 8) as qc eqn:HQ;
  assert (QR : 512 <= qc <= 2 ^ 44) by (subst qc; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia);
  assert (RQ : rng RNG (ASHOFF + qc) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst qc; clear - DTL DTH HP HK CK HROOM P2;
        Z.div_mod_to_equations; lia);
  assert (SH0 : bytes_at bsegs m (ASHOFF + qc) [Z_to_bv 8 0])
    by (subst qc; apply x2hb_sh0 with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia ..]);
  unfold ASHOFF in *;
  let v := eval vm_compute in (APX2HB + 148) in change (APX2HB + 148) with v.

Ltac c2_log :=
  let k := ident:(k) in let EA1 := ident:(EA1) in let EA2 := ident:(EA2) in let EA3 := ident:(EA3) in
  let EA4 := ident:(EA4) in let EV1 := ident:(EV1) in let EV3 := ident:(EV3) in let DTC := ident:(DTC) in
  let KXLF := ident:(KXLF) in let SYB := ident:(SYB) in let FR := ident:(FR) in let MI := ident:(MI) in
  let MU := ident:(MU) in let WM := ident:(WM) in let DTC' := ident:(DTC') in let SYB' := ident:(SYB') in
  let FR' := ident:(FR') in let MI' := ident:(MI') in let MU' := ident:(MU') in let WM' := ident:(WM') in
  let WDT := ident:(WDT) in let WV := ident:(WV) in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let DTE := ident:(DTE) in let DTBY' := ident:(DTBY') in let LB1 := ident:(LB1) in let DTLEN := ident:(DTLEN) in
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
   lazymatch lg with [SE ?a1 ?w1 ?v1; SE ?a2 ?w2 ?v2; SE ?a3 ?w3 ?v3; SE ?a4 ?w4 ?v4] =>
    assert (EA1 : estart E a1 = DT + 4 * pos + 8 * k + 10) by c2_es;
    assert (EA2 : estart E a2 = DT + 4 * pos + 8 * k + 8) by c2_es;
    assert (EA3 : estart E a3 = DT + 4 * pos + 8 * k + 6) by c2_es;
    assert (EA4 : estart E a4 = DT + 4 * pos + 8 * k + 4) by c2_es;
    assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256 * lvl)) by c2_evh;
    assert (EV3 : edenot E v3 = Z_to_bv 64 (nb + 256 * lvl)) by c2_evh;
    pose proof (kx_u8arr_replay bsegs E mm lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E mm lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E mm lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 mm lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 mm lg WM) as WM';
    cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
    rewrite ?EA1, ?EA2, ?EA3, ?EA4 in SYB', FR', MI', MU';
    cbn [replay] in DTC'; rewrite EA1, EA2, EA3, EA4, EV1, ?EV3 in DTC'
   end
  end;
  destruct WDT as (_ & _ & WV);
  specialize (SYB' ltac:(repeat split; lia));
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia));
  specialize (MI' ltac:(repeat split; let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end));
  specialize (MU' ltac:(repeat split; cbn; lia));
  replace (DT + 4 * pos + 8 * k + 4) with (DT + 4 * (pos + 2 * k) + 4) in DTC' by lia;
  replace (DT + 4 * pos + 8 * k + 6) with (DT + 4 * (pos + 2 * k) + 6) in DTC' by lia;
  replace (DT + 4 * pos + 8 * k + 8) with (DT + 4 * (pos + 2 * k) + 8) in DTC' by lia;
  replace (DT + 4 * pos + 8 * k + 10) with (DT + 4 * (pos + 2 * k) + 10) in DTC' by lia;
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end;
  assert (PRE' : x2pref T (pos + 2 * k + 2) (map bv_unsigned bs1))
    by (unfold bs1; apply x2hb_c2_pref; try assumption; try lia; apply length_wtlb);
  destruct (x2hb_dt_of bs1) as [DTE DTBY'];
  rewrite <- DTE in DTC';
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).

Ltac c2_next :=
  let k := ident:(k) in let XH' := ident:(XH') in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let KH := ident:(KH) in let KN := ident:(KN) in let QN := ident:(QN) in let HQ := ident:(HQ) in
  let qc := ident:(qc) in
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ ?v8 ?v9 _ _ _ _ _ _ _ ?v17 ?v18 ?v19 _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
    assert (XH' : XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 (map bv_unsigned bs1) mm)
      by (unfold X2HBFR; eapply XHb_close; eassumption);
    replace (pos + 2 * k + 2) with (pos + 2 * (k + 1)) in PRE' by lia;
    pose proof (KH mm (map bv_unsigned bs1) v8 v9 v17 v18 v19 XH' PRE') as KN
  end;
  assert (QN : (DT + 4 * pos + 4 + 8 * (k + 1)) / 8 = qc + 1)
    by (rewrite HQ; replace (DT + 4 * pos + 4 + 8 * (k + 1)) with ((DT + 4 * pos + 4 + 8 * k) + 1 * 8) by lia;
        apply Z.div_add; lia);
  unfold C2S, ASHOFF in KN; rewrite QN in KN;
  lazymatch type of KN with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
    replace S1 with S0; [exact KN|] end end;
  f_equal; try f_equal; c2_feq.

Lemma c2_more : forall k m dt y8 y9 y17 y18 y19,
  0 <= k -> k + 1 < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 2 * k) dt ->
  (forall m' dt' z8 z9 z17 z18 z19,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 2 * (k + 1)) dt' ->
     evtF bsegs RNG C2POST (C2S (k + 1) m' z8 z9 z17 z18 z19)) ->
  evtF bsegs RNG C2POST (C2S k m y8 y9 y17 y18 y19).
Proof.
  intros k m dt y8 y9 y17 y18 y19 HK CK I PRE KH.
  c2_setup.
  pose proof HL as HL0. destruct HL0 as [HL1|HL1]; rewrite HL1.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 148) in let p2 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2] 60%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 1 256; KZRange k 0 255;
          KZRange (bg + k) 0 255; KZRange (cnt - k - 2) 0 255; KZRange (2 ^ mtl - pos - 2 * k - 2) 0 4096;
          KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44); KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 8 * k) 8]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 8 * k, 8); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 8 * k, 8)]
         [(DT + 4 * pos + 4 + 8 * k, 8); (SYM + bg + k, 1)].
  all: try c2_side.
  all: kx_post_regs.
  all: c2_log.
  all: c2_next.
Qed.

Lemma c2_last : forall k m dt y8 y9 y17 y18 y19,
  0 <= k -> k + 1 = cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 2 * k) dt -> evtF bsegs RNG C2POST (C2S k m y8 y9 y17 y18 y19).
Proof.
  intros k m dt y8 y9 y17 y18 y19 HK CK I PRE.
  c2_setup.
  rewrite <- CK.
  pose proof HL as HL0. destruct HL0 as [HL1|HL1]; rewrite HL1.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 148) in let p2 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2] 60%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange k 0 255; KZRange (bg + k) 0 255;
          KZRange (2 ^ mtl - pos - 2 * k - 2) 0 4096; KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44);
          KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 8 * k) 8]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 8 * k, 8); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 8 * k, 8)]
         [(DT + 4 * pos + 4 + 8 * k, 8); (SYM + bg + k, 1)].
  all: try c2_side.
  all: kx_post_regs.
  all: c2_log.
  all: unfold C2POST; replace (pos + 2 * cnt) with (pos + 2 * k + 2) by lia;
       eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma c2_body : forall k m dt y8 y9 y17 y18 y19,
  0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 2 * k) dt ->
  (forall m' dt' z8 z9 z17 z18 z19, k + 1 < cnt ->
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 2 * (k + 1)) dt' ->
     evtF bsegs RNG C2POST (C2S (k + 1) m' z8 z9 z17 z18 z19)) ->
  evtF bsegs RNG C2POST (C2S k m y8 y9 y17 y18 y19).
Proof.
  intros k m dt y8 y9 y17 y18 y19 HK I PRE KH.
  assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
  - eapply c2_more; [lia | exact CK | exact I | exact PRE |].
    intros m' dt' z8 z9 z17 z18 z19 I' PRE'. eapply KH; [exact CK | exact I' | exact PRE'].
  - eapply c2_last; [lia | exact CK | exact I | exact PRE].
Qed.

Lemma c2_loop : forall n k m dt y8 y9 y17 y18 y19,
  Z.of_nat n = cnt - k -> 0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 2 * k) dt -> evtF bsegs RNG C2POST (C2S k m y8 y9 y17 y18 y19).
Proof.
  induction n as [|n IH]; intros k m dt y8 y9 y17 y18 y19 HN HK I PRE; [lia|].
  eapply c2_body; [exact HK | exact I | exact PRE |].
  intros m' dt' z8 z9 z17 z18 z19 HK' I' PRE'. eapply IH; [lia | lia | exact I' | exact PRE'].
Qed.

Ltac c2_hfeq := first [ reflexivity | c2_bveq | f_equal; lia
                      | f_equal; rewrite Z.mod_small by lia; change (2 ^ (3 mod 64)) with 8; lia ].

Lemma c2_head : forall m dt x7 x28 x29 x30 x31,
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG C2POST (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                           SPF DT SYM pos bg cnt nb bs lvl 2 2 (APX2HB + 100)).
Proof.
  intros m dt x7 x28 x29 x30 x31 I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 100) in change (APX2HB + 100) with v.
  let p1 := eval vm_compute in (APX2HB + 148) in let p2 := eval vm_compute in (APX2HB + 2428) in
  kx_runFm [p1; p2] 40%nat
    [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256; KZRange bs 0 255; KZRange nb 0 12; KZRange lvl 1 2]
    (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  kx_post_regs. cbn [mem_denot].
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ ?v8 ?v9 _ _ _ _ _ _ _ ?v17 ?v18 ?v19 _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (c2_loop (Z.to_nat cnt) 0 m dt v8 v9 v17 v18 v19 ltac:(lia) ltac:(lia) I ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact PRE)) as L0
  end.
  unfold C2S, ASHOFF in L0. rewrite !Z.mul_0_r, !Z.add_0_r in L0.
  lazymatch type of L0 with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
    replace S1 with S0; [exact L0|] end end.
  f_equal; try f_equal; c2_hfeq.
Qed.
End C2.

Lemma c2_zero : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bg <= 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 pos)
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg 0 nb bs lvl 2 2 (APX2HB + 100)).
Proof.
  intros until dt. intros HY HL HB I PRE.
  open_hyhb HY. open_xhb I. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 100) in change (APX2HB + 100) with v.
  destruct HL as [HL|HL]; subst lvl.
  all: let p := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR | eassumption ..].
Qed.

Lemma x2hb_c2 : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m0 SYM (SYM + 256) -> x2hb_art m0 ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 ->
  pos + 2 * cnt <= 2 ^ mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 2 * cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl 2 2 (APX2HB + 100)).
Proof.
  intros until dt. intros HY UDT USY ART0 HP HB HC0 HBC HNB HT HM HROOM HL HBS I PRE.
  assert (CZ : cnt = 0 \/ 1 <= cnt) by lia. destruct CZ as [CZ|CZ].
  - subst cnt. rewrite Z.mul_0_r, Z.add_0_r. eapply c2_zero; [exact HY | exact HL | lia | exact I | exact PRE].
  - eapply c2_head; first [eassumption | lia].
Qed.
End CANSEC1.
