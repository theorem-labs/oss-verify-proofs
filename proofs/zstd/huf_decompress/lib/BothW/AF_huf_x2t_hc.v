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

Lemma x8_stepE : forall (T DT c c1 o1 o2 nb lv : Z) (bs w : list byte),
  c1 = c + 1 -> o1 = DT + 4 * c + 4 -> o2 = DT + 4 * c + 6 -> 0 <= c -> 4 * c + 8 <= zlen bs ->
  x2pref T c (map bv_unsigned bs) -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 -> length w = 2%nat ->
  x2pref T c1 (map bv_unsigned (replay1 DT (replay1 DT bs o1 w) o2 (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c c1 o1 o2 nb lv bs w E1 E2 E3 HC HL PRE HNB HT HLV LW. subst c1 o1 o2.
  destruct (x2hb_dt_of bs) as [EB BB]. rewrite <- EB.
  apply x2hb_c1_pref; try assumption; rewrite ?length_map; lia.
Qed.

Lemma x8_c1E : forall (T DT c c1 o1 o2 nb lv : Z) (dt : list Z) (w : list byte),
  c1 = c + 1 -> o1 = DT + 4 * c + 4 -> o2 = DT + 4 * c + 6 -> 0 <= c -> 4 * c + 8 <= zlen dt -> Forall isbyte dt ->
  x2pref T c dt -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 -> length w = 2%nat ->
  x2pref T c1 (map bv_unsigned (replay1 DT (replay1 DT (map (Z_to_bv 8) dt) o1 w) o2
                                 (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c c1 o1 o2 nb lv dt w E1 E2 E3 HC HL HBY PRE HNB HT HLV LW. subst c1 o1 o2.
  apply x2hb_c1_pref; assumption.
Qed.

Ltac x8_peel j :=
  eapply (x8_stepE _ _ j); [lia | lia | lia | lia | rewrite ?replay1_length, ?length_map; lia | | lia | lia | lia | assumption].

Lemma x2hb_c8_pref : forall (T DT c nb lv : Z) (dt : list Z) (w0 w1 w2 w3 w4 w5 w6 w7 : list byte),
  0 <= c -> 4 * c + 36 <= zlen dt -> Forall isbyte dt -> x2pref T c dt -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 ->
  length w0 = 2%nat -> length w1 = 2%nat -> length w2 = 2%nat -> length w3 = 2%nat ->
  length w4 = 2%nat -> length w5 = 2%nat -> length w6 = 2%nat -> length w7 = 2%nat ->
  x2pref T (c + 8) (map bv_unsigned (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (map (Z_to_bv 8) dt) (DT + 4 * c + 4) w0) (DT + 4 * c + 6) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 8) w1) (DT + 4 * c + 10) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 12) w2) (DT + 4 * c + 14) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 16) w3) (DT + 4 * c + 18) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 20) w4) (DT + 4 * c + 22) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 24) w5) (DT + 4 * c + 26) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 28) w6) (DT + 4 * c + 30) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)))) (DT + 4 * c + 32) w7) (DT + 4 * c + 34) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c nb lv dt w0 w1 w2 w3 w4 w5 w6 w7 HC HL HBY PRE HNB HT HLV L0 L1 L2 L3 L4 L5 L6 L7.
  x8_peel (c + 7). x8_peel (c + 6). x8_peel (c + 5). x8_peel (c + 4).
  x8_peel (c + 3). x8_peel (c + 2). x8_peel (c + 1).
  eapply (x8_c1E _ _ c); [lia | lia | lia | lia | lia | assumption | assumption | lia | lia | lia | assumption].
Qed.

Lemma x8_w2 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x mod 65536 = y mod 65536 ->
  word_to_le_bytes 2 (Z_to_bv 64 x) = word_to_le_bytes 2 (Z_to_bv 64 y).
Proof.
  intros x y Hx Hy H.
  assert (B0 : x mod 256 = y mod 256) by (revert H; Z.div_mod_to_equations; lia).
  assert (B1 : (x / 256) mod 256 = (y / 256) mod 256) by (revert H; Z.div_mod_to_equations; lia).
  unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small x), (Z.mod_small y) by lia.
  cbn [Z_to_le_bytes].
  f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; first [exact B0 | exact B1 | revert B0 B1; Z.div_mod_to_equations; lia].
Qed.

Lemma x8_hw : forall X l nb lv s, (s = 16 \/ s = 48) -> 0 <= l < 65536 -> 0 <= nb + 256 * lv < 32768 ->
  X = 4294967297 * (l + 65536 * (nb + 256 * lv)) ->
  word_to_le_bytes 2 (Z_to_bv 64 (X mod 2 ^ 64 / 2 ^ (s mod 64))) = word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv)).
Proof.
  intros X l nb lv s HS HL HH HX.
  set (h := nb + 256 * lv) in *.
  rewrite (Z.mod_small X) by (subst X; lia).
  destruct HS as [HS|HS]; subst s.
  - change (2 ^ (16 mod 64)) with 65536.
    replace X with (l + (h + 65536 * (l + 65536 * h)) * 65536) by (subst X; lia).
    rewrite Z.div_add by lia. rewrite (Z.div_small l) by lia. rewrite Z.add_0_l.
    apply x8_w2; [lia | lia |].
    replace (h + 65536 * (l + 65536 * h)) with (h + (l + 65536 * h) * 65536) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - change (2 ^ (48 mod 64)) with (2 ^ 48).
    replace X with ((l + 65536 * h + 4294967296 * l) + h * 2 ^ 48) by (subst X; lia).
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma x8_andz : forall x, 0 <= x < 2 ^ 64 -> x mod 2 = 0 -> Z_to_bv 64 0 = alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 1).
Proof.
  intros x H1 H2. apply bv_eq. rewrite u_and64, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small x) by lia.
  change (Z.land x (1 mod 2 ^ 64)) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  change (2 ^ 1) with 2. rewrite H2. reflexivity.
Qed.

Lemma x8_shd : forall E B c off A X lo hi,
  bv_unsigned (edenot E B) = X -> lo <= X -> X + 36 <= hi ->
  ((0 <=? c) && (c <=? 35) && (0 <=? off) && (off <=? 34) && (0 <=? A) && (A + 2 ^ 44 <=? 2 ^ 64))%bool = true ->
  4096 <= lo -> hi <= 2 ^ 47 -> (hi <= lo / 8 + A \/ (hi + 7) / 8 + A + 1 <= lo) ->
  flat E (SA (EAlu ALU_SRL (EAlu ALU_ADD B (ELit c)) (ELit 3)) A) (elenZ E (ELit 1)) /\
  flat E (SA B off) (elenZ E (ELit 2)) /\
  (estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD B (ELit c)) (ELit 3)) A) + elenZ E (ELit 1) <= estart E (SA B off) \/
   estart E (SA B off) + elenZ E (ELit 2) <= estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD B (ELit c)) (ELit 3)) A)).
Proof.
  intros E B c off A X lo hi HX H1 H2 HB H3 H4 HS.
  rewrite !Bool.andb_true_iff, !Z.leb_le in HB. destruct HB as (((((C0 & C1) & O0) & O1) & A0) & A1).
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64, u_add64, HX.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 2)) with 2. change (2 ^ (3 mod 64)) with 8.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small (X + c)) by lia.
  assert (D0 : 0 <= lo / 8) by (apply Z.div_pos; lia).
  assert (D1 : lo / 8 <= (X + c) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (X + c) / 8 <= (hi + 7) / 8) by (apply Z.div_le_mono; lia).
  assert (D4 : (X + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  repeat split; lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma x8_sh0 : forall (m : amem) lo hi G, unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi ->
  0 <= ASHOFF + G -> ASHOFF + G + 1 <= 2 ^ 64 -> bytes_at bsegs m (ASHOFF + G) [Z_to_bv 8 0].
Proof.
  intros m lo hi G U H1 H2 H3 H4. split; [exact H3|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error]. unfold mrd. replace (ASHOFF + G + Z.of_nat 0) with (ASHOFF + G) by lia.
  erewrite unpoisoned_full; [reflexivity | exact U | lia | lia].
Qed.

Section C8.
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
Hypothesis HROOM : pos + 8 * cnt <= 2 ^ mtl.
Hypothesis HBS : 0 <= bs < 256.
Hypothesis HL : lvl = 1 \/ lvl = 2.

Definition C8POST := x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 8 * cnt).

Definition C8S (k : Z) (m : amem) (y14 y17 y20 y21 y22 y23 y24 y25 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (32 * k)) (Z_to_bv 64 0) (Z_to_bv 64 (-1))
          (Z_to_bv 64 (65536 * nb + 16777216 * lvl)) (Z_to_bv 64 (DT + 4 * pos + 4)) (Z_to_bv 64 (SYM + bg + k))
          (Z_to_bv 64 (SYM + (bg + cnt))) (Z_to_bv 64 (SYM + bg + k)) y14 (Z_to_bv 64 bs) (Z_to_bv 64 lvl) y17
          (Z_to_bv 64 (ASHOFF + (DT + 4 * pos + 4 + 32 * k) / 8)) (Z_to_bv 64 (-33)) y20 y21 y22 y23 y24 y25 x26 x27
          (Z_to_bv 64 1) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)))
     F (Z_to_bv 64 (APX2HB + 456)) fc None m (seg_rom bsegs).

Ltac c8_zl :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR; Z.div_mod_to_equations; lia.

Ltac c8_clrk h :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR h.

Ltac c8_lz :=
  let DTL := ident:(DTL) in let DTH := ident:(DTH) in let SYL := ident:(SYL) in let SYH := ident:(SYH) in
  let KLO := ident:(KLO) in let SPT := ident:(SPT) in let DSY := ident:(DSY) in let DSP := ident:(DSP) in
  let HK := ident:(HK) in let CK := ident:(CK) in let P2 := ident:(P2) in let BX1 := ident:(BX1) in
  let BX2 := ident:(BX2) in let LSY := ident:(LSY) in
  clear - DTL DTH SYL SYH KLO SPT DSY DSP HP HB HBC HROOM HK CK P2 BX1 BX2 LSY; lia.

Ltac c8_bval :=
  let BX1 := ident:(BX1) in let BX2 := ident:(BX2) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in
  w4ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  clear - BX1 BX2 DTL DTH; rewrite Z.mod_small by lia; lia.

Ltac c8_shd :=
  let k := ident:(k) in let BX1 := ident:(BX1) in let BX2 := ident:(BX2) in let DTL := ident:(DTL) in
  let DTH := ident:(DTH) in let SHD := ident:(SHD) in
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL (EAlu ALU_ADD ?B (ELit ?c)) (ELit 3)) ?A) _ /\ flat _ (SA _ ?off) _ /\ _ =>
    apply (x8_shd E B c off A (32 * k + DT + 4 * pos) DT (DT + 4 * (1 + 2 ^ mtl)));
    [ c8_bval | exact BX1 | exact BX2 | vm_compute; reflexivity | exact DTL | exact DTH
    | first [exact SHD | clear - SHD; lia] ]
  end.

Ltac c8_acc :=
  lazymatch goal with |- accP ?RN ?E (?a, ?n) =>
    unfold accP; cbn [fst snd];
    rewrite (flat_u E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                               unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c8_zl);
    unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    lazymatch goal with R : rng RN ?lo 1 |- _ => let R3 := fresh "R3" in destruct R as (_ & _ & R3); apply R3; c8_zl end
  end.

Ltac c8_region :=
  lazymatch goal with |- region_ok ?sg ?mm ?E (zr_reg ?r) =>
    let r' := eval vm_compute in (zr_reg r) in change (region_ok sg mm E r'); unfold region_ok; cbn [fst snd];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      unfold estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      split; [c8_zl|]; split; [c8_zl|];
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3;
      lazymatch goal with |- _ (Z_to_bv 64 ?x) <> None =>
        replace x with (A + Z.of_nat 0) by (c8_clrk Hi; Z.div_mod_to_equations; lia) end;
      rewrite SH3; discriminate
    end
  end.

Ltac c8_kword :=
  lazymatch goal with |- kentry_ok ?sg ?E ?mm (zk_ent (ZKWord ?za 1 (ZL 0))) =>
    let k' := eval vm_compute in (zk_ent (ZKWord za 1 (ZL 0))) in change (kentry_ok sg E mm k'); cbn [kentry_ok];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ /\ flat E ?a _ /\ _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      let FL := fresh "FL" in
      assert (FL : flat E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                                   unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c8_zl);
      split; [lia|]; split; [exact FL|];
      let FU := fresh "FU" in pose proof (flat_u E a 1 FL) as FU;
      replace (adenot E a) with (Z_to_bv 64 (A + Z.of_nat 0));
      [ rewrite rdn_unfold; cbv beta iota;
        specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3; rewrite SH3;
        rewrite rdn_unfold; cbv beta iota; cbn [edenot]; reflexivity
      | apply bv_eq; rewrite FU; unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c8_zl ]
    end
  end.

Ltac c8_side :=
  let KLO := ident:(KLO) in let SPT := ident:(SPT) in
  first [ lazymatch goal with |- KHIGH + 112 <= _ <= _ => unfold KHIGH; clear - KLO SPT; lia end
        | c8_shd | c8_acc | c8_region | c8_kword ].

Ltac c8_bveq := apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity.

Ltac c8_feq := let HL1 := ident:(HL1) in first [ reflexivity | c8_bveq | f_equal; clear - HL1; lia ].

Ltac c8_setup :=
  let I := ident:(I) in let m := ident:(m) in let k := ident:(k) in let HY' := ident:(HY') in
  let KLO := ident:(KLO) in let RSDT := ident:(RSDT) in let RSSY := ident:(RSSY) in let DTLEN := ident:(DTLEN) in
  let SYLEN := ident:(SYLEN) in let DTC := ident:(DTC) in let ABD := ident:(ABD) in let DTL := ident:(DTL) in
  let DTH := ident:(DTH) in let HK := ident:(HK) in let CK := ident:(CK) in let UDTm := ident:(UDTm) in
  let P2 := ident:(P2) in let LDT := ident:(LDT) in let LSY := ident:(LSY) in let WDT := ident:(WDT) in
  let SHD := ident:(SHD) in let qc := ident:(qc) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  let RQ := ident:(RQ) in let SH0 := ident:(SH0) in let dt := ident:(dt) in let USYm := ident:(USYm) in
  let BX1 := ident:(BX1) in let BX2 := ident:(BX2) in
  pose proof HY as HY'; open_hyhb HY'; open_xhb I;
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption);
  assert (USYm : unpoisoned m SYM (SYM + 256)) by (eapply x2hb_unp_syM; eassumption);
  unfold KHIGH in KLO; unfold shspan in RSDT, RSSY;
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia);
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN);
  assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN;
  pose proof (proj2 DTC) as WDT; rewrite LDT in WDT;
  pose proof (ablk_shad_disj _ _ ABD ltac:(lia)) as SHD; rewrite !shad_div in SHD;
  assert (BX1 : DT <= 32 * k + DT + 4 * pos) by (clear - HK HP; lia);
  assert (BX2 : 32 * k + DT + 4 * pos + 36 <= DT + 4 * (1 + 2 ^ mtl)) by (clear - HK CK HROOM HP; lia);
  unfold C8S;
  remember ((DT + 4 * pos + 4 + 32 * k) / 8) as qc eqn:HQ;
  assert (QR : 512 <= qc <= 2 ^ 44) by (subst qc; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia);
  assert (RQ : rng RNG (ASHOFF + qc) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst qc; clear - DTL DTH HP HK CK HROOM P2;
        Z.div_mod_to_equations; lia);
  assert (SH0 : bytes_at bsegs m (ASHOFF + qc) [Z_to_bv 8 0])
    by (subst qc; apply x8_sh0 with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia ..]);
  unfold ASHOFF in *;
  let v := eval vm_compute in (APX2HB + 456) in change (APX2HB + 456) with v.

Ltac c8_es :=
  let BX1 := ident:(BX1) in let BX2 := ident:(BX2) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in
  unfold estart; cbn [a_base a_off]; w4ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  clear - BX1 BX2 DTL DTH; rewrite Z.mod_small by lia; lia.

Ltac c8_ev :=
  let HL1 := ident:(HL1) in
  w4ez;
  lazymatch goal with
  | |- word_to_le_bytes 2 (Z_to_bv 64 (?X mod _ / 2 ^ (?s mod 64))) = _ =>
    lazymatch X with context [bv_unsigned (ev ?E ?j)] =>
      let R := fresh "R" in kx_range (EVar j) R;
      let y := constr:(bv_unsigned (ev E j)) in
      lazymatch goal with
      | HL1 : lvl = 1 |- _ =>
        apply (x8_hw X y nb lvl s);
        [ first [left; reflexivity | right; reflexivity] | clear - R; lia | clear - HL1 HNB HT; lia | clear - HL1; lia ]
      | HL1 : lvl = 2 |- _ =>
        apply (x8_hw X (256 * y + bs) nb lvl s);
        [ first [left; reflexivity | right; reflexivity] | clear - R HBS; lia | clear - HL1 HNB HT; lia | clear - HL1; lia ]
      end
    end
  end.

Ltac c8_log :=
  let k := ident:(k) in let EA1 := ident:(EA1) in let EA2 := ident:(EA2) in let EA3 := ident:(EA3) in let EA4 := ident:(EA4) in let EA5 := ident:(EA5) in let EA6 := ident:(EA6) in let EA7 := ident:(EA7) in let EA8 := ident:(EA8) in let EA9 := ident:(EA9) in let EA10 := ident:(EA10) in let EA11 := ident:(EA11) in let EA12 := ident:(EA12) in let EA13 := ident:(EA13) in let EA14 := ident:(EA14) in let EA15 := ident:(EA15) in let EA16 := ident:(EA16) in
  let EV1 := ident:(EV1) in let EV3 := ident:(EV3) in let DTC := ident:(DTC) in
  let KXLF := ident:(KXLF) in let SYB := ident:(SYB) in let FR := ident:(FR) in let MI := ident:(MI) in
  let MU := ident:(MU) in let WM := ident:(WM) in let DTC' := ident:(DTC') in let SYB' := ident:(SYB') in
  let FR' := ident:(FR') in let MI' := ident:(MI') in let MU' := ident:(MU') in let WM' := ident:(WM') in
  let WDT := ident:(WDT) in let WV := ident:(WV) in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let DTE := ident:(DTE) in let DTBY' := ident:(DTBY') in let LB1 := ident:(LB1) in let DTLEN := ident:(DTLEN) in
  let BX1 := ident:(BX1) in let BX2 := ident:(BX2) in let CK := ident:(CK) in let HK := ident:(HK) in
  let HL1 := ident:(HL1) in
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
   lazymatch lg with [SE ?a1 _ ?v1; SE ?a2 _ ?v2; SE ?a3 _ ?v3; SE ?a4 _ ?v4; SE ?a5 _ ?v5; SE ?a6 _ ?v6; SE ?a7 _ ?v7; SE ?a8 _ ?v8; SE ?a9 _ ?v9; SE ?a10 _ ?v10; SE ?a11 _ ?v11; SE ?a12 _ ?v12; SE ?a13 _ ?v13; SE ?a14 _ ?v14; SE ?a15 _ ?v15; SE ?a16 _ ?v16] =>
    assert (EA1 : estart E a1 = DT + 4 * (pos + 8 * k) + 34) by c8_es;
    assert (EA2 : estart E a2 = DT + 4 * (pos + 8 * k) + 32) by c8_es;
    assert (EA3 : estart E a3 = DT + 4 * (pos + 8 * k) + 30) by c8_es;
    assert (EA4 : estart E a4 = DT + 4 * (pos + 8 * k) + 28) by c8_es;
    assert (EA5 : estart E a5 = DT + 4 * (pos + 8 * k) + 26) by c8_es;
    assert (EA6 : estart E a6 = DT + 4 * (pos + 8 * k) + 24) by c8_es;
    assert (EA7 : estart E a7 = DT + 4 * (pos + 8 * k) + 22) by c8_es;
    assert (EA8 : estart E a8 = DT + 4 * (pos + 8 * k) + 20) by c8_es;
    assert (EA9 : estart E a9 = DT + 4 * (pos + 8 * k) + 18) by c8_es;
    assert (EA10 : estart E a10 = DT + 4 * (pos + 8 * k) + 16) by c8_es;
    assert (EA11 : estart E a11 = DT + 4 * (pos + 8 * k) + 14) by c8_es;
    assert (EA12 : estart E a12 = DT + 4 * (pos + 8 * k) + 12) by c8_es;
    assert (EA13 : estart E a13 = DT + 4 * (pos + 8 * k) + 10) by c8_es;
    assert (EA14 : estart E a14 = DT + 4 * (pos + 8 * k) + 8) by c8_es;
    assert (EA15 : estart E a15 = DT + 4 * (pos + 8 * k) + 6) by c8_es;
    assert (EA16 : estart E a16 = DT + 4 * (pos + 8 * k) + 4) by c8_es;
    assert (EV1 : word_to_le_bytes 2 (edenot E v1) = word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lvl))) by c8_ev;
    assert (EV3 : word_to_le_bytes 2 (edenot E v3) = word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lvl))) by c8_ev;
    pose proof (kx_u8arr_replay bsegs E mm lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E mm lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E mm lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 mm lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 mm lg WM) as WM';
    cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
    rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8, ?EA9, ?EA10, ?EA11, ?EA12, ?EA13, ?EA14, ?EA15, ?EA16 in SYB', FR', MI', MU';
    cbn [replay] in DTC'; rewrite EA1, EA2, EA3, EA4, EA5, EA6, EA7, EA8, EA9, EA10, EA11, EA12, EA13, EA14, EA15, EA16, EV1, EV3 in DTC'
   end
  end;
  destruct WDT as (_ & _ & WV);
  specialize (SYB' ltac:(repeat split; c8_lz));
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; c8_lz));
  specialize (MI' ltac:(repeat split; let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None =>
      replace (b + j) with (DT + (b - DT + j)) by (clear - Hj; lia); apply WV; clear - Hj BX1 BX2 HP HK; lia end));
  specialize (MU' ltac:(repeat split; cbn; c8_lz));
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end;
  assert (PRE' : x2pref T (pos + 8 * k + 8) (map bv_unsigned bs1))
    by (unfold bs1; apply x2hb_c8_pref;
        first [ apply length_wtlb | assumption | clear - DTLEN HROOM CK HK HP HNB HT HL1; lia ]);
  destruct (x2hb_dt_of bs1) as [DTE DTBY'];
  rewrite <- DTE in DTC';
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).

Ltac c8_next :=
  let k := ident:(k) in let XH' := ident:(XH') in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let KH := ident:(KH) in let KN := ident:(KN) in let QN := ident:(QN) in let HQ := ident:(HQ) in
  let qc := ident:(qc) in
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?v14 _ _ ?v17 _ _ ?v20 ?v21 ?v22 ?v23 ?v24 ?v25 _ _ _ _ _ _) _ _ _ _ ?mm _) =>
    assert (XH' : XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 (map bv_unsigned bs1) mm)
      by (unfold X2HBFR; eapply XHb_close; eassumption);
    replace (pos + 8 * k + 8) with (pos + 8 * (k + 1)) in PRE' by lia;
    pose proof (KH mm (map bv_unsigned bs1) v14 v17 v20 v21 v22 v23 v24 v25 XH' PRE') as KN
  end;
  assert (QN : (DT + 4 * pos + 4 + 32 * (k + 1)) / 8 = qc + 4)
    by (rewrite HQ; replace (DT + 4 * pos + 4 + 32 * (k + 1)) with ((DT + 4 * pos + 4 + 32 * k) + 4 * 8) by lia;
        apply Z.div_add; lia);
  unfold C8S, ASHOFF in KN; rewrite QN in KN;
  lazymatch type of KN with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
    replace S1 with S0; [exact KN|] end end;
  f_equal; try f_equal; c8_feq.

Lemma c8_more : forall k m dt y14 y17 y20 y21 y22 y23 y24 y25,
  0 <= k -> k + 1 < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 8 * k) dt ->
  (forall m' dt' z14 z17 z20 z21 z22 z23 z24 z25,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 8 * (k + 1)) dt' ->
     evtF bsegs RNG C8POST (C8S (k + 1) m' z14 z17 z20 z21 z22 z23 z24 z25)) ->
  evtF bsegs RNG C8POST (C8S k m y14 y17 y20 y21 y22 y23 y24 y25).
Proof.
  intros k m dt y14 y17 y20 y21 y22 y23 y24 y25 HK CK I PRE KH.
  c8_setup.
  pose proof HL as HL0. destruct HL0 as [HL1|HL1]; rewrite HL1.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 456) in let p2 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2] 160%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 1 256; KZRange k 0 255;
          KZRange (bg + k) 0 255; KZRange (cnt - k - 2) 0 255; KZRange (2 ^ mtl - pos - 8 * k - 8) 0 4096;
          KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44); KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 32 * k) 32]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 32 * k, 32); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 32 * k, 32)]
         [(DT + 4 * pos + 4 + 32 * k, 32); (SYM + bg + k, 1)].
  all: try c8_side.
  all: kx_post_regs.
  all: c8_log.
  all: c8_next.
Qed.

Lemma c8_last : forall k m dt y14 y17 y20 y21 y22 y23 y24 y25,
  0 <= k -> k + 1 = cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 8 * k) dt -> evtF bsegs RNG C8POST (C8S k m y14 y17 y20 y21 y22 y23 y24 y25).
Proof.
  intros k m dt y14 y17 y20 y21 y22 y23 y24 y25 HK CK I PRE.
  c8_setup.
  rewrite <- CK.
  pose proof HL as HL0. destruct HL0 as [HL1|HL1]; rewrite HL1.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 456) in let p2 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2] 160%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange k 0 255; KZRange (bg + k) 0 255;
          KZRange (2 ^ mtl - pos - 8 * k - 8) 0 4096; KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44);
          KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 32 * k) 32]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 32 * k, 32); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 32 * k, 32)]
         [(DT + 4 * pos + 4 + 32 * k, 32); (SYM + bg + k, 1)].
  all: try c8_side.
  all: kx_post_regs.
  all: c8_log.
  all: unfold C8POST; replace (pos + 8 * cnt) with (pos + 8 * k + 8) by lia;
       eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma c8_body : forall k m dt y14 y17 y20 y21 y22 y23 y24 y25,
  0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 8 * k) dt ->
  (forall m' dt' z14 z17 z20 z21 z22 z23 z24 z25, k + 1 < cnt ->
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 8 * (k + 1)) dt' ->
     evtF bsegs RNG C8POST (C8S (k + 1) m' z14 z17 z20 z21 z22 z23 z24 z25)) ->
  evtF bsegs RNG C8POST (C8S k m y14 y17 y20 y21 y22 y23 y24 y25).
Proof.
  intros k m dt y14 y17 y20 y21 y22 y23 y24 y25 HK I PRE KH.
  assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
  - eapply c8_more; [lia | exact CK | exact I | exact PRE |].
    intros m' dt' z14 z17 z20 z21 z22 z23 z24 z25 I' PRE'. eapply KH; [exact CK | exact I' | exact PRE'].
  - eapply c8_last; [lia | exact CK | exact I | exact PRE].
Qed.

Lemma c8_loop : forall n k m dt y14 y17 y20 y21 y22 y23 y24 y25,
  Z.of_nat n = cnt - k -> 0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 8 * k) dt -> evtF bsegs RNG C8POST (C8S k m y14 y17 y20 y21 y22 y23 y24 y25).
Proof.
  induction n as [|n IH]; intros k m dt y14 y17 y20 y21 y22 y23 y24 y25 HN HK I PRE; [lia|].
  eapply c8_body; [exact HK | exact I | exact PRE |].
  intros m' dt' z14 z17 z20 z21 z22 z23 z24 z25 HK' I' PRE'. eapply IH; [lia | lia | exact I' | exact PRE'].
Qed.

Ltac c8_andg :=
  let DTL := ident:(DTL) in let DTH := ident:(DTH) in let DT4 := ident:(DT4) in
  lazymatch goal with |- Z_to_bv 64 0 = edenot ?E (EAlu ALU_AND ?X (ELit 1)) =>
    change (edenot E (EAlu ALU_AND X (ELit 1))) with (alu64 ALU_AND (edenot E X) (edenot E (ELit 1))); w4ez;
    apply x8_andz; [clear - DTL DTH HP HROOM HC; lia | clear - DT4; Z.div_mod_to_equations; lia]
  end.

Ltac c8_hfeq :=
  first [ reflexivity | c8_bveq | c8_andg | f_equal; lia
        | f_equal; rewrite Z.mod_small by lia; change (2 ^ (3 mod 64)) with 8; lia ].

Lemma c8_head : forall m dt x7 x28 x29 x30 x31,
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG C8POST (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                           SPF DT SYM pos bg cnt nb bs lvl 8 8 (APX2HB + 396)).
Proof.
  intros m dt x7 x28 x29 x30 x31 I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 396) in change (APX2HB + 396) with v.
  let p1 := eval vm_compute in (APX2HB + 456) in let p2 := eval vm_compute in (APX2HB + 2428) in
  kx_runFm [p1; p2] 40%nat
    [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256; KZRange bs 0 255; KZRange nb 0 12; KZRange lvl 1 2]
    (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  kx_post_regs. cbn [mem_denot].
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?v14 _ _ ?v17 _ _ ?v20 ?v21 ?v22 ?v23 ?v24 ?v25 _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (c8_loop (Z.to_nat cnt) 0 m dt v14 v17 v20 v21 v22 v23 v24 v25 ltac:(lia) ltac:(lia) I
                  ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact PRE)) as L0
  end.
  unfold C8S, ASHOFF in L0. rewrite !Z.mul_0_r, !Z.add_0_r in L0.
  lazymatch type of L0 with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
    replace S1 with S0; [exact L0|] end end.
  f_equal; try f_equal; c8_hfeq.
Qed.
End C8.

Lemma c8_zero : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bg <= 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 pos)
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg 0 nb bs lvl 8 8 (APX2HB + 396)).
Proof.
  intros until dt. intros HY HL HB I PRE.
  open_hyhb HY. open_xhb I. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 396) in change (APX2HB + 396) with v.
  destruct HL as [HL|HL]; subst lvl.
  all: let p := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR | eassumption ..].
Qed.

Lemma x2hb_c8 : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m0 SYM (SYM + 256) -> x2hb_art m0 ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 ->
  pos + 8 * cnt <= 2 ^ mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 8 * cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl 8 8 (APX2HB + 396)).
Proof.
  intros until dt. intros HY UDT USY ART0 HP HB HC0 HBC HNB HT HM HROOM HL HBS I PRE.
  assert (CZ : cnt = 0 \/ 1 <= cnt) by lia. destruct CZ as [CZ|CZ].
  - subst cnt. rewrite Z.mul_0_r, Z.add_0_r. eapply c8_zero; [exact HY | exact HL | lia | exact I | exact PRE].
  - eapply c8_head; first [eassumption | lia].
Qed.
End CANSEC1.
