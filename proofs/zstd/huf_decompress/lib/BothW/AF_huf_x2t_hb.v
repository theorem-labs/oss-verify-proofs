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

Lemma c4_step : forall (T DT c nb lv : Z) (bs w : list byte),
  0 <= c -> 4 * c + 8 <= Z.of_nat (length bs) -> x2pref T c (map bv_unsigned bs) -> 0 <= nb <= T -> T <= 12 ->
  1 <= lv <= 2 -> length w = 2%nat ->
  x2pref T (c + 1) (map bv_unsigned (replay1 DT (replay1 DT bs (DT + 4 * c + 4) w) (DT + 4 * c + 6)
                                       (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c nb lv bs w HC HL PRE HNB HT HLV LW.
  destruct (x2hb_dt_of bs) as [E B]. rewrite <- E.
  apply x2hb_c1_pref; try assumption. rewrite length_map. lia.
Qed.

Lemma x2hb_c4_pref : forall (T DT c nb lv : Z) (dt : list Z) (w1 w2 w3 w4 : list byte),
  0 <= c -> 4 * c + 20 <= zlen dt -> Forall isbyte dt -> x2pref T c dt -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 ->
  length w1 = 2%nat -> length w2 = 2%nat -> length w3 = 2%nat -> length w4 = 2%nat ->
  x2pref T (c + 4) (map bv_unsigned
    (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (replay1 DT (map (Z_to_bv 8) dt)
       (DT + 4 * c + 4) w1) (DT + 4 * c + 6) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))
       (DT + 4 * c + 8) w2) (DT + 4 * c + 10) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))
       (DT + 4 * c + 12) w3) (DT + 4 * c + 14) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))
       (DT + 4 * c + 16) w4) (DT + 4 * c + 18) (word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lv))))).
Proof.
  intros T DT c nb lv dt w1 w2 w3 w4 HC HL HBY PRE HNB HT HLV L1 L2 L3 L4.
  replace (DT + 4 * c + 16) with (DT + 4 * (c + 3) + 4) by lia.
  replace (DT + 4 * c + 18) with (DT + 4 * (c + 3) + 6) by lia.
  replace (DT + 4 * c + 12) with (DT + 4 * (c + 2) + 4) by lia.
  replace (DT + 4 * c + 14) with (DT + 4 * (c + 2) + 6) by lia.
  replace (DT + 4 * c + 8) with (DT + 4 * (c + 1) + 4) by lia.
  replace (DT + 4 * c + 10) with (DT + 4 * (c + 1) + 6) by lia.
  replace (c + 4) with (c + 3 + 1) by lia.
  apply c4_step; [lia | rewrite !replay1_length, length_map; lia | | assumption ..].
  replace (c + 3) with (c + 2 + 1) by lia.
  apply c4_step; [lia | rewrite !replay1_length, length_map; lia | | assumption ..].
  replace (c + 2) with (c + 1 + 1) by lia.
  apply c4_step; [lia | rewrite !replay1_length, length_map; lia | | assumption ..].
  apply x2hb_c1_pref; first [assumption | lia].
Qed.

Lemma c4_w2 : forall X Y, X mod 65536 = Y mod 65536 ->
  word_to_le_bytes 2 (Z_to_bv 64 X) = word_to_le_bytes 2 (Z_to_bv 64 Y).
Proof.
  intros X Y H.
  assert (W : forall v : word, word_to_le_bytes 2 v = [Z_to_bv 8 (bv_unsigned v); Z_to_bv 8 (Z.shiftr (bv_unsigned v) 8)])
    by (intros v; reflexivity).
  rewrite !W. f_equal; [|f_equal];
    apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; change (2 ^ 64) with 18446744073709551616;
    Z.div_mod_to_equations; lia.
Qed.

Ltac c4_fpre := unfold flat, estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  cbn [Z.of_N]; change (2 ^ (3 mod 64)) with 8 in *.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2hb_sh0b : forall (m : amem) lo hi G, unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi ->
  0 <= ASHOFF + G -> ASHOFF + G + 1 <= 2 ^ 64 -> bytes_at bsegs m (ASHOFF + G) [Z_to_bv 8 0].
Proof.
  intros m lo hi G U H1 H2 H3 H4. split; [exact H3|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error]. unfold mrd. replace (ASHOFF + G + Z.of_nat 0) with (ASHOFF + G) by lia.
  erewrite unpoisoned_full; [reflexivity | exact U | lia | lia].
Qed.

Section C4.
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
Hypothesis HROOM : pos + 4 * cnt <= 2 ^ mtl.
Hypothesis HBS : 0 <= bs < 256.
Hypothesis HL : lvl = 1 \/ lvl = 2.

Definition C4PC : Z := if Z.eqb lvl 1 then APX2HB + 1692 else APX2HB + 2168.
Definition C4B : Z := if Z.eqb lvl 1 then 65536 * nb + 16777216 else 65536 * nb + bs + 33554432.

Definition C4POST := x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 4 * cnt).

Definition C4S (k : Z) (m : amem) (y8 y9 y15 y18 y19 y30 y31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-1))
          (Z_to_bv 64 (ASHOFF + (DT + 4 * pos + 4 + 16 * k) / 8)) y8 y9
          (Z_to_bv 64 (DT + 4 * pos + 4 + 16 * k)) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt)))
          (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (DT + 4 * pos + 4 + 16 * k)) y15 (Z_to_bv 64 0) (Z_to_bv 64 (-9))
          y18 y19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 C4B) (Z_to_bv 64 (-17)) y30 y31)
     F (Z_to_bv 64 C4PC) fc None m (seg_rom bsegs).

Ltac c4_zl :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR; Z.div_mod_to_equations; lia.

Ltac c4_clrk h :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HK CK HROOM P2 HQ QR h.

Ltac c4_zs :=
  let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in let CK := ident:(CK) in
  let P2 := ident:(P2) in
  clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia.

Ltac c4_zf :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HK := ident:(HK) in
  let CK := ident:(CK) in let P2 := ident:(P2) in
  clear - SHD DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia.

Ltac c4_es := unfold estart; cbn [a_base a_off]; w4ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite Z.mod_small by c4_zs; c4_zs.

Ltac c4_flat := lazymatch goal with |- flat _ _ _ /\ _ =>
  c4_fpre; repeat (rewrite (Z.mod_small _ (2 ^ 64)) by c4_zs); first [ c4_zf | c4_zl ] end.

Ltac c4_acc :=
  lazymatch goal with |- accP ?RN ?E (?a, ?n) =>
    unfold accP; cbn [fst snd];
    rewrite (flat_u E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                               unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c4_zl);
    unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    lazymatch goal with R : rng RN ?lo 1 |- _ => let R3 := fresh "R3" in destruct R as (_ & _ & R3); apply R3; c4_zl end
  end.

Ltac c4_region :=
  lazymatch goal with |- region_ok ?sg ?mm ?E (zr_reg ?r) =>
    let r' := eval vm_compute in (zr_reg r) in change (region_ok sg mm E r'); unfold region_ok; cbn [fst snd];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      unfold estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      split; [c4_zl|]; split; [c4_zl|];
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3;
      lazymatch goal with |- _ (Z_to_bv 64 ?x) <> None =>
        replace x with (A + Z.of_nat 0) by (c4_clrk Hi; Z.div_mod_to_equations; lia) end;
      rewrite SH3; discriminate
    end
  end.

Ltac c4_kword :=
  lazymatch goal with |- kentry_ok ?sg ?E ?mm (zk_ent (ZKWord ?za 1 (ZL 0))) =>
    let k' := eval vm_compute in (zk_ent (ZKWord za 1 (ZL 0))) in change (kentry_ok sg E mm k'); cbn [kentry_ok];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ /\ flat E ?a _ /\ _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      let FL := fresh "FL" in
      assert (FL : flat E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                                   unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c4_zl);
      split; [lia|]; split; [exact FL|];
      let FU := fresh "FU" in pose proof (flat_u E a 1 FL) as FU;
      replace (adenot E a) with (Z_to_bv 64 (A + Z.of_nat 0));
      [ rewrite rdn_unfold; cbv beta iota;
        specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3; rewrite SH3;
        rewrite rdn_unfold; cbv beta iota; cbn [edenot]; reflexivity
      | apply bv_eq; rewrite FU; unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; cbn [Z.of_N]; c4_zl ]
    end
  end.

Ltac c4_side := first [ lazymatch goal with |- KHIGH + 112 <= _ <= _ => unfold KHIGH; lia end
                      | c4_flat | c4_acc | c4_region | c4_kword ].

Ltac c4_orz :=
  lazymatch goal with |- context [edenot ?E (EAlu ALU_SRL (EMd M_MUL (ELit ?c) (EAlu ALU_OR ?X ?Y)) (ELit ?sh))] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let EW := fresh "EW" in let EX := fresh "EX" in let EY := fresh "EY" in
      pose proof (ez_ok zv E (kE_atoms zv xs) (EAlu ALU_SRL (EMd M_MUL (ELit c) (EAlu ALU_OR X Y)) (ELit sh))) as EW;
      pose proof (ez_ok zv E (kE_atoms zv xs) X) as EX;
      pose proof (ez_ok zv E (kE_atoms zv xs) Y) as EY;
      let na := eval vm_compute in (length zv) in
      cbv [ez] in EW, EX, EY; change (length zv) with na in EX, EY; cbv [nth Nat.ltb Nat.leb] in EX, EY;
      rewrite EW; clear EW;
      change (edenot E (EAlu ALU_OR X Y)) with (alu64 ALU_OR (edenot E X) (edenot E Y));
      rewrite EX, EY; clear EX EY
    end;
    rewrite alu_or; unfold v_or
  end.

Ltac c4_gen :=
  repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
    let R := fresh "RS" in kx_range (EVar j) R; revert R; generalize (bv_unsigned (ev E j))
  end.

Ltac c4_lor :=
  try lazymatch goal with |- context [Z.lor ?Pm ?Qm] =>
    lazymatch Pm with context [256 * ?s] =>
      rewrite (Z.lor_comm Pm Qm);
      let HV := fresh "HV" in let LR := fresh "LR" in let L := fresh "L" in
      assert (HV : Z.lor Qm Pm / 65536 = nb + 512)
        by (apply (x2hb_w_hi Qm Pm nb bs s); try (rewrite Z.mod_small by lia); lia);
      assert (LR : 0 <= Z.lor Qm Pm < 18446744073709551616)
        by (apply (x2hb_w_range Qm Pm nb bs s); try (rewrite Z.mod_small by lia); lia);
      set (L := Z.lor Qm Pm) in *; clearbody L
    end
  end.

Ltac c4_fin :=
  repeat match goal with |- context [2 ^ (?s mod 64)] =>
    let v := eval vm_compute in (2 ^ (s mod 64)) in change (2 ^ (s mod 64)) with v end;
  repeat match goal with |- context [2 ^ 64] => change (2 ^ 64) with 18446744073709551616 end;
  Z.div_mod_to_equations; lia.

Ltac c4_ev :=
  let HL1 := ident:(HL1) in
  first [ c4_orz | w4ez ];
  rewrite ?Z_to_bv_unsigned; try unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  first [ apply c4_w2 | f_equal ];
  c4_gen;
  clear - HNB HT HBS HL1; intros; rewrite HL1;
  c4_lor;
  c4_fin.

Ltac c4_bveq := apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity.

Ltac c4_feq := first [ reflexivity | c4_bveq | f_equal; lia ].

Ltac c4_setup :=
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
  unfold C4S;
  remember ((DT + 4 * pos + 4 + 16 * k) / 8) as qc eqn:HQ;
  assert (QR : 512 <= qc <= 2 ^ 44) by (subst qc; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia);
  assert (RQ : rng RNG (ASHOFF + qc) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst qc; clear - DTL DTH HP HK CK HROOM P2;
        Z.div_mod_to_equations; lia);
  assert (SH0 : bytes_at bsegs m (ASHOFF + qc) [Z_to_bv 8 0])
    by (subst qc; apply x2hb_sh0b with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HK CK HROOM P2; Z.div_mod_to_equations; lia ..]);
  unfold ASHOFF in *.

Ltac c4_lvl :=
  let HL0 := ident:(HL0) in let HL1 := ident:(HL1) in
  pose proof HL as HL0; destruct HL0 as [HL1|HL1]; unfold C4PC, C4B; rewrite HL1; cbn [Z.eqb Pos.eqb];
  let v1 := eval vm_compute in (APX2HB + 1692) in let v2 := eval vm_compute in (APX2HB + 2168) in
  try change (APX2HB + 1692) with v1; try change (APX2HB + 2168) with v2.

Ltac c4_log :=
  let k := ident:(k) in let EA1 := ident:(EA1) in let EA2 := ident:(EA2) in let EA3 := ident:(EA3) in
  let EA4 := ident:(EA4) in let EA5 := ident:(EA5) in let EA6 := ident:(EA6) in let EA7 := ident:(EA7) in
  let EA8 := ident:(EA8) in let EV1 := ident:(EV1) in let EV3 := ident:(EV3) in let DTC := ident:(DTC) in
  let KXLF := ident:(KXLF) in let SYB := ident:(SYB) in let FR := ident:(FR) in let MI := ident:(MI) in
  let MU := ident:(MU) in let WM := ident:(WM) in let DTC' := ident:(DTC') in let SYB' := ident:(SYB') in
  let FR' := ident:(FR') in let MI' := ident:(MI') in let MU' := ident:(MU') in let WM' := ident:(WM') in
  let WDT := ident:(WDT) in let WV := ident:(WV) in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let DTE := ident:(DTE) in let DTBY' := ident:(DTBY') in let LB1 := ident:(LB1) in let DTLEN := ident:(DTLEN) in
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?mm ?lg) _) =>
   lazymatch lg with [SE ?a1 _ ?v1; SE ?a2 _ _; SE ?a3 _ ?v3; SE ?a4 _ _; SE ?a5 _ ?v1; SE ?a6 _ _; SE ?a7 _ ?v3; SE ?a8 _ _] =>
    assert (EA1 : estart E a1 = DT + 4 * pos + 16 * k + 18) by c4_es;
    assert (EA2 : estart E a2 = DT + 4 * pos + 16 * k + 16) by c4_es;
    assert (EA3 : estart E a3 = DT + 4 * pos + 16 * k + 14) by c4_es;
    assert (EA4 : estart E a4 = DT + 4 * pos + 16 * k + 12) by c4_es;
    assert (EA5 : estart E a5 = DT + 4 * pos + 16 * k + 10) by c4_es;
    assert (EA6 : estart E a6 = DT + 4 * pos + 16 * k + 8) by c4_es;
    assert (EA7 : estart E a7 = DT + 4 * pos + 16 * k + 6) by c4_es;
    assert (EA8 : estart E a8 = DT + 4 * pos + 16 * k + 4) by c4_es;
    assert (EV1 : edenot E v1 = Z_to_bv 64 (nb + 256 * lvl)) by c4_ev;
    assert (EV3 : word_to_le_bytes 2 (edenot E v3) = word_to_le_bytes 2 (Z_to_bv 64 (nb + 256 * lvl))) by c4_ev;
    pose proof (kx_u8arr_replay bsegs E mm lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E mm lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E mm lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E mm lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 mm lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 mm lg WM) as WM';
    cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU';
    rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8 in SYB', FR', MI', MU';
    cbn [replay] in DTC'; rewrite EA1, EA2, EA3, EA4, EA5, EA6, EA7, EA8, EV1, EV3 in DTC'
   end
  end;
  destruct WDT as (_ & _ & WV);
  specialize (SYB' ltac:(repeat split; lia));
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia));
  specialize (MI' ltac:(repeat split; let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end));
  specialize (MU' ltac:(repeat split; cbn; lia));
  replace (DT + 4 * pos + 16 * k + 4) with (DT + 4 * (pos + 4 * k) + 4) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 6) with (DT + 4 * (pos + 4 * k) + 6) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 8) with (DT + 4 * (pos + 4 * k) + 8) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 10) with (DT + 4 * (pos + 4 * k) + 10) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 12) with (DT + 4 * (pos + 4 * k) + 12) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 14) with (DT + 4 * (pos + 4 * k) + 14) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 16) with (DT + 4 * (pos + 4 * k) + 16) in DTC' by lia;
  replace (DT + 4 * pos + 16 * k + 18) with (DT + 4 * (pos + 4 * k) + 18) in DTC' by lia;
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end;
  assert (PRE' : x2pref T (pos + 4 * k + 4) (map bv_unsigned bs1))
    by (unfold bs1; apply x2hb_c4_pref; try assumption; try lia; apply length_wtlb);
  destruct (x2hb_dt_of bs1) as [DTE DTBY'];
  rewrite <- DTE in DTC';
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).

Ltac c4_next :=
  let k := ident:(k) in let XH' := ident:(XH') in let bs1 := ident:(bs1) in let PRE' := ident:(PRE') in
  let KH := ident:(KH) in let KN := ident:(KN) in let QN := ident:(QN) in let HQ := ident:(HQ) in
  let qc := ident:(qc) in let HL1 := ident:(HL1) in
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ ?v8 ?v9 _ _ _ _ _ ?v15 _ _ ?v18 ?v19 _ _ _ _ _ _ _ _ _ _ ?v30 ?v31) _ _ _ _ ?mm _) =>
    assert (XH' : XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 (map bv_unsigned bs1) mm)
      by (unfold X2HBFR; eapply XHb_close; eassumption);
    replace (pos + 4 * k + 4) with (pos + 4 * (k + 1)) in PRE' by lia;
    pose proof (KH mm (map bv_unsigned bs1) v8 v9 v15 v18 v19 v30 v31 XH' PRE') as KN
  end;
  assert (QN : (DT + 4 * pos + 4 + 16 * (k + 1)) / 8 = qc + 2)
    by (rewrite HQ; replace (DT + 4 * pos + 4 + 16 * (k + 1)) with ((DT + 4 * pos + 4 + 16 * k) + 2 * 8) by lia;
        apply Z.div_add; lia);
  unfold C4S, C4PC, C4B, ASHOFF in KN; rewrite QN in KN; rewrite HL1 in KN; cbn [Z.eqb Pos.eqb] in KN;
  lazymatch type of KN with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
    replace S1 with S0; [exact KN|] end end;
  f_equal; try f_equal; c4_feq.

Lemma c4_more : forall k m dt y8 y9 y15 y18 y19 y30 y31,
  0 <= k -> k + 1 < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 4 * k) dt ->
  (forall m' dt' z8 z9 z15 z18 z19 z30 z31,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 4 * (k + 1)) dt' ->
     evtF bsegs RNG C4POST (C4S (k + 1) m' z8 z9 z15 z18 z19 z30 z31)) ->
  evtF bsegs RNG C4POST (C4S k m y8 y9 y15 y18 y19 y30 y31).
Proof.
  intros k m dt y8 y9 y15 y18 y19 y30 y31 HK CK I PRE KH.
  c4_setup.
  c4_lvl.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 1692) in let p2 := eval vm_compute in (APX2HB + 2168) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2; p3] 80%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257); KZAlign DT 4;
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 1 256; KZRange k 0 255;
          KZRange (bg + k) 0 255; KZRange (cnt - k - 2) 0 255; KZRange (2 ^ mtl - pos - 4 * k - 4) 0 4096;
          KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44); KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 16 * k) 16]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 16 * k, 16); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 16 * k, 16)]
         [(DT + 4 * pos + 4 + 16 * k, 16); (SYM + bg + k, 1)].
  all: try c4_side.
  all: kx_post_regs.
  all: c4_log.
  all: c4_next.
Qed.

Lemma c4_last : forall k m dt y8 y9 y15 y18 y19 y30 y31,
  0 <= k -> k + 1 = cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 4 * k) dt -> evtF bsegs RNG C4POST (C4S k m y8 y9 y15 y18 y19 y30 y31).
Proof.
  intros k m dt y8 y9 y15 y18 y19 y30 y31 HK CK I PRE.
  c4_setup.
  rewrite <- CK.
  c4_lvl.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       let p1 := eval vm_compute in (APX2HB + 1692) in let p2 := eval vm_compute in (APX2HB + 2168) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2; p3] 80%nat
         [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257); KZAlign DT 4;
          KZRange (2 ^ mtl) 2 4096; KZRange pos 0 4096; KZRange bg 0 256; KZRange k 0 255; KZRange (bg + k) 0 255;
          KZRange (2 ^ mtl - pos - 4 * k - 4) 0 4096; KZRange nb 0 12; KZRange bs 0 255; KZRange qc 512 (2 ^ 44);
          KZWord (A + qc) 1 0; KZWr (DT + 4 * pos + 4 + 16 * k) 16]
         [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 16 * k, 16); (A + qc, 1)] [(SYM + bg + k, 1); (DT + 4 * pos + 4 + 16 * k, 16)]
         [(DT + 4 * pos + 4 + 16 * k, 16); (SYM + bg + k, 1)].
  all: try c4_side.
  all: kx_post_regs.
  all: c4_log.
  all: unfold C4POST; replace (pos + 4 * cnt) with (pos + 4 * k + 4) by lia;
       eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma c4_body : forall k m dt y8 y9 y15 y18 y19 y30 y31,
  0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 4 * k) dt ->
  (forall m' dt' z8 z9 z15 z18 z19 z30 z31, k + 1 < cnt ->
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (pos + 4 * (k + 1)) dt' ->
     evtF bsegs RNG C4POST (C4S (k + 1) m' z8 z9 z15 z18 z19 z30 z31)) ->
  evtF bsegs RNG C4POST (C4S k m y8 y9 y15 y18 y19 y30 y31).
Proof.
  intros k m dt y8 y9 y15 y18 y19 y30 y31 HK I PRE KH.
  assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
  - eapply c4_more; [lia | exact CK | exact I | exact PRE |].
    intros m' dt' z8 z9 z15 z18 z19 z30 z31 I' PRE'. eapply KH; [exact CK | exact I' | exact PRE'].
  - eapply c4_last; [lia | exact CK | exact I | exact PRE].
Qed.

Lemma c4_loop : forall n k m dt y8 y9 y15 y18 y19 y30 y31,
  Z.of_nat n = cnt - k -> 0 <= k < cnt -> XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
  x2pref T (pos + 4 * k) dt -> evtF bsegs RNG C4POST (C4S k m y8 y9 y15 y18 y19 y30 y31).
Proof.
  induction n as [|n IH]; intros k m dt y8 y9 y15 y18 y19 y30 y31 HN HK I PRE; [lia|].
  eapply c4_body; [exact HK | exact I | exact PRE |].
  intros m' dt' z8 z9 z15 z18 z19 z30 z31 HK' I' PRE'. eapply IH; [lia | lia | exact I' | exact PRE'].
Qed.

Ltac c4_hfeq := first [ reflexivity | c4_bveq | f_equal; lia
                      | f_equal; rewrite Z.mod_small by lia; change (2 ^ (3 mod 64)) with 8; lia ].

Lemma c4_head : forall m dt x7 x28 x29 x30 x31,
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG C4POST (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                           SPF DT SYM pos bg cnt nb bs lvl 4 4 (APX2HB + 1628)).
Proof.
  intros m dt x7 x28 x29 x30 x31 I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 1628) in change (APX2HB + 1628) with v.
  pose proof HL as HL0. destruct HL0 as [HL1|HL1]; rewrite HL1.
  all: let p1 := eval vm_compute in (APX2HB + 1692) in let p2 := eval vm_compute in (APX2HB + 2168) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2; p3] 40%nat
         [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256; KZRange bs 0 255; KZRange nb 0 12; KZAlign DT 4]
         (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ ?v8 ?v9 _ _ _ _ _ ?v15 _ _ ?v18 ?v19 _ _ _ _ _ _ _ _ _ _ ?v30 ?v31) _ _ _ _ _ _) =>
    pose proof (c4_loop (Z.to_nat cnt) 0 m dt v8 v9 v15 v18 v19 v30 v31 ltac:(lia) ltac:(lia) I
                  ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact PRE)) as L0
  end.
  all: unfold C4S, C4PC, C4B, ASHOFF in L0; rewrite HL1 in L0; cbn [Z.eqb Pos.eqb] in L0;
       rewrite !Z.mul_0_r, !Z.add_0_r in L0.
  all: lazymatch type of L0 with evtF _ _ _ ?S0 => lazymatch goal with |- evtF _ _ _ ?S1 =>
         replace S1 with S0; [exact L0|] end end.
  all: f_equal; try f_equal; c4_hfeq.
Qed.
End C4.

Lemma c4_zero : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bg <= 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 pos)
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg 0 nb bs lvl 4 4 (APX2HB + 1628)).
Proof.
  intros until dt. intros HY HL HB I PRE.
  open_hyhb HY. open_xhb I. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  let v := eval vm_compute in (APX2HB + 1628) in change (APX2HB + 1628) with v.
  destruct HL as [HL|HL]; subst lvl.
  all: let p := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR | eassumption ..].
Qed.

Lemma x2hb_c4 : forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m0 SYM (SYM + 256) -> x2hb_art m0 ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 ->
  pos + 4 * cnt <= 2 ^ mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 4 * cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl 4 4 (APX2HB + 1628)).
Proof.
  intros until dt. intros HY UDT USY ART0 HP HB HC0 HBC HNB HT HM HROOM HL HBS I PRE.
  assert (CZ : cnt = 0 \/ 1 <= cnt) by lia. destruct CZ as [CZ|CZ].
  - subst cnt. rewrite Z.mul_0_r, Z.add_0_r. eapply c4_zero; [exact HY | exact HL | lia | exact I | exact PRE].
  - eapply c4_head; first [eassumption | lia].
Qed.
End CANSEC1.
