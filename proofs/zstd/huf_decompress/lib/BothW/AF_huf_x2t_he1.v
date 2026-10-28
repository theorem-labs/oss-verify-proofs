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

Lemma x2cd_pref1 : forall (T DT u nb lv : Z) (bs w2 : list byte) (w : bv 64) (a b : Z),
  0 <= u -> 4 * u + 8 <= zlen bs -> x2pref T u (map bv_unsigned bs) -> 0 <= nb <= T -> T <= 12 -> 1 <= lv <= 2 ->
  length w2 = 2%nat -> bv_unsigned w mod 65536 = nb + 256 * lv -> a = DT + 4 * u + 4 -> b = DT + 4 * u + 6 ->
  x2pref T (u + 1) (map bv_unsigned (replay1 DT (replay1 DT bs a w2) b (word_to_le_bytes 2 w))).
Proof.
  intros T DT u nb lv bs w2 w a b HU HL PRE HNB HT12 HLV LW HW -> ->.
  destruct (x2hb_dt_of bs) as [E1 HBY].
  assert (HL' : 4 * u + 8 <= zlen (map bv_unsigned bs)) by (rewrite length_map; exact HL).
  rewrite <- E1. set (dt := map bv_unsigned bs) in *. clearbody dt. clear E1 HL.
  intros v Hv. unfold c2ok.
  assert (HV : v < u \/ v = u) by lia. destruct HV as [HV|HV].
  - destruct (x2hb_znth_old dt (4 * v + 6) ltac:(lia) HBY) as [N6 R6].
    destruct (x2hb_znth_old dt (4 * v + 7) ltac:(lia) HBY) as [N7 R7].
    rewrite (x2hb_znth_map _ (4 * v + 6) (Z_to_bv 8 (Znth (4 * v + 6) dt))).
    2: { rewrite x2hb_r1_out by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         rewrite x2hb_r1_out by (rewrite ?length_map, ?LW; lia). exact N6. }
    rewrite (x2hb_znth_map _ (4 * v + 7) (Z_to_bv 8 (Znth (4 * v + 7) dt))).
    2: { rewrite x2hb_r1_out by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         rewrite x2hb_r1_out by (rewrite ?length_map, ?LW; lia). exact N7. }
    rewrite !x2hb_bv8, !Z.mod_small by lia. apply PRE; lia.
  - subst v.
    rewrite (x2hb_znth_map _ (4 * u + 6) (Z_to_bv 8 (bv_unsigned w))).
    2: { rewrite x2hb_r1_in by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         replace (Z.to_nat (DT + (4 * u + 6) - (DT + 4 * u + 6))) with O by lia. reflexivity. }
    rewrite (x2hb_znth_map _ (4 * u + 7) (Z_to_bv 8 (bv_unsigned w ≫ 8))).
    2: { rewrite x2hb_r1_in by (rewrite ?replay1_length, ?length_map, ?length_wtlb; lia).
         replace (Z.to_nat (DT + (4 * u + 7) - (DT + 4 * u + 6))) with 1%nat by lia. reflexivity. }
    rewrite !x2hb_bv8, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    revert HW. generalize (bv_unsigned w). intros W HW. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2cd_shd_ap : forall E X B k L H, ablk L H -> L <= H ->
  L <= bv_unsigned (edenot E X) <= H + 7 -> L <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 2 <= H ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 2)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 2) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF)).
Proof.
  intros E X B k L H AB LH XR BR BR2.
  pose proof (ablk_lin L H AB) as (L1 & L2 & L3 & L4).
  pose proof (ablk_shad_disj L H AB LH) as SD.
  pose proof (shad_mono L (bv_unsigned (edenot E X)) ltac:(lia)) as M1.
  pose proof (shad_mono (bv_unsigned (edenot E X)) (H + 7) ltac:(lia)) as M2.
  assert (SH : forall a, shad a = ASHOFF + a / 8) by (intro a; rewrite shad_div; lia).
  rewrite SH in M1, M2, SD. rewrite (SH (H + 7)) in SD.
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 2)) with 2. change (2 ^ (3 mod 64)) with 8.
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  unfold ASHOFF in *. repeat split; lia.
Qed.

Ltac x2cd_fpre := unfold flat, estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  cbn [Z.of_N]; change (2 ^ (3 mod 64)) with 8 in *.

Section CD.
Variables (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : amem) (SPF DT SYM pos cnt bg nb T mtl bs : Z) (syb j0 : list byte).
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
Hypothesis HTM : T <= mtl.
Hypothesis HL4 : 4 <= T - nb.
Hypothesis HROOM : pos + 2 ^ (T - nb) * cnt <= 2 ^ mtl.
Hypothesis HBS : 0 <= bs < 256.

Definition CDPOST := x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 2 ^ (T - nb) * cnt).

Definition CDI (k c0 i E q V0 V16 V32 V48 lvl : Z) (m : amem) (y13 y14 y26 y27 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (4 * 2 ^ (T - nb)))
          (Z_to_bv 64 (-1)) (Z_to_bv 64 (DT + 4 + 4 * c0))
          (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt))) y13 y14 (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 1)
          (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (DT + 4 + 4 * E)) (Z_to_bv 64 0) (Z_to_bv 64 (ASHOFF + q))
          (Z_to_bv 64 V0) (Z_to_bv 64 V48) (Z_to_bv 64 V32) (Z_to_bv 64 V16) y26 y27 (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33))
          (Z_to_bv 64 (65536 * nb + 16777216 * lvl)) (Z_to_bv 64 (4 * 2 ^ (T - nb))))
     F (Z_to_bv 64 (APX2HB + 1048)) fc None m (seg_rom bsegs).

Definition CDO (k c : Z) (m : amem) (y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 : word) (lvl : Z) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (4 * 2 ^ (T - nb)))
          (Z_to_bv 64 (-1)) (Z_to_bv 64 (DT + 4 + 4 * c)) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + (bg + cnt))) y13 y14
          (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 1) y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33))
          (Z_to_bv 64 (65536 * nb + 16777216 * lvl)) (Z_to_bv 64 (4 * 2 ^ (T - nb))))
     F (Z_to_bv 64 (APX2HB + 952)) fc None m (seg_rom bsegs).

Lemma x2cd_sh0 : forall (m : amem) lo hi G, unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi ->
  0 <= ASHOFF + G -> ASHOFF + G + 1 <= 2 ^ 64 -> bytes_at bsegs m (ASHOFF + G) [Z_to_bv 8 0].
Proof.
  intros m lo hi G U H1 H2 H3 H4. split; [exact H3|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error]. unfold mrd. replace (ASHOFF + G + Z.of_nat 0) with (ASHOFF + G) by lia.
  erewrite unpoisoned_full; [reflexivity | exact U | lia | lia].
Qed.

Ltac cd_zl :=
  let SHD := ident:(SHD) in let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HC0 := ident:(HC0) in let HP := ident:(HP) in
  let HCE := ident:(HCE) in let HE := ident:(HE) in let P2 := ident:(P2) in let HQ := ident:(HQ) in let QR := ident:(QR) in
  clear - SHD DTL DTH HP HC0 HCE HE P2 HQ QR; Z.div_mod_to_equations; lia.

Ltac cd_bnd := w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HC0 := ident:(HC0) in let HP := ident:(HP) in
  let HCE := ident:(HCE) in let HE := ident:(HE) in let P2 := ident:(P2) in
  clear - DTL DTH HP HC0 HCE HE P2; rewrite ?Z.mod_small by lia; lia.

Ltac cd_shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      let ABD := ident:(ABD) in
      apply (x2cd_shd_ap E X B k DT (DT + 4 * (1 + 2 ^ mtl))); [exact ABD | lia | cd_bnd | cd_bnd | cd_bnd]
  end.

Ltac cd_acc :=
  lazymatch goal with |- accP ?RN ?E (?a, ?n) =>
    unfold accP; cbn [fst snd];
    rewrite (flat_u E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                               unfold bv_wrap, bv_modulus; cbn [Z.of_N]; cd_zl);
    unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    lazymatch goal with R : rng RN ?lo 1 |- _ => let R3 := fresh "R3" in destruct R as (_ & _ & R3); apply R3; cd_zl end
  end.

Ltac cd_region :=
  lazymatch goal with |- region_ok ?sg ?mm ?E (zr_reg ?r) =>
    let r' := eval vm_compute in (zr_reg r) in change (region_ok sg mm E r'); unfold region_ok; cbn [fst snd];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      unfold estart, elenZ; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      split; [cd_zl|]; split; [cd_zl|];
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3;
      lazymatch goal with |- _ (Z_to_bv 64 ?x) <> None =>
        replace x with (A + Z.of_nat 0) by (cd_zl) end;
      rewrite SH3; discriminate
    end
  end.

Ltac cd_kword :=
  lazymatch goal with |- kentry_ok ?sg ?E ?mm (zk_ent (ZKWord ?za 1 (ZL 0))) =>
    let k' := eval vm_compute in (zk_ent (ZKWord za 1 (ZL 0))) in change (kentry_ok sg E mm k'); cbn [kentry_ok];
    lazymatch goal with SH : bytes_at _ _ ?A [Z_to_bv 8 0] |- _ /\ flat E ?a _ /\ _ =>
      let SH3 := fresh "SH3" in destruct SH as (_ & _ & SH3);
      let FL := fresh "FL" in
      assert (FL : flat E a 1) by (unfold flat, estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
                                   unfold bv_wrap, bv_modulus; cbn [Z.of_N]; cd_zl);
      split; [lia|]; split; [exact FL|];
      let FU := fresh "FU" in pose proof (flat_u E a 1 FL) as FU;
      replace (adenot E a) with (Z_to_bv 64 (A + Z.of_nat 0));
      [ rewrite rdn_unfold; cbv beta iota;
        specialize (SH3 O ltac:(cbn [length]; lia)); cbn [nth_error] in SH3; unfold wa in SH3; rewrite SH3;
        rewrite rdn_unfold; cbv beta iota; cbn [edenot]; reflexivity
      | apply bv_eq; rewrite FU; unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; cbn [Z.of_N]; cd_zl ]
    end
  end.

Ltac cd_side := first [ lazymatch goal with |- KHIGH + 112 <= _ <= _ => unfold KHIGH; lia end
                      | cd_shd | cd_acc | cd_region | cd_kword ].

Ltac cd_br :=
  lazymatch goal with |- branch_taken _ _ _ = _ =>
    w4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    let DTL := ident:(DTL) in let DTH := ident:(DTH) in let HC0 := ident:(HC0) in let HP := ident:(HP) in
    let HCE := ident:(HCE) in let HE := ident:(HE) in let P2 := ident:(P2) in
        clear - DTL DTH HP HC0 HCE HE P2; rewrite ?Z.mod_small by lia;
    first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
          | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.

Ltac cd_brne :=
  lazymatch goal with |- branch_taken BC_NE _ _ = _ =>
    w4ez; unfold branch_taken; rewrite ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?Z.mod_small by lia;
    lazymatch goal with |- context [?x =? ?y] =>
      destruct (Z.eqb_spec x y); cbn [negb]; first [reflexivity | exfalso; lia]
    end
  end.

Lemma x2cd_mapid : forall dt, Forall isbyte dt -> map bv_unsigned (map (Z_to_bv 8) dt) = dt.
Proof.
  induction dt as [|z dt IH]; intros HB0; [reflexivity|].
  apply Forall_cons_iff in HB0. destruct HB0 as [HZ HB']. cbn [map]. rewrite IH by exact HB'. f_equal.
  rewrite x2hb_bv8. cbv beta in HZ. apply Z.mod_small. lia.
Qed.

Ltac cd_esg := unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  rewrite ?Z.mod_small by lia; lia.

Ltac cd_pref_step nb lvl :=
  lazymatch goal with |- x2pref ?T ?n (map bv_unsigned (replay1 _ (replay1 _ _ _ _) _ _)) =>
    replace n with ((n - 1) + 1) by lia;
    eapply (x2cd_pref1 _ _ _ nb lvl);
    [ lia | rewrite ?replay1_length, ?length_map; lia | | lia | lia | lia | apply length_wtlb
    | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite ?Z.mod_small by lia; lia
    | cd_esg | cd_esg ]
  end.

Lemma cdi_cont : forall k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27,
  (lvl = 1 \/ lvl = 2) -> 0 <= k < cnt -> pos <= c0 -> 0 <= i -> c0 + 8 * i + 16 <= E -> E <= 2 ^ mtl ->
  0 <= V0 < 2 ^ 64 -> 0 <= V16 < 2 ^ 64 -> 0 <= V32 < 2 ^ 64 -> 0 <= V48 < 2 ^ 64 ->
  V16 mod 65536 = nb + 256 * lvl -> V48 mod 65536 = nb + 256 * lvl ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (c0 + 8 * i) dt ->
  (forall m' dt' z13 z14 z26 z27,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (c0 + 8 * (i + 1)) dt' ->
     evtF bsegs RNG CDPOST (CDI k c0 (i + 1) E ((DT + 4 + 4 * (c0 + 8 * (i + 1))) / 8) V0 V16 V32 V48 lvl m' z13 z14 z26 z27)) ->
  evtF bsegs RNG CDPOST (CDI k c0 i E ((DT + 4 + 4 * (c0 + 8 * i)) / 8) V0 V16 V32 V48 lvl m y13 y14 y26 y27).
Proof.
  intros k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27 HL HK HC0' HI HCE HE HV0 HV16 HV32 HV48 W16 W48 I PRE KI.
  assert (HC0 : pos <= c0 /\ 0 <= i) by lia. assert (HLV : 1 <= lvl <= 2) by lia.
  remember ((DT + 4 + 4 * (c0 + 8 * i)) / 8) as q eqn:HQ.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  pose proof (ablk_shad_disj _ _ ABD ltac:(lia)) as SHD. rewrite !shad_div in SHD.
  assert (QR : 512 <= q <= 2 ^ 44) by (subst q; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia).
  assert (RQ : rng RNG (ASHOFF + q) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst q; clear - DTL DTH HP HC0 HCE HE P2;
        Z.div_mod_to_equations; lia).
  assert (RW1 : rng RNG (DT + 4 + 4 * c0 + 32 * i) 32) by (eapply rng_sub; [exact RDT | lia | lia]).
  assert (SH0 : bytes_at bsegs m (ASHOFF + q) [Z_to_bv 8 0])
    by (subst q; apply x2cd_sh0 with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia ..]).
  unfold CDI, ASHOFF in *. let v := eval vm_compute in (APX2HB + 1048) in change (APX2HB + 1048) with v.
  (let A := eval cbv [ASHOFF] in ASHOFF in
  let p1 := eval vm_compute in (APX2HB + 952) in let p2 := eval vm_compute in (APX2HB + 1048) in
  let p3 := eval vm_compute in (APX2HB + 2428) in
  kx_runFm [p1; p2; p3] 200%nat
    [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
     KZRange (2 ^ mtl) 2 4096; KZRange c0 0 4096; KZRange i 0 512; KZRange E 16 4096; KZRange (E - c0 - 8 * i - 16) 0 4096;
     KZRange k 0 255; KZRange (bg + k) 0 255; KZRange cnt 1 256; KZRange nb 0 12; KZRange lvl 1 2;
     KZRange V0 0 (2^64 - 1); KZRange V16 0 (2^64 - 1); KZRange V32 0 (2^64 - 1); KZRange V48 0 (2^64 - 1);
     KZRange q 512 (2^44); KZWord (A + q) 1 0; KZWr (DT + 4 + 4 * c0 + 32 * i) 32]
    [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)]).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [cd_side | cd_br] end).
  kx_post_regs.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
    pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM'
  end.
  cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU'.
  destruct WDT as (_ & _ & WV).
  specialize (SYB' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; unfold estart; cbn [a_base a_off]; w4ez;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (MI' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia;
    repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
  specialize (MU' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; cbn; lia)).
  cbn [replay] in DTC'.
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
  assert (PRE' : x2pref T (c0 + 8 * (i + 1)) (map bv_unsigned bs1)).
  { unfold bs1. do 8 (cd_pref_step nb lvl).
    rewrite x2cd_mapid by assumption. replace (c0 + 8 * (i + 1) - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1) with (c0 + 8 * i) by lia.
    exact PRE. }
  destruct (x2hb_dt_of bs1) as [DTE DTBY'].
  rewrite <- DTE in DTC'.
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
  replace (DT + 4 * c0 + 4) with (DT + 4 + 4 * c0) by lia.
  replace (SYM + (bg + k)) with (SYM + bg + k) by lia.
  replace (32 * i + 32) with (32 * (i + 1)) by lia.
  replace (DT + 4 * E + 4) with (DT + 4 + 4 * E) by lia.
  let A := eval cbv [ASHOFF] in ASHOFF in
  lazymatch goal with |- context [Z_to_bv 64 (q + ?C)] =>
    replace (q + C) with (A + (DT + 4 + 4 * (c0 + 8 * (i + 1))) / 8) by (subst q; Z.div_mod_to_equations; lia)
  end.
  lazymatch goal with |- context [Z_to_bv 64 (?a * lvl + ?b * nb)] => replace (a * lvl + b * nb) with (b * nb + a * lvl) by lia end.
  let v := eval vm_compute in (APX2HB + 1048) in change (APX2HB + 1048) with v in KI.
  eapply KI; [| exact PRE'].
  unfold X2HBFR. eapply XHb_close; eassumption.
Qed.

Lemma cdi_exo : forall k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27,
  (lvl = 1 \/ lvl = 2) -> 0 <= k -> k + 1 < cnt -> pos <= c0 -> 0 <= i -> E = c0 + 8 * i + 8 -> E <= 2 ^ mtl ->
  0 <= V0 < 2 ^ 64 -> 0 <= V16 < 2 ^ 64 -> 0 <= V32 < 2 ^ 64 -> 0 <= V48 < 2 ^ 64 ->
  V16 mod 65536 = nb + 256 * lvl -> V48 mod 65536 = nb + 256 * lvl ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (c0 + 8 * i) dt ->
  (forall m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T E dt' ->
     evtF bsegs RNG CDPOST (CDO (k + 1) E m' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 lvl)) ->
  evtF bsegs RNG CDPOST (CDI k c0 i E ((DT + 4 + 4 * (c0 + 8 * i)) / 8) V0 V16 V32 V48 lvl m y13 y14 y26 y27).
Proof.
  intros k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27 HL HK0 HK2 HC0' HI HEQ HE HV0 HV16 HV32 HV48 W16 W48 I PRE KO.
  assert (HC0 : pos <= c0 /\ 0 <= i) by lia. assert (HLV : 1 <= lvl <= 2) by lia.
  assert (HCE : c0 + 8 * i + 8 <= E) by lia. assert (HK : 0 <= k < cnt) by lia.
  remember ((DT + 4 + 4 * (c0 + 8 * i)) / 8) as q eqn:HQ.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  pose proof (ablk_shad_disj _ _ ABD ltac:(lia)) as SHD. rewrite !shad_div in SHD.
  assert (QR : 512 <= q <= 2 ^ 44) by (subst q; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia).
  assert (RQ : rng RNG (ASHOFF + q) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst q; clear - DTL DTH HP HC0 HCE HE P2;
        Z.div_mod_to_equations; lia).
  assert (RW1 : rng RNG (DT + 4 + 4 * c0 + 32 * i) 32) by (eapply rng_sub; [exact RDT | lia | lia]).
  assert (SH0 : bytes_at bsegs m (ASHOFF + q) [Z_to_bv 8 0])
    by (subst q; apply x2cd_sh0 with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia ..]).
  unfold CDI, CDO, ASHOFF in *. let v := eval vm_compute in (APX2HB + 1048) in change (APX2HB + 1048) with v.
  (let A := eval cbv [ASHOFF] in ASHOFF in
  let p1 := eval vm_compute in (APX2HB + 952) in let p2 := eval vm_compute in (APX2HB + 1048) in
  let p3 := eval vm_compute in (APX2HB + 2428) in
  kx_runFmd [p1; p2; p3] 200%nat [true]
    [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
     KZRange (2 ^ mtl) 2 4096; KZRange c0 0 4096; KZRange i 0 512; KZRange E 8 4096; KZRange (E - c0 - 8 * i - 8) 0 0;
     KZRange (cnt - k - 2) 0 255; KZRange k 0 255; KZRange (bg + k) 0 255; KZRange cnt 1 256; KZRange nb 0 12; KZRange lvl 1 2;
     KZRange V0 0 (2^64 - 1); KZRange V16 0 (2^64 - 1); KZRange V32 0 (2^64 - 1); KZRange V48 0 (2^64 - 1);
     KZRange q 512 (2^44); KZWord (A + q) 1 0; KZWr (DT + 4 + 4 * c0 + 32 * i) 32]
    [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)]).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [cd_side | cd_br | cd_brne] end).
  kx_post_regs.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
    pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM'
  end.
  cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU'.
  destruct WDT as (_ & _ & WV).
  specialize (SYB' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; unfold estart; cbn [a_base a_off]; w4ez;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (MI' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia;
    repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
  specialize (MU' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; cbn; lia)).
  cbn [replay] in DTC'.
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
  assert (PRE' : x2pref T (c0 + 8 * (i + 1)) (map bv_unsigned bs1)).
  { unfold bs1. do 8 (cd_pref_step nb lvl).
    rewrite x2cd_mapid by assumption. replace (c0 + 8 * (i + 1) - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1) with (c0 + 8 * i) by lia.
    exact PRE. }
  destruct (x2hb_dt_of bs1) as [DTE DTBY'].
  rewrite <- DTE in DTC'.
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
  replace (c0 + 8 * (i + 1)) with E in PRE' by lia.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a10) (Z_to_bv 64 ?a11)
                                          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace a10 with (DT + 4 + 4 * E) by lia; replace a11 with (SYM + bg + (k + 1)) by lia
  end.
  lazymatch goal with |- context [Z_to_bv 64 (?a * lvl + ?b * nb)] => replace (a * lvl + b * nb) with (b * nb + a * lvl) by lia end.
  let v := eval vm_compute in (APX2HB + 952) in change (APX2HB + 952) with v in KO.
  eapply KO; [| exact PRE'].
  unfold X2HBFR. eapply XHb_close; eassumption.
Qed.

Lemma cdi_exr : forall k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27,
  (lvl = 1 \/ lvl = 2) -> 0 <= k -> k + 1 = cnt -> pos <= c0 -> 0 <= i -> E = c0 + 8 * i + 8 -> E <= 2 ^ mtl ->
  E = pos + 2 ^ (T - nb) * cnt ->
  0 <= V0 < 2 ^ 64 -> 0 <= V16 < 2 ^ 64 -> 0 <= V32 < 2 ^ 64 -> 0 <= V48 < 2 ^ 64 ->
  V16 mod 65536 = nb + 256 * lvl -> V48 mod 65536 = nb + 256 * lvl ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (c0 + 8 * i) dt ->
  evtF bsegs RNG CDPOST (CDI k c0 i E ((DT + 4 + 4 * (c0 + 8 * i)) / 8) V0 V16 V32 V48 lvl m y13 y14 y26 y27).
Proof.
  intros k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27 HL HK0 HK2 HC0' HI HEQ HE HEND HV0 HV16 HV32 HV48 W16 W48 I PRE.
  assert (HC0 : pos <= c0 /\ 0 <= i) by lia. assert (HLV : 1 <= lvl <= 2) by lia.
  assert (HCE : c0 + 8 * i + 8 <= E) by lia. assert (HK : 0 <= k < cnt) by lia.
  remember ((DT + 4 + 4 * (c0 + 8 * i)) / 8) as q eqn:HQ.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  pose proof (ablk_shad_disj _ _ ABD ltac:(lia)) as SHD. rewrite !shad_div in SHD.
  assert (QR : 512 <= q <= 2 ^ 44) by (subst q; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia).
  assert (RQ : rng RNG (ASHOFF + q) 1)
    by (eapply rng_sub; [exact RSDT | |]; rewrite shad_div; subst q; clear - DTL DTH HP HC0 HCE HE P2;
        Z.div_mod_to_equations; lia).
  assert (RW1 : rng RNG (DT + 4 + 4 * c0 + 32 * i) 32) by (eapply rng_sub; [exact RDT | lia | lia]).
  assert (SH0 : bytes_at bsegs m (ASHOFF + q) [Z_to_bv 8 0])
    by (subst q; apply x2cd_sh0 with DT (DT + 4 * (1 + 2 ^ mtl));
        [exact UDTm | unfold ASHOFF; clear - DTL DTH HP HC0 HCE HE P2; Z.div_mod_to_equations; lia ..]).
  unfold CDI, ASHOFF in *. let v := eval vm_compute in (APX2HB + 1048) in change (APX2HB + 1048) with v.
  (let A := eval cbv [ASHOFF] in ASHOFF in
  let p1 := eval vm_compute in (APX2HB + 952) in let p2 := eval vm_compute in (APX2HB + 1048) in
  let p3 := eval vm_compute in (APX2HB + 2428) in
  kx_runFm [p1; p2; p3] 200%nat
    [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
     KZRange (2 ^ mtl) 2 4096; KZRange c0 0 4096; KZRange i 0 512; KZRange E 8 4096; KZRange (E - c0 - 8 * i - 8) 0 0;
     KZRange (cnt - k - 1) 0 0; KZRange k 0 255; KZRange (bg + k) 0 255; KZRange cnt 1 256; KZRange nb 0 12; KZRange lvl 1 2;
     KZRange V0 0 (2^64 - 1); KZRange V16 0 (2^64 - 1); KZRange V32 0 (2^64 - 1); KZRange V48 0 (2^64 - 1);
     KZRange q 512 (2^44); KZWord (A + q) 1 0; KZWr (DT + 4 + 4 * c0 + 32 * i) 32]
    [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)] [(DT + 4 + 4 * c0 + 32 * i, 32)]).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [cd_side | cd_br | cd_brne] end).
  kx_post_regs.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m ?lg) _) =>
    pose proof (kx_u8arr_replay bsegs E m lg DT _ DTC KXLF) as DTC';
    pose proof (kx_bytes_at_log bsegs E m lg SYM syb SYB KXLF) as SYB';
    pose proof (kx_rw_cells_log bsegs E m lg _ _ FR KXLF) as FR';
    pose proof (kx_mem_inv_log bsegs E m lg MI KXLF) as MI';
    pose proof (kx_munch_log E _ m0 m lg MU KXLF) as MU';
    pose proof (kx_wmono_log bsegs E m0 m lg WM) as WM'
  end.
  cbn [log_apart log_inside log_wr] in SYB', FR', MI', MU'.
  destruct WDT as (_ & _ & WV).
  specialize (SYB' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; unfold estart; cbn [a_base a_off]; w4ez;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; lia)).
  specialize (MI' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia;
    repeat split; intros j Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj;
    lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WV; lia end)).
  specialize (MU' ltac:(unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    cbn [Z.of_N]; rewrite ?Z.mod_small by lia; repeat split; cbn; lia)).
  cbn [replay] in DTC'.
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
  assert (PRE' : x2pref T (c0 + 8 * (i + 1)) (map bv_unsigned bs1)).
  { unfold bs1. do 8 (cd_pref_step nb lvl).
    rewrite x2cd_mapid by assumption. replace (c0 + 8 * (i + 1) - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1) with (c0 + 8 * i) by lia.
    exact PRE. }
  destruct (x2hb_dt_of bs1) as [DTE DTBY'].
  rewrite <- DTE in DTC'.
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, !replay1_length, length_map; exact DTLEN).
  replace (c0 + 8 * (i + 1)) with (pos + 2 ^ (T - nb) * cnt) in PRE' by lia.
  unfold CDPOST.
  eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR' | eassumption ..].
Qed.

Lemma cdi_loop : forall n k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27,
  E = c0 + 8 * i + 8 * Z.of_nat (S n) ->
  (lvl = 1 \/ lvl = 2) -> 0 <= k < cnt -> pos <= c0 -> 0 <= i -> E <= 2 ^ mtl -> E = pos + 2 ^ (T - nb) * (k + 1) ->
  0 <= V0 < 2 ^ 64 -> 0 <= V16 < 2 ^ 64 -> 0 <= V32 < 2 ^ 64 -> 0 <= V48 < 2 ^ 64 ->
  V16 mod 65536 = nb + 256 * lvl -> V48 mod 65536 = nb + 256 * lvl ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (c0 + 8 * i) dt ->
  (k + 1 < cnt -> forall m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T E dt' ->
     evtF bsegs RNG CDPOST (CDO (k + 1) E m' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 lvl)) ->
  evtF bsegs RNG CDPOST (CDI k c0 i E ((DT + 4 + 4 * (c0 + 8 * i)) / 8) V0 V16 V32 V48 lvl m y13 y14 y26 y27).
Proof.
  induction n as [|n IH];
    intros k c0 i E V0 V16 V32 V48 lvl m dt y13 y14 y26 y27 HN HL HK HC0 HI HE HEK HV0 HV16 HV32 HV48 W16 W48 I PRE KO.
  - assert (CK : k + 1 < cnt \/ k + 1 = cnt) by lia. destruct CK as [CK|CK].
    + apply cdi_exo with dt; try assumption; try lia.
      intros m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 I' PRE'.
      exact (KO CK m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 I' PRE').
    + apply cdi_exr with dt; try assumption; try lia. all: rewrite <- CK; exact HEK.
  - apply cdi_cont with dt; try assumption; try lia.
    intros m' dt' z13 z14 z26 z27 I' PRE'. apply IH with dt'; try assumption; lia.
Qed.

End CD.
End CANSEC1.
