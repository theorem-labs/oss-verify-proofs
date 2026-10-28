(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg
  AF_huf_x2t_bgeo.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure AF_huf_x2t_bl2i.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Ltac hd_pcoff := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => let p := eval vm_compute in (n - 0x81e48) in p end.
Ltac hd_at_stop stops := let p := hd_pcoff in let b := eval vm_compute in (existsb (Z.eqb p) stops) in
  lazymatch b with true => idtac | false => fail end.
Ltac hd_walk stops := repeat (tryif hd_at_stop stops then fail else zstep).
Ltac hd_ifpc := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Definition HdHide (P : Prop) : Prop := P.
Ltac hd_hide H := let t := type of H in change (HdHide t) in H.
Ltac hd_hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (HdHide (A \/ B)) in H end.
Ltac hd_clr := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | context [rw_cells _ _ _ _] => clear H | context [u8arr _ _ _ _] => clear H | context [u32arr _ _ _ _] => clear H
  | context [stk _ _ _ _] => clear H | context [munch _ _ _] => clear H | context [wmono _ _ _] => clear H
  | context [mem_inv _ _] => clear H | context [HdHide _] => clear H | context [Z.modulo _ _] => clear H
  | context [rng _ _ _] => clear H | context [ablk _ _] => clear H | context [rng_aimg _] => clear H
  end end.
Ltac hd_p2 := repeat match goal with |- context [2 ^ ?k] => lazymatch k with Zpos _ => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end end.
Ltac hd_zn := repeat first
  [ match goal with |- context [Z.shiftl ?x ?k] => rewrite (Z.shiftl_mul_pow2 x k) by lia end
  | progress hd_p2
  | match goal with |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia end
  | match goal with E : Znth ?i ?l = _ |- context [Znth ?i ?l] => rewrite E end
  | match goal with |- context [bv_swrap 32 ?z] => rewrite (FseWalkKit.swrap32_small z) by lia end
  | match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (FseRdKit2.sx32_small z) by lia end ].
Ltac hd_znh H := repeat first
  [ match type of H with context [Z.shiftl ?x ?k] => rewrite (Z.shiftl_mul_pow2 x k) in H by lia end
  | match type of H with context [2 ^ ?k] => lazymatch k with Zpos _ => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in H end end
  | match type of H with context [?a mod ?b] => rewrite (Z.mod_small a b) in H by (hd_clr; lia) end
  | match type of H with context [bv_swrap 32 ?z] => rewrite (FseWalkKit.swrap32_small z) in H by lia end ].
Ltac hd_knorm := repeat match goal with
  | H : ?a < ?b |- _ => progress hd_znh H
  | H : ?a <= ?b |- _ => progress hd_znh H
  | H : ~ _ |- _ => progress hd_znh H
  | H : @eq Z _ _ |- _ => progress hd_znh H
  end.
Ltac hd_regeq := lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
      first [ reflexivity | f_equal; lia
            | f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; change (2^1) with 2; rewrite ?Z.mod_small by lia;
              rewrite ?FseWalkKit.swrap32_small by lia; lia
            | f_equal; hd_zn; lia
            | apply Z_to_bv_eqm; hd_clr;
              try (lazymatch goal with |- context [Z.lxor ?x ?c] => change c with (2^64 - 1); rewrite (KXS.lxor_ones64 x) by lia end);
              try (lazymatch goal with |- context [Z.lxor ?x ?c] => change c with (2^64 - 1); rewrite (KXS.lxor_ones64 x) by lia end);
              rewrite ?FseWalkKit.swrap32_small by lia; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
              Z.div_mod_to_equations; lia ]
  | |- _ = _ => first [ reflexivity | hd_zn; first [ reflexivity | f_equal; lia ] ]
  end.
Ltac hd_cells := repeat lazymatch goal with
  | |- cons _ _ = cons _ _ => refine (f_equal2 (@cons _) _ _); [ first [ reflexivity | f_equal; hd_regeq ] | ]
  | |- nil = nil => reflexivity
  end.
Ltac hd_frq FR :=
  unfold X2BF;
  lazymatch type of FR with rw_cells _ _ _ ?cs =>
    lazymatch goal with |- rw_cells _ _ _ ?cs' => replace cs' with cs; [exact FR | hd_cells] end end.
Ltac hd_eqs := lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = _ => f_equal; try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal; try hd_regeq end)
  end.

Lemma hd_swr : forall x M c, M mod 4294967296 = 0 -> 0 < M -> -2147483648 <= x + c < 2147483648 ->
  bv_swrap 32 (x mod M + c) = x + c.
Proof.
  intros x M c HM HP HR.
  assert (EM : M = 4294967296 * (M / 4294967296)) by (pose proof (Z.div_mod M 4294967296 ltac:(lia)); lia).
  rewrite (Z.mod_eq x M) by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite EM at 1. rewrite <- Z.mul_assoc. generalize (M / 4294967296 * (x / M)). intros j.
  clear HM HP EM. Z.div_mod_to_equations. lia.
Qed.

Lemma hd_zx32 : forall x, 0 <= x < 2 ^ 32 -> bv_unsigned (zx32 (Z_to_bv 64 x)) = x.
Proof.
  intros x H. unfold zx32. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small x (2 ^ 32)) by lia. rewrite (Z.mod_small x (2 ^ 64)) by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X2B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF hdw r mtl : Z).
  Hypothesis HY : x2B_hyps RNG SPV SPA lo DT WK wksz FF mtl.
  Hypothesis UDT : unpoisoned m5 DT (DT + 4 * (1 + 2 ^ mtl)).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : x2hb_art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Hypothesis HM : hdw mod 256 = mtl.
  Hypothesis HR : 0 <= hdw < 2^32.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis X2HB : x2hb_stmt.
  Variable POST : machine_state -> Prop.
  Local Ltac x2_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : x2hb_art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x2_unp_dtM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UDT m2 MU) as UDT1;
        pose proof (x2_unp_wkM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x2_artM RNG m5 SPV SPA lo DT WK wksz FF mtl HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x2_open :=
    open_hx2b HY; unfold KHIGH in *;
    pose proof (x2_bands RNG SPV SPA lo DT WK wksz FF mtl HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    pose proof (x2_rsta RNG SPV SPA lo DT WK wksz FF mtl HY) as RSTA;
    pose proof (x2b_dtbB mtl (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY)) as (DTBR & P2R);
    lazymatch goal with H1 : DT + 4 * (1 + 2 ^ mtl) <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 528 <= SPA <= SPV - 512 |- _ =>
      assert (SDSA : DT + 4 * (1 + 2 ^ mtl) <= SPA - 5408 \/ SPA + 408 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA - 5408 \/ SPA + 408 <= WK) by (clear - H2 H3 H4; lia) end;
    x2_reunp.
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5408) (2^47 - 528); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x60f000 (2^47 - 12); KZRange WK 0x60f000 (2^47 - 2124); KZRange wksz 2124 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZRange hdw 0 (2^32); KZRange mtl 1 12; KZRange (2 ^ mtl) 2 4096; KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4;
     KZDisj DT (4 * (1 + 2 ^ mtl)) (SPA - 112) 520; KZDisj WK wksz (SPA - 112) 520; KZDisj DT (4 * (1 + 2 ^ mtl)) WK wksz;
     KZDisj WK wksz FF 64; KZDisj DT (4 * (1 + 2 ^ mtl)) FF 64; KZDisj (SPA - 112) 520 FF 64] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 xs6 xs7
             xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis TLM : tl <= mtl.
  Notation TT := (TTB tl mtl).
  Lemma TT_range : 1 <= tl <= 12 -> tl <= TT <= mtl /\ Z.min mtl 11 <= TT.
  Proof. intros H. pose proof (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY). apply TTB_range; lia. Qed.
  Local Ltac x2_fwd L := intros; pose proof (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY); eapply L; try eassumption; lia.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof. x2_fwd AF_huf_x2t_bpure.rank_small'. Qed.
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Lemma rdn_sh0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
    rdn bsegs m (wa (shad p)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof.
    intros m X n p (H0 & H1 & H) Hp Hg. cbn [rdn]. replace (shad p) with (ASHOFF + p / 8) by (rewrite shad_div; lia).
    destruct (H (p / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
      as (b & Hb & Hok).
    rewrite Hb. rewrite (gran_ok_full _ _ Hok) by (Z.div_mod_to_equations; lia). reflexivity.
  Qed.
  Notation XS1 w := (xs1 rank w).
  Lemma xs1_bounds : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof. x2_fwd AF_huf_x2t_bpure.xs1_bounds'. Qed.
  Variables (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word).
  Variables (xnv xflv : word).
  Section FM.
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Notation RV0 w := (rv0 rank tl TT w).
  Notation RVC c w := (rvc rank tl TT c w).
  Notation RINV := (AF_huf_x2t_bpure.RINV rank).
  Notation SINV := (AF_huf_x2t_bpure.SINV hw rank nbs maxW).
  Notation RSF := (AF_huf_x2t_bpure.RSF rank maxW).
  Notation VINV := (AF_huf_x2t_bpure.VINV rank tl mtl).
  Notation ROWS := (AF_huf_x2t_bpure.ROWS rank tl mtl maxW).
  Notation RVX := (AF_huf_x2t_bpure.RVX rank tl mtl maxW).
  Lemma sinv0 : forall rs0, RINV (maxW + 1) rs0 -> Znth 1 rs0 = XS1 (maxW + 1) -> SINV 0 rs0.
  Proof. x2_fwd AF_huf_x2t_bpure.sinv0. Qed.
  Lemma sort_unit : forall j rs0, 0 <= j < nbs -> SINV j rs0 -> zlen rs0 = 15 ->
    0 <= Znth j hw <= maxW /\ 0 <= Znth (Znth j hw + 1) rs0 /\ Znth (Znth j hw + 1) rs0 + 1 <= nbs
    /\ SINV (j + 1) (Zupd (Znth j hw + 1) (Znth (Znth j hw + 1) rs0 + 1) rs0).
  Proof. x2_fwd AF_huf_x2t_bpure.sort_unit. Qed.
  Lemma rsf_of_sinv : forall rs0, SINV nbs rs0 -> zlen rs0 = 15 -> RSF (Zupd 1 0 rs0).
  Proof. x2_fwd AF_huf_x2t_bpure.rsf_of_sinv. Qed.
  Lemma rv0_bounds : forall w, 1 <= w <= maxW + 1 -> 0 <= RV0 w <= 2 ^ mtl /\ RV0 (maxW + 1) = 2^TT.
  Proof. x2_fwd AF_huf_x2t_bpure.rv0_bounds. Qed.
  Lemma rows0 : forall c rv, c <= tl + 1 - maxW -> VINV (maxW + 1) rv -> ROWS c 1 rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rows0. Qed.
  Lemma rows_next : forall c rv, ROWS c (maxW + 1) rv -> ROWS (c + 1) 1 rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rows_next. Qed.
  Lemma rvc_val : forall c w, 0 <= c -> 1 <= w <= maxW + 1 -> 0 <= RVC c w <= RV0 w /\ RVC c w = RV0 w / 2^c.
  Proof. x2_fwd AF_huf_x2t_bpure.rvc_val. Qed.
  Lemma rvx_of_rows : forall rv, ROWS (TT - (tl + 1 - maxW) + 1) 1 rv -> RVX rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rvx_of_rows. Qed.
  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 2 ^ mtl /\ 1 <= 2 ^ e <= 2 ^ mtl.
  Proof. x2_fwd AF_huf_x2t_bpure.l1_facts. Qed.
  Section FX.
  Variables (rs0 rv : list Z) (syb : list byte).
  Hypothesis RSFX : RSF rs0.
  Hypothesis RVXX : RVX rv.
  Notation XBF v152 v160 v192 v208 v264 v304 v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank (Z_to_bv 64 (16777216 * (hdw mod 2 ^ 64 / 16777216))) (Z_to_bv 64 mtl) (Z_to_bv 64 r) v24 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (tl + 1 - TT))
        (Z_to_bv 64 223338299392) (Z_to_bv 64 (18446744073709551615 - (DT + 4))) (Z_to_bv 64 (DT + 12)) (Z_to_bv 64 (DT + 27)) (Z_to_bv 64 (DT + 20)) (Z_to_bv 64 (DT + 19))
        (Z_to_bv 64 (DT + 35)) (Z_to_bv 64 (DT + 28)) (Z_to_bv 64 (DT + 11)) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (18446744073709551615 - WK))
        v152 v160 v192 v208 v224 v232 v240 v248 v256 v264 v272 v280 v288 (Z_to_bv 64 maxW) v304 v312 v320 v328 (Z_to_bv 64 (DT + 4)) v344 v360 (Z_to_bv 64 TT) v376 k384 k392
        dt rs0 syb rv mm) (only parsing).
  Local Ltac fr_norm FR :=
    try replace (Z_to_bv 64 (-1 * TT + tl + 1)) with (Z_to_bv 64 (tl + 1 - TT)) in FR by (f_equal; lia);
    try replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 (18446744073709551615 - (DT + 4))) in FR by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  Notation STLE pc mm w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
           xra x5 x6 x7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST
       (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (WK + 4 * w)) (Z_to_bv 64 (TT - (tl + 1 - w))) (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - TT)))) (Z_to_bv 64 (tl + 1 - w))
           (Z_to_bv 64 (4 * w)) (Z_to_bv 64 (18446744073709551615 - WK)) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (XS1 w))
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STLT mm w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
           xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82560 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Notation XL w minW len v320 v328 v344 dt mm :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         (Z_to_bv 64 (4294967296 * (tl + 1 - w))) (Z_to_bv 64 (maxW + 1 - minW)) (Z_to_bv 64 (2 * tl + 2 - w - minW)) (Z_to_bv 64 (4 * minW))
         (Z_to_bv 64 (65536 * (tl + 1 - w) + 16777216)) (Z_to_bv 64 (4 * minW)) (Z_to_bv 64 (WK + 52 * (tl + 1 - w) + 4 * minW))
         (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 minW) (Z_to_bv 64 len) v320 v328 v344
         (Z_to_bv 64 (WK + 52 * (tl + 1 - w))) (Z_to_bv 64 (18446744073709551615 - (WK + 52 * (tl + 1 - w)))) dt mm) (only parsing).
  Notation STSH mm w minW len st s v320 v328 v344 dt xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len v320 v328 v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82758 mm xra (Z_to_bv 64 st) x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 s)
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Lemma l2_facts : forall w e minW, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> tl - maxW + 1 <= e -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 2 ^ mtl /\ 2 <= 2 ^ e <= 2 ^ mtl /\ 1 <= minW <= maxW /\ 1 <= e <= mtl - 1.
  Proof.
    intros w e minW HW HE HLE HMIN. pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l1_facts w e HW HE ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    assert (2 <= 2 ^ e) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    repeat split; try lia.
  Qed.
  Lemma l2x_facts : forall w len minW, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    RV0 (w + 1) = RV0 w + (XS1 (w + 1) - XS1 w) * len /\ 2 <= len <= 2 ^ (mtl - 1) /\ 1 <= minW <= maxW /\ tl + 1 - w + (tl + 1 - TT) <= minW
    /\ RVC (tl + 1 - w) (maxW + 1) = len /\ 0 <= RVC (tl + 1 - w) minW <= len /\ RVC (tl + 1 - w) 1 = 0.
  Proof. x2_fwd AF_huf_x2t_bpure.l2x_facts. Qed.
  Lemma w2_facts : forall w len minW w2 len2, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> minW <= w2 <= maxW -> len2 = 2 ^ (TT - (tl + 1 - w) - (tl + 1 - w2)) ->
    0 <= XS1 w2 /\ XS1 (w2 + 1) <= 256 /\ XS1 (w2 + 1) = XS1 w2 + Znth w2 rank /\ 0 <= Znth w2 rank
    /\ 0 <= RVC (tl + 1 - w) w2 /\ RVC (tl + 1 - w) (w2 + 1) = RVC (tl + 1 - w) w2 + (XS1 (w2 + 1) - XS1 w2) * len2 /\ RVC (tl + 1 - w) (w2 + 1) <= len
    /\ 1 <= len2 <= len /\ 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= mtl - 1 /\ RVC (tl + 1 - w) w2 <= len.
  Proof. x2_fwd AF_huf_x2t_bpure.w2_facts. Qed.
  Notation STSK mm w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x827c4 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (4 * st)) (Z_to_bv 64 sv)
           xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STJ mm w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82abc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 (Z_to_bv 64 sv)
           xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STW2 mm w minW len st s sv w2 v344 dt xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82b00 mm xra x5 x6 x7 xa0 (Z_to_bv 64 (4 * w2)) xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 (Z_to_bv 64 sv)
           (Z_to_bv 64 (2 * tl + 2 - w - w2)) (Z_to_bv 64 (maxW + 1 - w2)) x28 x29 x30 x31)) (only parsing).
  Notation STSL mm w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82ac8 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STLT2 mm w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82560 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Lemma signed_small : forall z, -100 <= z <= 100 -> bv_signed (Z_to_bv 64 z) = z.
  Proof.
    intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (2 ^ 63) with 9223372036854775808. destruct (Z.ltb_spec0 (z mod 18446744073709551616) 9223372036854775808); Z.div_mod_to_equations; lia.
  Qed.

  Notation XBW dt mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank (Z_to_bv 64 (16777216 * (hdw mod 2 ^ 64 / 16777216))) (Z_to_bv 64 mtl) (Z_to_bv 64 r) k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112
        (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (18446744073709551615 - WK)) k152 k160 k192 (Z_to_bv 64 tl)
        k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 (Z_to_bv 64 (DT + 4)) k344 k360 (Z_to_bv 64 TT) k376 k384 k392 dt rs0 syb rv mm) (only parsing).
  Notation STQ mm xra x5 x6 x7 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 :=
    (ST 0x824b0 mm xra x5 x6 x7 xa0 xa1 (Z_to_bv 64 (TT - tl + maxW)) (Z_to_bv 64 (4294967296 * (maxW + 1))) xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 WK) (Z_to_bv 64 maxW) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11
        x28 x29 x30 (Z_to_bv 64 (tl - maxW + 1)))
    (only parsing).
  Notation STEX mm v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (tl + 1 - maxW + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - (maxW + 1))) (Z_to_bv 64 (tl + 1 - (maxW + 1))) (Z_to_bv 64 maxW)
         (Z_to_bv 64 (XS1 (maxW + 1))) v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST (ST 0x82cac mm xra x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STHD mm w v152 v160 v264 v304 v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
           xra x5 x6 x7 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF v152 v160 (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) v264 v304 v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82594 mm xra x5 x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 w) xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Ltac hd_prune K :=
    try (exfalso; lia);
    try (exfalso; rewrite ?unsigned_lit in K by lia; lia);
    try (exfalso; rewrite ?Z.mod_small in K by lia; lia).
  Ltac hd_go stops :=
    hd_walk stops;
    try (hd_ifpc; let K := fresh "K" in bcase K; hd_prune K; hd_go stops).

  Lemma x2_latchB : forall m1 (dt : list Z) (w : Z) v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW ->
    (forall m2 ya0 ya1 ya2 ya5 ya6 ya7, w + 1 <= maxW ->
       STHD m2 (w + 1) (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
            v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
            xra x5 x6 x7 ya0 ya1 ya2 ya5 ya6 ya7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31) ->
    (forall m2 ya1 ya2 ya3 ya4 ya5 ya6 ya7, w = maxW ->
       XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - (w + 1))) (Z_to_bv 64 (tl + 1 - (w + 1))) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
           v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt m2 ->
       evtF bsegs RNG POST (ST 0x82cac m2 xra x5 x6 x7 (Z_to_bv 64 DT) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                              xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) ->
    STLT m1 w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW KH KE I. open_xbb I. open_hx2b HY. hd_hide_disj.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    pose proof (munch_refl [(SPA, SPA + 408)] m1) as MU1. pose proof (wmono_refl bsegs m1) as WM1.
    hd_hide DTC. hd_hide HWC. hd_hide RK. hd_hide RS0. hd_hide SYC. hd_hide RV. hd_hide NBC.
    hd_go [1868; 3684; 3916].
    all: unfold HdHide in *.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m1 mm MU1 WM1 end.
    all: try kx_mkR_foldF.
    all: hd_knorm.
    all: lazymatch goal with |- evtF _ _ _ ?s => lazymatch s with MS _ _ _ _ _ ?mm _ =>
           let EQS := fresh "EQS" in eassert (EQS : _ = s);
           [| rewrite <- EQS; first [ eapply (KH mm); [ first [ hd_clr; lia | lia ] | close_xbb ]
                                    | eapply (KE mm); [ first [ hd_clr; lia | lia ] | close_xbb ] ] ] end end.
    all: try hd_eqs.
    all: try (lazymatch goal with |- Z_to_bv 64 _ = _ => hd_regeq end).
    all: try (lazymatch goal with |- Z_to_bv 64 _ = _ => rewrite hd_swr by (first [reflexivity | hd_clr; lia]); f_equal; lia end).
    all: try (lazymatch goal with |- rw_cells _ _ _ _ => hd_frq FR end).
  Time Qed.


  Lemma x2v_sh0n : forall m lo0 hi a, unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m lo0 hi a U L H. assert (0 <= lo0) by (destruct U; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (a / 8 + ASHOFF) with (ASHOFF + a / 8) by lia.
    eapply unpoisoned_full_rd; [exact U| rewrite shad_div; pose proof (Z.div_le_mono lo0 a 8 ltac:(lia) L); lia| lia].
  Qed.

  Lemma x2v_acc_rng : forall lo0 len a n, rng RNG lo0 len -> lo0 <= a < lo0 + len -> a + Z.of_nat n <= lo0 + len -> acc_in RNG (Z_to_bv 64 a, n).
  Proof. intros lo0 len a n [R0 [R1 R2]] H1 H2. unfold acc_in; cbn [fst snd]. rewrite unsigned_lit by lia. apply R2; lia. Qed.

  Ltac x2v_side := rewrite ?shad_div, ?nshad_div; unfold ASHOFF; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
    rewrite ?Z.mod_small by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; Z.div_mod_to_equations; lia.
  Definition HdI2 (i j : Z) : Prop := True.
  Ltac hd_shload := lazymatch goal with |- context [ov_read_bytes bsegs ?m ?ad 1%nat] =>
    lazymatch ad with context [Z.shiftr ?a 3] =>
    lazymatch goal with MU : munch _ m5 m |- _ =>
      let U := fresh "U" in pose proof (x2_unp_wkM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UW m MU) as U;
      let HS := fresh "HS" in
      assert (HS : ov_read_bytes bsegs m ad 1 = Some [Z_to_bv 8 0])
        by (rewrite <- (x2v_sh0n m WK (WK + wksz) a U) by x2v_side; f_equal;
            first [ reflexivity | unfold wa; f_equal; unfold ASHOFF; lia
                  | unfold wa; apply Z_to_bv_eqm; unfold ASHOFF; rewrite ?Zmod_mod; reflexivity ]);
      rewrite HS; clear HS U end end end; load_post.
  Ltac hd_u32at m ad i U :=
    let HR := fresh "HR" in
    assert (HR : ov_read_bytes bsegs m ad 4 = Some (le4 (Z_to_bv 64 (Znth i rs0))))
      by (apply (u32arr_read bsegs m (WK + 676) _ i _ ad U); [apply nth_error_map_Znth; lia | lia |
            unfold wa; first [ reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia
                             | apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.mod_small by lia; lia ]]);
    rewrite HR; clear HR.
  Ltac hd_u32load := lazymatch goal with |- context [ov_read_bytes bsegs ?m ?ad 4%nat] =>
    lazymatch goal with HU : HdHide (u32arr bsegs ?m0 (WK + 676) (map (Z_to_bv 64) rs0)), HIX : HdI2 ?i ?j |- _ =>
    lazymatch goal with MV : munch ?W m0 m, WV : wmono bsegs m0 m |- _ =>
      let U := fresh "U" in
      assert (U : u32arr bsegs m (WK + 676) (map (Z_to_bv 64) rs0))
        by (apply (u32arr_transport bsegs W m0 m _ _ HU MV WV); cbn [disjoint_from]; rewrite length_map; split; [lia | exact Logic.I]);
      first [ hd_u32at m ad i U | hd_u32at m ad j U ]; clear U end end end; load_post.
  Ltac hd_acchint := lazymatch goal with
    | |- acc_in _ (?ad, 1%nat) => lazymatch ad with context [Z.shiftr _ 3] =>
        lazymatch goal with H : rng _ (shad WK) _ |- _ => eapply (x2v_acc_rng _ _ _ _ H); x2v_side end end
    | |- acc_in _ (_, 4%nat) => lazymatch goal with H : rng _ WK wksz |- _ => eapply (x2v_acc_rng _ _ _ _ H); x2v_side end
    end.
  Local Ltac solve_load ::= first [ hd_shload | hd_u32load | solve_load_base | solve_load_image ].
  Local Ltac acc_hint ::= hd_acchint.
  Ltac hd_prune2 K :=
    try (exfalso; lia);
    try (exfalso; rewrite ?Z.shiftl_mul_pow2 in K by lia; rewrite ?Z.mod_small in K by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); lia);
    try (exfalso; rewrite ?FseWalkKit.swrap32_small in K by lia; rewrite ?unsigned_lit in K by lia; rewrite ?Z.mod_small in K by lia; lia).
  Ltac hd_prune3 K := hd_prune2 K;
    try (exfalso; lazymatch type of K with context [bv_unsigned (sxb (Z_to_bv 8 ?c))] =>
                      rewrite (sxb_lit c) in K by lia; cbn in K; lia end).
  Ltac hd_go2 stops :=
    hd_walk stops;
    try (hd_ifpc; let K := fresh "K" in bcase K; hd_prune3 K; hd_go2 stops).
  Ltac hd_rawlia r :=
    let RB := fresh "RB" in assert (RB : -20 <= r <= 30) by lia;
    repeat match goal with H : ?t |- _ => lazymatch t with context [r] => fail | _ => clear H end end;
    Z.div_mod_to_equations; lia.
  Ltac hd_maxfix := repeat match goal with |- context [Z.max 1 ?r] =>
    first [ rewrite (Z.max_r 1 r) by hd_rawlia r | rewrite (Z.max_l 1 r) by hd_rawlia r ] end.
  Ltac hd_close K mm := lazymatch goal with |- evtF _ _ _ ?s =>
    let EQS := fresh "EQS" in eassert (EQS : _ = s); [| rewrite <- EQS; eapply (K mm); [ first [ hd_clr; lia | lia ] | close_xbb ] ] end.
  Definition HdI1 (i : Z) : Prop := True.
  Ltac hd_rvload := lazymatch goal with |- context [ov_read_bytes bsegs ?m ?ad 4%nat] =>
    lazymatch goal with HU : HdHide (u32arr bsegs m WK (map (Z_to_bv 64) ?l)), HIX : HdI1 ?i |- _ =>
      let HR := fresh "HR" in
      assert (HR : ov_read_bytes bsegs m ad 4 = Some (le4 (Z_to_bv 64 (Znth i l))))
        by (apply (u32arr_read bsegs m WK _ i _ ad HU); [apply nth_error_map_Znth; lia | lia |
              unfold wa; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; rewrite ?Z.mod_small by lia; lia ]]);
      rewrite HR; clear HR end end; load_post.
  Local Ltac solve_load ::= first [ hd_shload | hd_u32load | hd_rvload | solve_load_base | solve_load_image ].
  Ltac hd_lx := repeat match goal with |- context [Z.lxor ?x 9223372036854775808] =>
    let H := fresh "LX" in
    assert (H : Z.lxor x 9223372036854775808 = x + 9223372036854775808)
      by (change 9223372036854775808 with (2 ^ 63); apply zb_lxor_pow2_small; lia);
    rewrite H; clear H end.
  Ltac hd_bw := repeat match goal with |- context [bv_wrap ?n ?x] =>
    replace (bv_wrap n x) with x by (unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus;
                                     change (2 ^ Z.of_N n) with 18446744073709551616; lia) end.
  Ltac hd_ltb := hd_bw; hd_lx; repeat match goal with |- context [Z.ltb ?a ?b] =>
    first [ replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; hd_clr; lia)
          | replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; hd_clr; lia) ] end; cbn [Z.b2z].
  Ltac hd_walk3 stops := repeat (tryif hd_at_stop stops then fail else (zstep; try hd_ltb)).
  Ltac hd_prune4 K :=
    try (match goal with E : Znth _ _ = RV0 _ |- _ => rewrite E in K end);
    try (rewrite hd_zx32 in K by lia); hd_prune3 K.
  Ltac hd_go3 stops :=
    hd_walk3 stops;
    try (hd_ifpc; let K := fresh "K" in bcase K; hd_prune4 K; hd_go3 stops).

  Ltac hd_un D := let t := type of D in lazymatch t with HdHide ?P => let D' := fresh "D" in pose proof (D : P) as D'; destruct D'; lia end.
  Ltac hd_dj := cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; repeat split; try exact I;
    first [ lia | match goal with D : HdHide (_ \/ _) |- _ => hd_un D end ].
  Ltac hd_tr m m' MU WM :=
    let W := lazymatch type of MU with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at bsegs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_transport bsegs W m m' A2 bs2) in H; [ | exact MU | hd_dj ] | clear H ]
    | H : wr_at bsegs m ?A2 ?n2 |- _ => apply (wr_at_transport bsegs m m' A2 n2) in H; [ | exact WM ]
    | H : rw_cells bsegs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_transport bsegs W m m' A2 cs2) in H; [ | exact MU | exact WM | hd_dj ] | clear H ]
    | H : u8arr bsegs m ?A2 ?xs |- _ =>
        first [ apply (u8arr_transport bsegs W m m' A2 xs) in H; [ | exact MU | exact WM | hd_dj ] | clear H ]
    | H : u32arr bsegs m ?A2 ?xs |- _ =>
        first [ apply (u32arr_transport bsegs W m m' A2 xs) in H; [ | exact MU | exact WM | hd_dj ] | clear H ]
    | H : stk bsegs m ?loq ?hiq |- _ =>
        first [ apply (stk_transport_disjoint bsegs W m m' loq hiq) in H; [ | exact MU | exact WM | hd_dj ] | clear H ]
    | H : munch ?Wq ?mq m |- _ =>
        apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; lia | exact MU ] ]
    | H : wmono bsegs ?mq m |- _ => apply (wmono_trans bsegs mq m m') in H; [ | exact WM ]
    end.

  Lemma x2_l1B : forall m1 (dt : list Z) (w : Z) v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376
      xra x5 x6 x7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> TT - (tl + 1 - w) < tl - maxW + 1 -> x2pref TT (RV0 w) dt ->
    (forall m2 (dt' : list Z) y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31, x2pref TT (RV0 (w + 1)) dt' ->
       STLT m2 w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt'
            (Z_to_bv 64 0x82560) y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs6 xs8 xs9 xs10 xs11 y28 y29 y30 y31) ->
    STLE 0x82628 m1 w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt xra x5 x6 x7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HE PRE K I. open_xbb I. x2_open. hd_hide_disj.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l1_facts w (TT - (tl + 1 - w)) HW eq_refl ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    pose proof (rv0_bounds w ltac:(lia)) as (RB0 & _).
    pose proof RVXX as (RV0X & _). pose proof (RV0X w HW) as RVW. clear RV0X.
    assert (RVN : RV0 w + 2 ^ (TT - (tl + 1 - w)) * (XS1 (w + 1) - XS1 w) = RV0 (w + 1)) by (rewrite F6, F3; ring).
    assert (HIX1 : HdI1 w) by exact Logic.I.
    hd_hide DTC. hd_hide HWC. hd_hide RK. hd_hide RS0. hd_hide SYC. hd_hide RV. hd_hide NBC.
    hd_go3 [46100; 3652; 3916].
    unfold HdHide in DTC, HWC, RK, RS0, SYC, RV, NBC.
    try kx_mkR_foldF.
    assert (P2 : 2 ^ mtl <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
    rewrite RVW. rewrite (hd_zx32 (RV0 w)) by lia. rewrite (Z.shiftl_mul_pow2 (RV0 w) 2) by lia. change (2 ^ 2) with 4.
    replace (Z_to_bv 64 (DT + 4 + RV0 w * 4)) with (Z_to_bv 64 (DT + 4 + 4 * RV0 w)) by (f_equal; ring).
    replace (Z_to_bv 64 (XS1 (w + 1) + (WK + 736))) with (Z_to_bv 64 (WK + 736 + XS1 w + (XS1 (w + 1) - XS1 w))) by (f_equal; ring).
    pose proof (x2_helper_hyps RNG SPV SPA lo DT WK wksz FF mtl HY) as HH.
    destruct (stk_split bsegs m1 lo (SPA - 112) SPA STK ltac:(lia)) as [STKL STKF].
    assert (USY : unpoisoned m1 (WK + 736) (WK + 736 + 256)) by (eapply unpoisoned_sub; [exact UW1 | lia | lia]).
    pose proof X2HB as XH. unfold x2hb_stmt in XH.
    eapply evtF_cut;
    [ eapply (XH RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 SPA DT (WK + 736) (RV0 w) (XS1 (w + 1) - XS1 w) (XS1 w) (tl + 1 - w) TT 0 1 mtl dt syb);
        first [ exact HH | exact MI | exact DTC | exact DTLEN | exact DTBY | exact (proj1 SYC) | exact SYLEN | exact STKF | exact ART1
              | exact UDT1 | exact USY | exact TP | exact PRE | left; reflexivity | rewrite RVN; lia | (hd_clr; lia) ] | ].
    intros ms' PO. unfold x2hb_post in PO.
    destruct PO as (y5 & y6 & y7 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2 & dt' & -> & MU2 & WM2 & MI2 & DTC2 & DTLEN2 & DTBY2 & PRE2 & STKF2).
    replace (ret_pc (Z_to_bv 64 0x82560)) with (Z_to_bv 64 0x82560) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear DTC STKF STK MI UDT1 UW1 ART1 USY HH XH.
    hd_tr m1 m2 MU2 WM2.
    pose proof (stk_merge bsegs m2 lo (SPA - 112) SPA STKL STKF2 ltac:(lia)) as STK2.
    rewrite RVN in PRE2.
    eapply K; [ exact PRE2 | close_xbb ].
  Time Qed.

  End FX.
  End FM.
End X2B.
End CANSEC1.
