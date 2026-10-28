(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2 ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_defs AZ_hft_x2_geo AZ_hft_x2_kit AZ_hft_x2h_defs AZ_hft_x2_defs AZ_hft_x2_facts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.
Section X2B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF hdw r : Z).
  Hypothesis HY : x2A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Hypothesis HM : hdw mod 256 = 12.
  Hypothesis HR : 0 <= hdw < 2^32.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide5 DT WK SPA lo FF; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase5 DT WK SPA lo FF lo1 in
                lazymatch goal with
                | U : unpoisoned mm X ?hi0 |- _ => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | match goal with
                | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | kxa_unp_hook ]
    end.
  Local Ltac kxl_rng ::=
    first [ kxl_hyp
          | lazymatch goal with
            | |- rng ?RG ?A ?N =>
                let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with H : rng RG X ?N0 |- _ => apply (rng_sub' RG X N0 A N H); solve [kx_lia] end
            end
          | lazymatch goal with
            | |- rng ?RG ?A ?N => match goal with H : rng RG ?A0 ?N0 |- _ => apply (rng_sub' RG A0 N0 A N H); solve [kxl_lia_small] end
            end
          | kx_rng ].
  Local Ltac kxa_rng0 ::=
    kxa_norm;
    lazymatch goal with
    | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
        first [ let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with
                | H : rng RG (shad X) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | match goal with
                | H : rng RG (shad ?A0) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad A0) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                | H : rng RG ?A0 ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n A0 N0 H);
                    [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | lazymatch RG with
                | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
                end
              | kxa_rng_hook ]
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac x2_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x2_unp_dtM _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x2_unp_wkM _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x2_artM _ _ _ _ _ _ _ _ _ HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x2_open :=
    open_hx2 HY; unfold KHIGH in *;
    pose proof (x2_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    assert (RSTA : rng RNG SPA 728) by (lazymatch goal with H : rng RNG lo (SPV - lo) |- _ => eapply rng_sub'; [exact H| lia] end);
    lazymatch goal with H1 : DT + 16388 <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 848 <= SPA <= SPV - 832 |- _ =>
      assert (SDSA : DT + 16388 <= SPA - 5072 \/ SPA + 728 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA - 5072 \/ SPA + 728 <= WK) by (clear - H2 H3 H4; lia) end;
    hide_all_disj; x2_reunp.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5072) (2^47 - 848); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x625000 (2^47 - 16388); KZRange WK 0x625000 (2^47 - 2124); KZRange wksz 2124 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZRange hdw 0 (2^32); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT 16388 SPA 728; KZDisj WK wksz SPA 728; KZDisj DT 16388 WK wksz;
     KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 728 FF 64] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7
             (Z_to_bv 64 0x7fff8000) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  (* [comment removed for export] *)
  Notation TT := (AZ_hft_x2_defs.TT tl).
  Lemma TT_range : 1 <= tl <= 12 -> tl <= TT <= 12 /\ 11 <= TT.
  Proof. intros H. unfold AZ_hft_x2_defs.TT. destruct (Z.ltb_spec tl 12); lia. Qed.

  (* [comment removed for export] *)
  Local Ltac x2_lens :=
    first [ assert (zlen (map (Z_to_bv 8) hw) = 256) by assumption | assert (zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW) ];
    first [ assert (zlen (map (Z_to_bv 8) (u32b rank)) = 52) by assumption
          | assert (zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity) ];
    try lazymatch goal with
    | RS0 : u8arr _ _ (WK + 676) (map _ (u32b ?rs)) |- _ =>
        first [ assert (zlen (map (Z_to_bv 8) (u32b rs)) = 60) by assumption
              | assert (zlen (map (Z_to_bv 8) (u32b rs)) = 60) by (rewrite length_map, u32b_length2, ?Zupd_length2; lia) ]
    end;
    try lazymatch goal with
    | RV : u8arr _ _ WK (map _ (u32b ?rs)) |- _ =>
        first [ assert (zlen (map (Z_to_bv 8) (u32b rs)) = 624) by assumption
              | assert (zlen (map (Z_to_bv 8) (u32b rs)) = 624) by (rewrite length_map, u32b_length2, ?Zupd_length2; lia) ]
    end;
    try lazymatch goal with
    | SYC : u8arr _ _ (WK + 736) ?sy |- _ => first [ assert (zlen sy = 256) by assumption | idtac ]
    end;
    try lazymatch goal with
    | DTC : u8arr _ _ DT (map _ ?d) |- _ =>
        first [ assert (zlen (map (Z_to_bv 8) d) = 16388) by assumption
              | assert (zlen (map (Z_to_bv 8) d) = 16388) by (rewrite length_map, ?Zupd_length2; lia) ]
    end.

  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.


  (* [comment removed for export] *)
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  (* [comment removed for export] *)
  Lemma rdn_sh0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
    rdn bsegs m (wa (shad p)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof. intros m X n p U Hp Hg. cbn [rdn]. rewrite (unp_shadow_zero m X n p U Hp Hg). reflexivity. Qed.
  Notation XS1 w := (xs1 rank w).
  Lemma xs1_bounds : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof.
    intros w Hw. pose proof STATS as (_ & (_ & LENW) & _). unfold FseNCount.Zlength in LENW.
    pose proof (xs1_nonneg (firstn (Z.to_nat nbs) hw) rank tl STATS w Hw) as A.
    pose proof (xs1_mono (firstn (Z.to_nat nbs) hw) rank tl STATS w 13 ltac:(lia) ltac:(lia)) as B.
    pose proof (xs1_top (firstn (Z.to_nat nbs) hw) rank tl STATS) as C.
    pose proof (rank_small 0 ltac:(lia)). unfold FseNCount.Zlength in C. rewrite length_firstn in C. lia.
  Qed.
  (* [comment removed for export] *)
  Variables (k0 k8 k16 k24 k32 k40 k48 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 : word).
  (* [comment removed for export] *)
  Variables (xnv xflv : word).
  (* [comment removed for export] *)
  Local Ltac runA AKS STOPS FUEL KZS RRS WWS :=
    let ks := eval cbv beta iota delta [app] in (KZS : list kz) in
    let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in
    let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
    kx_autoFA_core 0 stops (FUEL : nat) true aks ks rrs wws.
  (* [comment removed for export] *)
  Local Ltac runL CH AKS STOPS FUEL KZS RRS WWS :=
    let ks := eval cbv beta iota delta [app] in (KZS : list kz) in
    let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in
    let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
    kx_autoFLA_core 0 stops (FUEL : nat) true CH aks ks rrs wws.
  (* [comment removed for export] *)
  Section FM.
  (* [comment removed for export] *)
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Notation RV0 w := (rv0 rank tl TT w).
  Notation RVC c w := (rvc rank tl TT c w).
  Notation RINV := (AZ_hft_x2_facts.RINV rank).
  Notation SINV := (AZ_hft_x2_facts.SINV hw rank nbs maxW).
  Notation RSF := (AZ_hft_x2_facts.RSF rank maxW).
  Notation VINV := (AZ_hft_x2_facts.VINV rank tl).
  Notation ROWS := (AZ_hft_x2_facts.ROWS rank tl maxW).
  Notation RVX := (AZ_hft_x2_facts.RVX rank tl maxW).
  (* [comment removed for export] *)
  Lemma sinv0 : forall rs0, RINV (maxW + 1) rs0 -> Znth 1 rs0 = XS1 (maxW + 1) -> SINV 0 rs0.
  Proof. intros. eapply AZ_hft_x2_facts.sinv0; eauto. Qed.
  Lemma sort_unit : forall j rs0, 0 <= j < nbs -> SINV j rs0 -> zlen rs0 = 15 ->
    0 <= Znth j hw <= maxW /\ 0 <= Znth (Znth j hw + 1) rs0 /\ Znth (Znth j hw + 1) rs0 + 1 <= nbs
    /\ SINV (j + 1) (Zupd (Znth j hw + 1) (Znth (Znth j hw + 1) rs0 + 1) rs0).
  Proof. intros. eapply AZ_hft_x2_facts.sort_unit; eauto. Qed.
  Lemma rsf_of_sinv : forall rs0, SINV nbs rs0 -> zlen rs0 = 15 -> RSF (Zupd 1 0 rs0).
  Proof. intros. eapply AZ_hft_x2_facts.rsf_of_sinv; eauto. Qed.
  Lemma rv0_bounds : forall w, 1 <= w <= maxW + 1 -> 0 <= RV0 w <= 4096 /\ RV0 (maxW + 1) = 2^TT.
  Proof. intros. eapply AZ_hft_x2_facts.rv0_bounds; eauto. Qed.
  Lemma rows0 : forall c rv, c <= tl + 1 - maxW -> VINV (maxW + 1) rv -> ROWS c 1 rv.
  Proof. intros. eapply AZ_hft_x2_facts.rows0; eauto. Qed.
  Lemma rows_next : forall c rv, ROWS c (maxW + 1) rv -> ROWS (c + 1) 1 rv.
  Proof. intros. eapply AZ_hft_x2_facts.rows_next; eauto. Qed.
  Lemma rvc_val : forall c w, 0 <= c -> 1 <= w <= maxW + 1 -> 0 <= RVC c w <= RV0 w /\ RVC c w = RV0 w / 2^c.
  Proof. intros. eapply AZ_hft_x2_facts.rvc_val; eauto. Qed.
  Lemma rvx_of_rows : forall rv, ROWS (TT - (tl + 1 - maxW) + 1) 1 rv -> RVX rv.
  Proof. intros. eapply AZ_hft_x2_facts.rvx_of_rows; eauto. Qed.
  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 4096 /\ 1 <= 2 ^ e <= 4096.
  Proof. intros. eapply AZ_hft_x2_facts.l1_facts; eauto. Qed.

  Notation XBP v16 v48 v592 dt rs0 syb rv mm :=
    (XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 v16 (Z_to_bv 64 r) k32 k40 v48 (Z_to_bv 64 hdw) k72 (Z_to_bv 64 (tl + 1)) k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 (Z_to_bv 64 (DT + 4)) k264 k272 k280
        k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 v592
        (Z_to_bv 64 TT) (Z_to_bv 64 (WK + 736)) k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv mm) (only parsing).
  Notation HD24 := (hdw mod 2 ^ 64 / 16777216) (only parsing).
  Notation XBQ dt rs0 syb rv mm := (XBP k16 k48 k592 dt rs0 syb rv mm) (only parsing).
  Notation XBV dt rs0 syb rv mm := (XBP (Z_to_bv 64 HD24) (Z_to_bv 64 maxW) (Z_to_bv 64 (maxW + 1)) dt rs0 syb rv mm)
    (only parsing).
  Notation STS pc mm n xra x6 xa2 xa3 xs2 xs10 :=
    (ST pc mm xra (Z_to_bv 64 n) x6 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 HD24) (Z_to_bv 64 (WK + 680)) xa2 xa3
        (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (4294967296 * (maxW + 1))) (Z_to_bv 64 (0x7fff8000 + (WK + 680) / 8)) (Z_to_bv 64 nbs)
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624))
        (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).
  Notation STVE mm xra x5 x6 xa2 xa5 xa7 xs2 xs10 :=
    (ST 0x97848 mm xra x5 x6 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (TT - tl + maxW)) (Z_to_bv 64 (WK + 624 + 4 * (maxW + 1))) xa2 (Z_to_bv 64 (WK + 624 + 4 * (maxW + 1)))
        (Z_to_bv 64 0) xa5 (Z_to_bv 64 (2 ^ TT)) xa7
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624))
        (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).
  (* [comment removed for export] *)
  Notation XBW dt rs0 syb rv mm := (XBV dt rs0 syb rv mm) (only parsing).
  (* [comment removed for export] *)
  Notation STX pc mm c w xra x6 x7 xa2 xs2 xs10 x28 :=
    (ST pc mm xra (Z_to_bv 64 (WK + 4 * w)) x6 x7 (Z_to_bv 64 (TT - tl + maxW)) (Z_to_bv 64 (WK + 4 * w)) xa2 (Z_to_bv 64 (WK + 4))
        (Z_to_bv 64 (52 * c)) (Z_to_bv 64 maxW) (Z_to_bv 64 c) (Z_to_bv 64 (maxW + 1 - w))
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624))
        x28 (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).
  (* [comment removed for export] *)
  Notation STQ mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 :=
    (ST 0x97904 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11
        x28 (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).

  (* [comment removed for export] *)
  Lemma x2_x_bodyA : forall m1 (dt rs0 rv : list Z) (syb : list byte) (c w : Z) xra x6 x7 xa2 xs2 xs10 x28,
    XBW dt rs0 syb rv m1 -> tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= w <= maxW -> ROWS c w rv ->
    (forall m2 (rv' : list Z) (y6 y7 ya2 y28 : word), w + 1 <= maxW ->
       XBW dt rs0 syb rv' m2 -> ROWS c (w + 1) rv' ->
       evtF bsegs RNG POST (STX 0x97898 m2 c (w + 1) xra y6 y7 ya2 xs2 xs10 y28)) ->
    (forall m2 (rv' : list Z) (y6 y7 ya2 y28 : word), w = maxW ->
       XBW dt rs0 syb rv' m2 -> ROWS c (maxW + 1) rv' ->
       evtF bsegs RNG POST (STX 0x9787c m2 c (maxW + 1) xra y6 y7 ya2 xs2 xs10 y28)) ->
    evtF bsegs RNG POST (STX 0x97898 m1 c w xra x6 x7 xa2 xs2 xs10 x28).
  Proof.
    intros until x28; intros I HCR HW RWI KH KE. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    pose proof (rv0_bounds w ltac:(lia)) as (RB0 & TOP). pose proof (rvc_val c w ltac:(lia) ltac:(lia)) as (RCB & RCE).
    pose proof RWI as (R0 & RC & RWW). pose proof (R0 w HW) as R0W.
    (* [comment removed for export] *)
    runL FR [KAUnp WK 2124; KAApp WK 2124] [0x978c0] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange c 1 11; KZRange (RV0 w) 0 4096;
               KZWord (WK + 4 * w) 4%nat (RV0 w)])
      [(SPA, 728)] [(WK, 2124); (SPA, 728)].
    all: try (split; [lia| split; [lia| split; [lia| rewrite <- R0W; apply (rdn_u32b bsegs m1 WK rv w RV); [lia| rewrite R0W; lia]]]]).
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    zstep.
    assert (ESR : bv_swrap 32 (Z.shiftr (bv_wrap 32 (RV0 w)) (c mod 32)) = RVC c w).
    { rewrite wrap32_small by lia. rewrite (Z.mod_small c 32) by lia. rewrite RCE. rewrite Z.shiftr_div_pow2 by lia. apply swrap32_small. lia. }
    rewrite ESR.
    (* [comment removed for export] *)
    runL FR [KAUnp WK 2124; KAApp WK 2124] [0x97898; 0x9787c] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange c 1 11; KZRange (RV0 w) 0 4096; KZRange (RVC c w) 0 4096;
               KZWr WK 624])
      [(SPA, 728)] [(WK, 2124); (SPA, 728)].
    all: kxk_keepg RV. all: kx_mem. all: kx_tidy_run.
    all: clear KXUL; replace (WK + (4 * w + 52 * c) + 0 - WK) with (4 * (13 * c + w)) in RV by lia.
    all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
    all: rewrite (u32b_upd4 rv (13 * c + w) (RVC c w)) in RV by lia.
    all: assert (RVLEN' : zlen (Zupd (13 * c + w) (RVC c w) rv) = 156) by (rewrite Zupd_length2; exact RVLEN);
         assert (RVNN' : Forall (fun v : Z => 0 <= v) (Zupd (13 * c + w) (RVC c w) rv)) by (apply Forall_Zupd; [exact RVNN| lia]).
    all: assert (RWI' : ROWS c (w + 1) (Zupd (13 * c + w) (RVC c w) rv))
      by (split; [intros v Hv; rewrite Znth_Zupd_other by lia; apply R0; exact Hv|];
          split; [intros c' v Hc Hv; rewrite Znth_Zupd_other by lia; apply RC; assumption|];
          intros v Hv; destruct (Z.eq_dec v w) as [->|NE]; [apply Znth_Zupd_same; unfold FseNCount.Zlength; lia|];
          rewrite Znth_Zupd_other by lia; apply RWW; lia).
    - kx_setreg 5 (WK + 4 * (w + 1)). kx_setreg 11 (WK + 4 * (w + 1)). kx_setreg 17 (maxW + 1 - (w + 1)).
      eapply KH; [lia| close_xb| exact RWI'].
    - assert (EW : w = maxW) by lia. subst w.
      kx_setreg 5 (WK + 4 * (maxW + 1)). kx_setreg 11 (WK + 4 * (maxW + 1)). kx_setreg 17 (maxW + 1 - (maxW + 1)).
      eapply KE; [reflexivity| close_xb| exact RWI'].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_x_loopA : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (c w : Z) xra x6 x7 xa2 xs2 xs10 x28,
    XBW dt rs0 syb rv m1 -> tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= w <= maxW -> maxW + 1 - w <= Z.of_nat f -> ROWS c w rv ->
    (forall m2 (rv' : list Z) (y6 y7 ya2 y28 : word),
       XBW dt rs0 syb rv' m2 -> ROWS c (maxW + 1) rv' ->
       evtF bsegs RNG POST (STX 0x9787c m2 c (maxW + 1) xra y6 y7 ya2 xs2 xs10 y28)) ->
    evtF bsegs RNG POST (STX 0x97898 m1 c w xra x6 x7 xa2 xs2 xs10 x28).
  Proof.
    induction f as [|f IH]; intros until x28; intros I HCR HW HF RWI KE; [lia|].
    eapply x2_x_bodyA; [exact I| exact HCR| exact HW| exact RWI| |].
    - intros * HW1 I2 RW2. eapply IH with (w := w + 1); [exact I2| exact HCR| lia| lia| exact RW2| exact KE].
    - intros * EW I2 RW2. eapply KE; [exact I2| exact RW2].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w_latchA : forall m1 (dt rs0 rv : list Z) (syb : list byte) (c : Z) xra x6 x7 xa2 xs2 xs10 x28,
    XBW dt rs0 syb rv m1 -> tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> ROWS c (maxW + 1) rv ->
    (forall m2 (y6 y7 ya2 y28 : word), c + 1 <= TT - (tl + 1 - maxW) ->
       XBW dt rs0 syb rv m2 -> ROWS (c + 1) 1 rv ->
       evtF bsegs RNG POST (STX 0x97898 m2 (c + 1) 1 xra y6 y7 ya2 xs2 xs10 y28)) ->
    (forall m2 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28, c = TT - (tl + 1 - maxW) ->
       XBW dt rs0 syb rv m2 -> ROWS (TT - (tl + 1 - maxW) + 1) 1 rv ->
       evtF bsegs RNG POST (STQ m2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28)) ->
    evtF bsegs RNG POST (STX 0x9787c m1 c (maxW + 1) xra x6 x7 xa2 xs2 xs10 x28).
  Proof.
    intros until x28; intros I HCR RWI KH KE. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    pose proof (rows_next c rv RWI) as RWN.
    runL FR (@nil kza) [0x97898; 0x97904] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange maxW 1 12; KZRange TT 11 12; KZRange c 1 11])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97898) _ _ _ _) =>
            replace (WK + 4 * 1) with (WK + 4) in KH by lia; replace (maxW + 1 - 1) with maxW in KH by lia; kx_setreg 14 (52 * (c + 1));
            eapply KH; [lia| close_xb| exact RWN]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97904) _ _ _ _) => assert (EC : c = TT - (tl + 1 - maxW)) by lia; rewrite EC in RWN; eapply KE; [exact EC| close_xb| exact RWN]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w_loopA : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (c : Z) xra x6 x7 xa2 xs2 xs10 x28,
    XBW dt rs0 syb rv m1 -> tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> TT - (tl + 1 - maxW) + 1 - c <= Z.of_nat f -> ROWS c 1 rv ->
    (forall m2 (rv' : list Z) y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28,
       XBW dt rs0 syb rv' m2 -> ROWS (TT - (tl + 1 - maxW) + 1) 1 rv' ->
       evtF bsegs RNG POST (STQ m2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28)) ->
    evtF bsegs RNG POST (STX 0x97898 m1 c 1 xra x6 x7 xa2 xs2 xs10 x28).
  Proof.
    induction f as [|f IH]; intros until x28; intros I HCR HF RWI KE; [lia|].
    eapply (x2_x_loopA (Z.to_nat maxW)) with (w := 1); [exact I| exact HCR| lia| lia| exact RWI|].
    intros * I2 RW2.
    eapply x2_w_latchA; [exact I2| exact HCR| exact RW2| |].
    - intros * HC1 I3 RW3. eapply IH; [exact I3| lia| lia| exact RW3| exact KE].
    - intros * EC I3 RW3. eapply KE; [exact I3| exact RW3].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w_entA : forall m1 (dt rs0 rv : list Z) (syb : list byte) xra x5 x6 xa2 xa5 xa7 xs2 xs10,
    XBV dt rs0 syb rv m1 -> VINV (maxW + 1) rv ->
    (forall m2 (y6 y7 ya2 y28 : word), tl + 1 - maxW <= TT - (tl + 1 - maxW) ->
       XBW dt rs0 syb rv m2 -> ROWS (tl - maxW + 1) 1 rv ->
       evtF bsegs RNG POST (STX 0x97898 m2 (tl - maxW + 1) 1 xra y6 y7 ya2 xs2 xs10 y28)) ->
    (forall m2 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28, TT - (tl + 1 - maxW) < tl + 1 - maxW ->
       XBW dt rs0 syb rv m2 -> ROWS (TT - (tl + 1 - maxW) + 1) 1 rv ->
       evtF bsegs RNG POST (STQ m2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 y28)) ->
    evtF bsegs RNG POST (STVE m1 xra x5 x6 xa2 xa5 xa7 xs2 xs10).
  Proof.
    intros until xs10; intros I VI KR KN. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR. pose proof (rows0 (tl - maxW + 1) rv ltac:(lia) VI) as RW0.
    assert (P2T : 2 ^ TT <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (P2T0 : 0 < 2 ^ TT) by (apply Z.pow_pos_nonneg; lia).
    set (mb := tl - maxW + 1). assert (MBR : 1 <= mb <= 12) by lia.
    runL FR (@nil kza) [0x97898; 0x97904] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange maxW 1 12; KZRange TT 11 12; KZRange (2 ^ TT) 1 4096; KZRange mb 1 12; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem.
    all: repeat match goal with
         | KXA : atoms_ok ?zs ?E |- context [edenot ?E (EMd M_MULHU ?a ?b)] =>
             let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
             let HD := fresh "HD" in
             assert (HD : bv_unsigned (edenot E (EMd M_MULHU a b)) = ua * ub / 2 ^ 64)
               by (change (edenot E (EMd M_MULHU a b)) with (mul_div M_MULHU (edenot E a) (edenot E b)); rewrite KXS.u_mulhu64;
                   rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity);
            rewrite HD in *; clear HD
         end.
    all: kx_tidy_run.
    all: subst mb.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97898) _ _ _ _) =>
            replace (WK + 4 * 1) with (WK + 4) in KR by lia; replace (maxW + 1 - 1) with maxW in KR by lia; kx_setreg 10 (TT - tl + maxW);
            setreg_m 14 (52 * (tl - maxW + 1));
            eapply KR; [lia| close_xb| exact RW0]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97904) _ _ _ _) => eapply KN; [lia| close_xb| apply rows0; [lia| exact VI]]
         end.
  Qed.

  End FM.
End X2B.
End CANSEC1.
