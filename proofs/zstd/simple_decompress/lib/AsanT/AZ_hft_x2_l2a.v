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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_defs AZ_hft_x2_geo AZ_hft_x2_kit AZ_hft_x2h_defs AZ_hft_x2_defs AZ_hft_x2_facts AZ_hft_x2_facts2.
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
  Section FX.
  (* [comment removed for export] *)
  Variables (rs0 rv : list Z) (syb : list byte).
  Hypothesis RSFX : RSF rs0.
  Hypothesis RVXX : RVX rv.
  (* [comment removed for export] *)
  Notation XBF v88 v104 v152 v168 v176 v184 v264 v272 v280 v288 v544 v568 v576 J K dt mm :=
    (XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 (Z_to_bv 64 (hdw mod 2 ^ 64 / 16777216)) (Z_to_bv 64 r) (Z_to_bv 64 223338299392) (Z_to_bv 64 (tl + 1 - TT)) (Z_to_bv 64 maxW) (Z_to_bv 64 hdw)
        (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) v88 v104 (Z_to_bv 64 (DT + 8)) v152 (Z_to_bv 64 (DT + 7)) v168
        v176 v184 (Z_to_bv 64 (DT + 27)) (Z_to_bv 64 (DT + 20)) (Z_to_bv 64 (DT + 35)) (Z_to_bv 64 (DT + 28)) (Z_to_bv 64 (DT + 12)) (Z_to_bv 64 (DT + 19))
        (Z_to_bv 64 (DT + 11)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) v264 v272 v280 v288 (nth 0 J (Z_to_bv 64 0))
        (nth 1 J (Z_to_bv 64 0)) (nth 2 J (Z_to_bv 64 0)) (nth 3 J (Z_to_bv 64 0)) (nth 4 J (Z_to_bv 64 0)) (nth 5 J (Z_to_bv 64 0)) (nth 6 J (Z_to_bv 64 0)) (nth 7 J (Z_to_bv 64 0)) (nth 8 J (Z_to_bv 64 0))
        (nth 9 J (Z_to_bv 64 0)) (nth 10 J (Z_to_bv 64 0)) (nth 11 J (Z_to_bv 64 0)) (nth 12 J (Z_to_bv 64 0)) (nth 13 J (Z_to_bv 64 0)) (nth 14 J (Z_to_bv 64 0)) (nth 15 J (Z_to_bv 64 0)) (nth 16 J (Z_to_bv 64 0))
        (nth 17 J (Z_to_bv 64 0)) (nth 18 J (Z_to_bv 64 0)) (nth 19 J (Z_to_bv 64 0)) (nth 20 J (Z_to_bv 64 0)) (nth 21 J (Z_to_bv 64 0)) (nth 22 J (Z_to_bv 64 0)) (nth 23 J (Z_to_bv 64 0)) (nth 24 J (Z_to_bv 64 0))
        (nth 25 J (Z_to_bv 64 0)) (nth 26 J (Z_to_bv 64 0)) (nth 27 J (Z_to_bv 64 0)) (nth 28 J (Z_to_bv 64 0)) (nth 29 J (Z_to_bv 64 0)) (nth 30 J (Z_to_bv 64 0)) v544 (nth 31 J (Z_to_bv 64 0))
        (nth 32 J (Z_to_bv 64 0)) v568 v576 (Z_to_bv 64 (WK + 676)) (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 TT) (Z_to_bv 64 (WK + 736)) (nth 0 K (Z_to_bv 64 0))
        (nth 1 K (Z_to_bv 64 0)) (nth 2 K (Z_to_bv 64 0)) (nth 3 K (Z_to_bv 64 0)) (nth 4 K (Z_to_bv 64 0)) (nth 5 K (Z_to_bv 64 0)) (nth 6 K (Z_to_bv 64 0)) (nth 7 K (Z_to_bv 64 0)) (nth 8 K (Z_to_bv 64 0))
        (nth 9 K (Z_to_bv 64 0)) (nth 10 K (Z_to_bv 64 0)) k704 k712
        dt rs0 syb rv mm) (only parsing).
  (* [comment removed for export] *)
  Local Ltac fr_norm FR :=
    try replace (Z_to_bv 64 (-1 * TT + tl + 1)) with (Z_to_bv 64 (tl + 1 - TT)) in FR by (f_equal; lia).
  Notation STLE pc mm w v88 v152 v168 v176 v184 v264 v272 v280 v544 v568 v576 J K dt
           xra x5 x6 x7 xa1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x28 x29 x30 x31 :=
    (XBF v88 (Z_to_bv 64 (w + 1)) v152 v168 v176 v184 v264 v272 v280 (Z_to_bv 64 (XS1 (w + 1))) v544 v568 v576 J K dt mm ->
     evtF bsegs RNG POST
       (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (tl + 1 - w)) xa1 (Z_to_bv 64 (TT - (tl + 1 - w))) xa3 xa4 xa5 (Z_to_bv 64 (XS1 w)) xa7
           xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (RV0 w)) xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STLT mm w v88 v152 v168 v176 v184 v264 v272 v280 v544 v568 v576 J K dt
           xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF v88 (Z_to_bv 64 (w + 1)) v152 v168 v176 v184 v264 v272 v280 (Z_to_bv 64 (XS1 (w + 1))) v544 v568 v576 J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x97990 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  (* [comment removed for export] *)
  Notation XL w minW len v264 v272 v544 J K dt mm :=
    (XBF (Z_to_bv 64 (WK + 52 * (tl + 1 - w) + 4 * minW)) (Z_to_bv 64 (w + 1)) (Z_to_bv 64 minW) (Z_to_bv 64 (Z.shiftr (WK + 52 * (tl + 1 - w) + 4 * minW) 3))
         (Z_to_bv 64 (65536 * (tl + 1 - w) + 16777216)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) v264 v272 (Z_to_bv 64 len) (Z_to_bv 64 (XS1 (w + 1)))
         v544 (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (WK + 52 * (tl + 1 - w))) J K dt mm) (only parsing).
  (* [comment removed for export] *)
  Notation STSH mm w minW len st s v264 v272 v544 J K dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len v264 v272 v544 J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x98198 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 s) xa7
           xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 st) xs10 xs11 x28 x29 x30 x31)) (only parsing).

  (* [comment removed for export] *)
  Lemma l2_facts : forall w e minW, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> tl - maxW + 1 <= e -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 4096 /\ 2 <= 2 ^ e <= 4096 /\ 1 <= minW <= maxW /\ 1 <= e <= 11.
  Proof.
    intros w e minW HW HE HLE HMIN. pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l1_facts w e HW HE ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    assert (2 <= 2 ^ e) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (2 ^ e <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in *.
    repeat split; try lia.
  Qed.


  (* [comment removed for export] *)
  Lemma l2x_facts : forall w len minW, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    RV0 (w + 1) = RV0 w + (XS1 (w + 1) - XS1 w) * len /\ 2 <= len <= 2048 /\ 1 <= minW <= maxW /\ tl + 1 - w + (tl + 1 - TT) <= minW
    /\ RVC (tl + 1 - w) (maxW + 1) = len /\ 0 <= RVC (tl + 1 - w) minW <= len /\ RVC (tl + 1 - w) 1 = 0.
  Proof. intros. eapply AZ_hft_x2_facts2.l2x_facts; eauto. Qed.
  Lemma w2_facts : forall w len minW w2 len2, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> minW <= w2 <= maxW -> len2 = 2 ^ (TT - (tl + 1 - w) - (tl + 1 - w2)) ->
    0 <= XS1 w2 /\ XS1 (w2 + 1) <= 256 /\ XS1 (w2 + 1) = XS1 w2 + Znth w2 rank /\ 0 <= Znth w2 rank
    /\ 0 <= RVC (tl + 1 - w) w2 /\ RVC (tl + 1 - w) (w2 + 1) = RVC (tl + 1 - w) w2 + (XS1 (w2 + 1) - XS1 w2) * len2 /\ RVC (tl + 1 - w) (w2 + 1) <= len
    /\ 1 <= len2 <= len /\ 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= 11 /\ RVC (tl + 1 - w) w2 <= len.
  Proof. intros. eapply AZ_hft_x2_facts2.w2_facts; eauto. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation STSK mm w minW len st s sv J K dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 (DT + 4 + 4 * st)) J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x981dc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (4 * st)) xs3 xs4 xs5 xs6 xs7 xs9 (Z_to_bv 64 sv) xs11 x28 x29 x30 x31)) (only parsing).
  (* [comment removed for export] *)
  Notation STJ mm w minW len st s sv J K dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs9 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 (DT + 4 + 4 * st)) J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x98474 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (4 * st)) xs3 xs4 xs5 xs6 xs7 xs9 (Z_to_bv 64 sv) xs11 x28 x29 x30 x31)) (only parsing).
  (* [comment removed for export] *)
  Notation STW2 mm w minW len st s sv w2 K dt xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 (DT + 4 + 4 * st))
         [(Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 19 + 4 * st)); (Z_to_bv 64 (DT + 12 + 4 * st)); (Z_to_bv 64 (DT + 27 + 4 * st)); (Z_to_bv 64 (DT + 20 + 4 * st)); (Z_to_bv 64 (DT + 35 + 4 * st)); (Z_to_bv 64 (DT + 28 + 4 * st)); (Z_to_bv 64 (DT + 11 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 19 + 4 * st)); (Z_to_bv 64 (DT + 12 + 4 * st)); (Z_to_bv 64 (DT + 11 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 11 + 4 * st)); (Z_to_bv 64 (DT + 8 + 4 * st)); (Z_to_bv 64 (DT + 7 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 7 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 19 + 4 * st)); (Z_to_bv 64 (DT + 12 + 4 * st)); (Z_to_bv 64 (DT + 27 + 4 * st)); (Z_to_bv 64 (DT + 20 + 4 * st)); (Z_to_bv 64 (DT + 35 + 4 * st)); (Z_to_bv 64 (DT + 28 + 4 * st)); (Z_to_bv 64 (DT + 11 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (DT + 4 + 4 * st)); (Z_to_bv 64 (Z.lor sv 33554432))]
         K dt mm ->
     evtF bsegs RNG POST
       (ST 0x985bc mm xra x5 x6 x7 xa0 (Z_to_bv 64 w2) xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  (* [comment removed for export] *)
  Notation STSL mm w minW len st s v544 J K dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v544 J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x98178 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  (* [comment removed for export] *)
  Notation STLT2 mm w minW len st s v544 J K dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v544 J K dt mm ->
     evtF bsegs RNG POST
       (ST 0x97990 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  (* [comment removed for export] *)
  Local Ltac fr_pair FR a b b' :=
    lazymatch type of FR with
    | context C [C8 (Z_to_bv 64 a) :: C8 (Z_to_bv 64 b) :: ?rest] =>
        let new := context C [C8 (Z_to_bv 64 a) :: C8 (Z_to_bv 64 b') :: rest] in
        let H := fresh "FRX" in
        assert (H : new) by (replace (Z_to_bv 64 b') with (Z_to_bv 64 b) by (f_equal; lia); exact FR);
        clear FR; rename H into FR
    end.

  (* [comment removed for export] *)
  Lemma x2_l2hB : forall m1 (dt : list Z) (w : Z) v88 v152 v168 v176 v264 v272 v280 v544 v568 v576 (J K : list word)
      xra x5 x6 x7 xa1 xa3 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> XS1 w < XS1 (w + 1) ->
    (forall m2 (minW len : Z) y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya7 y28 y29 y30 y31,
       minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> len = 2 ^ (TT - (tl + 1 - w)) ->
       STSH m2 w minW len (RV0 w) (XS1 w) v264 v272 v544 J K dt xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 y28 y29 y30 y31) ->
    XBF v88 (Z_to_bv 64 (w + 1)) v152 v168 v176 (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) v264 v272 v280 (Z_to_bv 64 (XS1 (w + 1))) v544 v568 v576 J K dt m1 ->
    evtF bsegs RNG POST
       (ST 0x97ba0 m1 xra x5 x6 x7 (Z_to_bv 64 (tl + 1 - w)) xa1 (Z_to_bv 64 (TT - (tl + 1 - w))) xa3
           (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - TT)))) xa5 (Z_to_bv 64 (XS1 w)) xa7
           xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (RV0 w)) xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros HW HLE HLT KH I. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    set (e := TT - (tl + 1 - w)) in *. set (raw := tl + 1 - w + (tl + 1 - TT)) in *. set (minW := Z.max 1 raw) in *.
    destruct (l2_facts w e minW HW eq_refl HLE ltac:(reflexivity)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct RVXX as [RV0X RVCX]. pose proof (RV0X w HW) as RVW.
    (* [comment removed for export] *)
    runL FR (@nil kza) [0x97ba4] 4%nat (KZB ++ [KZRange tl 1 12; KZRange w 1 12; KZWr SPA 728]) [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run. all: x2_reunp.
    (* [comment removed for export] *)
    zstep.
    rewrite (Z.mod_small e 32) by lia. rewrite Z.shiftl_1_l. rewrite (FseWalkKit.swrap32_small (2 ^ e)) by lia.
    remember (2 ^ e) as len eqn:HLEN.
    (* [comment removed for export] *)
    runL FR (@nil kza) [0x97bb4] 10%nat
      (KZB ++ [KZRange tl 1 12; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange minW 1 12; KZRange len 2 4096; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run. all: x2_reunp.
    (* [comment removed for export] *)
    zstep.
    replace (Z.shiftr ((4294967296 * tl + -4294967296 * w + 4294967296) * 223338299392) 64) with (52 * (tl + 1 - w))
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 64) with 18446744073709551616; clear - TLR HW HMW; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    runL FR (@nil kza) [0x97bec] 16%nat
      (KZB ++ [KZRange tl 1 12; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange minW 1 12; KZRange len 2 4096; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run. all: x2_reunp.
    zstep. if_cases KS; zify_cond KS.
    2: exfalso; rewrite !FseWalkKit.signed_lit in KS by lia; lia.
    runL FR (@nil kza) [0x98198] 8%nat
      (KZB ++ [KZRange tl 1 12; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange minW 1 12; KZRange len 2 4096; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run. all: x2_reunp.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (65536 * tl + -65536 * w + 16842752)) with (Z_to_bv 64 (65536 * (tl + 1 - w) + 16777216)) in FR by (f_equal; lia).
    replace (Z_to_bv 64 (52 * tl + (-52 * w + (4 * minW + WK)) + 52)) with (Z_to_bv 64 (WK + 52 * (tl + 1 - w) + 4 * minW)) in FR by (f_equal; lia).
    replace (Z_to_bv 64 (52 * tl + (-52 * w + WK) + 52)) with (Z_to_bv 64 (WK + 52 * (tl + 1 - w))) in FR by (f_equal; lia).
    replace (Z_to_bv 64 ((52 * tl + (-52 * w + (4 * minW + WK)) + 52) mod 2 ^ 64 / 8)) with (Z_to_bv 64 (Z.shiftr (WK + 52 * (tl + 1 - w) + 4 * minW) 3)) in FR
      by (f_equal; rewrite Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2 ^ 3) with 8; f_equal; lia).
    replace (Z_to_bv 64 (2 * tl + -1 * w + 2)) with (Z_to_bv 64 (2 * tl + 2 - w)) in FR by (f_equal; lia).
    subst raw.
    eapply KH; [reflexivity| reflexivity| close_xb].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l2hA : forall m1 (dt : list Z) (w : Z) v88 v152 v168 v176 v184 v264 v272 v280 v544 v568 v576 (J K : list word)
      xra x5 x6 x7 xa1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) ->
    (forall m2 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31, XS1 w = XS1 (w + 1) ->
       STLT m2 w v88 v152 v168 v176 v184 v264 v272 v280 v544 v568 v576 J K dt
            xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (RV0 w)) xs10 xs11 y28 y29 y30 y31) ->
    (forall m2 (minW len : Z) y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya7 y28 y29 y30 y31, XS1 w < XS1 (w + 1) ->
       minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> len = 2 ^ (TT - (tl + 1 - w)) ->
       STSH m2 w minW len (RV0 w) (XS1 w) v264 v272 v544 J K dt xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 y28 y29 y30 y31) ->
    STLE 0x97b80 m1 w v88 v152 v168 v176 v184 v264 v272 v280 v544 v568 v576 J K dt xra x5 x6 x7 xa1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE KL KH I. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    pose proof (xs1_bounds w ltac:(lia)) as XB0. pose proof (xs1_bounds (w + 1) ltac:(lia)) as XB1.
    destruct (l2_facts w (TT - (tl + 1 - w)) (Z.max 1 (tl + 1 - w + (tl + 1 - TT))) HW eq_refl HLE eq_refl) as (_ & _ & F3 & F4 & _ & _ & _ & _ & F9 & _).
    (* [comment removed for export] *)
    runL FR (@nil kza) [0x97b98; 0x97990] 30%nat
      (KZB ++ [KZRange tl 1 12; KZRange maxW 1 12; KZRange TT 11 12; KZRange w 1 12; KZRange (XS1 w) 0 256; KZRange (XS1 (w + 1)) 0 256;
               KZRange (Z.max 1 (tl + 1 - w + (tl + 1 - TT))) 1 12; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    1: eapply KL; [exact KXBR| close_xb].
    set (raw := tl + 1 - w + (tl + 1 - TT)) in *.
    kx_setreg 14 raw.
    repeat match type of FR with
    | context [C8 (Z_to_bv 64 ?z)] => tryif constr_eq z raw then fail else replace (Z_to_bv 64 z) with (Z_to_bv 64 raw) in FR by (f_equal; lia)
    end.
    (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS.
    1: assert (RAWP : 1 <= raw) by (clear - KS0 KS1 TLR TTR HW HMW; subst raw; Z.div_mod_to_equations; lia).
    2: assert (RAWN : raw <= 0) by (clear - KS TLR TTR HW HMW; subst raw; apply Bool.andb_false_iff in KS; destruct KS as [KS|KS]; apply Z.ltb_ge in KS; Z.div_mod_to_equations; lia).
    all: try clear KS; try clear KS0; try clear KS1.
    2: zstep.
    all: x2_reunp.
    (* [comment removed for export] *)
    1: replace (Z_to_bv 64 raw) with (Z_to_bv 64 (Z.max 1 raw)) by (f_equal; lia).
    2: replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.max 1 raw)) by (f_equal; lia).
    all: kx_setreg 14 (Z.max 1 raw).
    all: subst raw; eapply x2_l2hB; [exact HW| exact HLE| clear - KXBR XB0 XB1 F3 F4; lia| | close_xb].
    all: intros; eapply KH; [clear - KXBR XB0 XB1 F3 F4; lia| eassumption| eassumption| eassumption].
  Qed.

  End FX.
  End FM.
End X2B.
End CANSEC1.
