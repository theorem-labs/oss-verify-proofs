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

  (* [comment removed for export] *)
  Notation XBP v24 v600 v256 v80 dt rs0 syb rv mm :=
    (XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 k16 v24 k32 k40 k48 (Z_to_bv 64 hdw) k72 v80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 v256 k264 k272 k280
        k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592
        v600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv mm) (only parsing).
  (* [comment removed for export] *)
  Notation HD24 := (hdw mod 2 ^ 64 / 16777216) (only parsing).

  (* [comment removed for export] *)
  Notation ST0 mm xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31 :=
    (ST 0x97570 mm xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xsrc (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) x29 x30 x31)
    (only parsing).
  (* [comment removed for export] *)
  Notation STM mm w cnt xra x5 x6 x7 xa2 xa4 xa5 xa6 xa7 xs2 xs10 :=
    (ST 0x975b8 mm xra x5 x6 x7 (Z_to_bv 64 HD24) (Z_to_bv 64 (WK + 680)) xa2 (Z_to_bv 64 w) xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 cnt) (Z_to_bv 64 (WK + 676)))
    (only parsing).
  (* [comment removed for export] *)
  Notation STME mm maxW xra x5 x6 x7 xa4 xa5 xa6 xa7 xs2 xs10 :=
    (ST 0x97608 mm xra x5 x6 x7 (Z_to_bv 64 HD24) (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (Znth maxW rank)) (Z_to_bv 64 (maxW - 1)) xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).

  (* [comment removed for export] *)
  Lemma x2_p1aA : forall m1 (dt rs0 rv : list Z) (syb : list byte) xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31,
    XBP k24 k600 k256 k80 dt rs0 syb rv m1 ->
    (forall m2 (ya2 : word),
       XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STM m2 tl 0 xra x5 x6 x7 ya2 xa4 xa5 xa6 xa7 xsrc xs10)) ->
    evtF bsegs RNG POST (ST0 m1 xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31).
  Proof.
    intros until x31; intros I K. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _).
    runL FR (@nil kza) [0x975b8] 60%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange r 0 4294967296; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    all: eapply K; close_xb.
  Qed.

  (* [comment removed for export] *)
  Lemma rank_some : (forall v, 1 <= v <= 12 -> Znth v rank = 0) -> False.
  Proof. intros HZ. pose proof STATS as (TL & _). apply (some_weight _ rank tl 12 STATS ltac:(lia)). intros v Hv. apply HZ. lia. Qed.

  (* [comment removed for export] *)
  Lemma x2_m_bodyA : forall m1 (dt rs0 rv : list Z) (syb : list byte) (w cnt : Z) xra x5 x6 x7 xa2 xa4 xa5 xa6 xa7 xs2 xs10,
    XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m1 ->
    1 <= w <= tl -> cnt = tl - w -> (forall v, w < v <= 12 -> Znth v rank = 0) ->
    (forall m2 (ya2 ya4 ya5 ya6 ya7 : word), 1 <= w - 1 -> Znth w rank = 0 ->
       XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m2 ->
       (forall v, w - 1 < v <= 12 -> Znth v rank = 0) ->
       evtF bsegs RNG POST (STM m2 (w - 1) (cnt + 1) xra x5 x6 x7 ya2 ya4 ya5 ya6 ya7 xs2 xs10)) ->
    (forall m2 (ya4 ya5 ya6 ya7 : word), Znth w rank <> 0 ->
       XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STME m2 w xra x5 x6 x7 ya4 ya5 ya6 ya7 xs2 xs10)) ->
    evtF bsegs RNG POST (STM m1 w cnt xra x5 x6 x7 xa2 xa4 xa5 xa6 xa7 xs2 xs10).
  Proof.
    intros until xs10; intros I HW HC HZ KH KE. open_xb I. x2_open. x2_lens. subst cnt.
    pose proof STATS as (TLR & _). pose proof (rank_small w ltac:(lia)) as RW0.
    runL FR [KAUnp WK 2124; KAApp WK 2124] [0x975b8; 0x97608] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange w 1 12; KZRange (Znth w rank) 0 256; KZWord (WK + 624 + 4 * w) 4%nat (Znth w rank); KZWr SPA 728])
      [(SPA, 728)] [(WK, 2124); (SPA, 728)].
    all: try (split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 624) rank w RK); lia]]]).
    all: kx_mem. all: kx_tidy_run.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97608) _ _ _ _) => kx_setreg 13 (w - 1); kx_setreg 30 (tl - w + 1); eapply KE; [exact KXBR| close_xb]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x975b8) _ _ _ _) =>
             kx_setreg 13 (w - 1); kx_setreg 30 (tl - w + 1);
             eapply KH; [| exact KXBR| close_xb| intros v Hv; destruct (Z.eq_dec v w) as [->|NE]; [exact KXBR| apply HZ; lia]];
             destruct (Z_lt_le_dec 1 w) as [L|L]; [lia|]; exfalso; apply rank_some; intros v Hv; destruct (Z.eq_dec v w) as [->|NE]; [exact KXBR| apply HZ; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_m_loopA : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (w cnt : Z) xra x5 x6 x7 xa2 xa4 xa5 xa6 xa7 xs2 xs10,
    XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m1 ->
    1 <= w <= tl -> w <= Z.of_nat f -> cnt = tl - w -> (forall v, w < v <= 12 -> Znth v rank = 0) ->
    (forall m2 (maxW : Z) (ya4 ya5 ya6 ya7 : word), 1 <= maxW <= w -> Znth maxW rank <> 0 -> (forall v, maxW < v <= 12 -> Znth v rank = 0) ->
       XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STME m2 maxW xra x5 x6 x7 ya4 ya5 ya6 ya7 xs2 xs10)) ->
    evtF bsegs RNG POST (STM m1 w cnt xra x5 x6 x7 xa2 xa4 xa5 xa6 xa7 xs2 xs10).
  Proof.
    induction f as [|f IH]; intros until xs10; intros I HW HF HC HZ KE; [lia|].
    eapply x2_m_bodyA; [exact I| exact HW| exact HC| exact HZ| |].
    - intros m2 ya2 ya4 ya5 ya6 ya7 HW1 Z0 I2 HZ2. eapply IH; [exact I2| lia| lia| lia| exact HZ2|].
      intros m3 maxW za4 za5 za6 za7 HMW NZ HZ3 I3. eapply KE; [lia| exact NZ| exact HZ3| exact I3].
    - intros m2 ya4 ya5 ya6 ya7 NZ I2. eapply (KE m2 w); [lia| exact NZ| exact HZ| exact I2].
  Qed.

  (* [comment removed for export] *)
  Notation STR mm maxW w acc xra x5 x6 x7 xa3 xs2 xs10 :=
    (ST 0x9763c mm xra x5 x6 x7 (Z_to_bv 64 HD24) (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (WK + 624 + 4 * w)) xa3 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (WK + 624 + 4 * w)) (Z_to_bv 64 (maxW + 1 - w)) (Z_to_bv 64 acc)
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).
  (* [comment removed for export] *)
  Notation STR2 mm maxW tot xra x5 x6 x7 xa2 xa5 xa6 xa7 xs2 xs10 :=
    (ST 0x976ac mm xra x5 x6 x7 (Z_to_bv 64 HD24) (Z_to_bv 64 (WK + 680)) xa2 (Z_to_bv 64 tot) (Z_to_bv 64 (maxW + 1)) xa5 xa6 xa7
        xs2 (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))
    (only parsing).

  (* [comment removed for export] *)
  Lemma x2_p1bA : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW : Z) xra x5 x6 x7 xa4 xa5 xa6 xa7 xs2 xs10,
    XBP (Z_to_bv 64 r) (Z_to_bv 64 11) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m1 ->
    1 <= maxW <= tl ->
    (forall m2 (ya3 : word),
       XBP (Z_to_bv 64 r) (Z_to_bv 64 TT) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STR m2 maxW 1 0 xra x5 x6 x7 ya3 xs2 xs10)) ->
    evtF bsegs RNG POST (STME m1 maxW xra x5 x6 x7 xa4 xa5 xa6 xa7 xs2 xs10).
  Proof.
    intros until xs10; intros I HMW K. open_xb I. x2_open. x2_lens.
    pose proof STATS as (TLR & _). pose proof (rank_small maxW ltac:(lia)) as RW0.
    runL FR (@nil kza) [0x9763c; 0x976a8] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256; KZRange maxW 1 12; KZRange (Znth maxW rank) 0 256; KZWr SPA 728])
      [(SPA, 728)] [(SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    all: try (replace (Z_to_bv 64 11) with (Z_to_bv 64 TT) in FR by (unfold AZ_hft_x2_defs.TT; destruct (Z.ltb_spec tl 12); [reflexivity| lia])).
    all: try (replace (Z_to_bv 64 12) with (Z_to_bv 64 TT) in FR by (unfold AZ_hft_x2_defs.TT; destruct (Z.ltb_spec tl 12); [exfalso; lia| reflexivity])).
    all: kx_setreg 12 (WK + 624 + 4 * 1); kx_setreg 15 (WK + 624 + 4 * 1); kx_setreg 14 (maxW + 1); setreg_m 16 (maxW + 1 - 1).
    all: eapply K; close_xb.
  Qed.


End X2B.
End CANSEC1.
