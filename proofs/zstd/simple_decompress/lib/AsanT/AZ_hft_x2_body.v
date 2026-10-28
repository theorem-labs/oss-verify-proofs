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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_defs AZ_hft_x2_geo AZ_hft_x2_kit AZ_hft_x2h_defs AZ_hft_x2_defs AZ_hft_x2_facts AZ_hft_x2_p1 AZ_hft_x2_p2 AZ_hft_x2_s1 AZ_hft_x2_s2 AZ_hft_x2_s3 AZ_hft_x2_l2i AZ_hft_x2_wl AZ_hft_x2_ex.
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
  Notation ST0 mm xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31 :=
    (ST 0x97570 mm xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xsrc (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) xnv xflv xs10 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) x29 x30 x31)
    (only parsing).

  (* [comment removed for export] *)
  Section GLUEG.
  Hypothesis SKAG : forall maxW, 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> forall (rs0 rv : list Z) (syb : list byte),
    AZ_hft_x2_facts.RSF rank maxW rs0 -> AZ_hft_x2_facts.RVX rank tl maxW rv ->
    AZ_hft_x2_l2i.SKA_T RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r POST hw rank nbs tl k0 k8 k704 k712 maxW rs0 rv syb.
  Hypothesis JNAG : forall maxW, 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> forall (rs0 rv : list Z) (syb : list byte),
    AZ_hft_x2_facts.RSF rank maxW rs0 -> AZ_hft_x2_facts.RVX rank tl maxW rv ->
    AZ_hft_x2_l2i.JNA_T RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r POST hw rank nbs tl k0 k8 k704 k712 maxW rs0 rv syb.
  Hypothesis SLAG : forall maxW, 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> forall (rs0 rv : list Z) (syb : list byte),
    AZ_hft_x2_facts.RSF rank maxW rs0 -> AZ_hft_x2_facts.RVX rank tl maxW rv ->
    AZ_hft_x2_l2i.SLA_T RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r POST hw rank nbs tl k0 k8 k704 k712 maxW rs0 rv syb.

  (* [comment removed for export] *)
  Lemma x2_bodyA : forall (dtb : list byte) xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31,
    mem_inv bsegs m5 -> stk bsegs m5 lo SPA ->
    rw_cells bsegs m5 SPA (X2F FF DT WK k0 k8 k16 k24 k32 k40 k48 (Z_to_bv 64 hdw) k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288
                             k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592
                             k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712) ->
    rw_cells bsegs m5 (FF + 48) [C4 (Z_to_bv 64 nbs)] ->
    u8arr bsegs m5 DT dtb -> zlen dtb = 16388 ->
    u8arr bsegs m5 (WK + 992) (map (Z_to_bv 8) hw) -> u32arr bsegs m5 (WK + 624) (map (Z_to_bv 64) rank) ->
    rw_cells bsegs m5 (WK + 676) [CB 60 (repeat (Z_to_bv 8 0) 60)] ->
    stk bsegs m5 WK (WK + 624) -> stk bsegs m5 (WK + 736) (WK + 992) -> stk bsegs m5 (WK + 1248) (WK + wksz) ->
    (forall (maxW : Z) (rs0 rv dt : list Z) (syb : list byte) (m2 : amem)
            (q0 q8 q16 q24 q32 q40 q48 q64 q72 q80 q88 q104 q144 q152 q160 q168 q176 q184 q192 q200 q208 q216 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q352 q360
             q368 q376 q384 q392 q400 q408 q416 q424 q432 q440 q448 q456 q464 q472 q480 q488 q496 q504 q512 q520 q528 q536 q544 q552 q560 q568 q576 q584 q592 q600 q608 q616 q624 q632 q640 q648 q656 q664 q672 q680
             q688 q696 q704 q712 : word)
            (yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys11 y28 y29 y30 y31 : word),
       1 <= maxW <= tl ->
       XB m5 SPV SPA lo DT WK wksz FF nbs hw rank q0 q8 q16 q24 q32 q40 q48 q64 q72 q80 q88 q104 q144 q152 q160 q168 q176 q184 q192 q200 q208 q216 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296
          q304 q312 q320 q328 q336 q344 q352 q360 q368 q376 q384 q392 q400 q408 q416 q424 q432 q440 q448 q456 q464 q472 q480 q488 q496 q504 q512 q520 q528 q536 q544 q552 q560 q568 q576 q584 q592 q600
          q608 q616 q624 q632 q640 q648 q656 q664 q672 q680 q688 q696 q704 q712 dt rs0 syb rv m2 ->
       x2pref TT (2 ^ TT) dt -> Znth 0 dt = 12 -> Znth 1 dt = 1 -> Znth 2 dt = TT ->
       evtF bsegs RNG POST (ST 0x99470 m2 yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) ys2 ys3 ys4 ys5 ys6 ys7 ys9 (Z_to_bv 64 r) ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST0 m5 xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xsrc xs10 x29 x30 x31).
  Proof.
    intros until x31; intros MI STK FR0 NBC DTC0 DTBL HWC RK0 RS00 WS1 WS2 WKR KENDX.
    pose proof STATS as (TLR & _ & _ & LRK' & _).
    pose proof (TT_range TLR) as TTR.
    open_hx2 HY. pose proof (x2_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF).
    (* [comment removed for export] *)
    rewrite <- (bytes_of_unsigned dtb) in DTC0. set (dt := map bv_unsigned dtb) in *.
    assert (DTLEN : zlen dt = 16388) by (subst dt; rewrite length_map; exact DTBL).
    assert (DTBY : Forall isbyte dt) by (subst dt; apply bytes_unsigned_range).
    clearbody dt.
    pose proof (u32arr_u32b bsegs m5 (WK + 624) rank RK0) as RK.
    apply stk_of_rw_cells in RS00. cbn [cells_size csize Nat.add] in RS00.
    destruct (u32b_of_stk bsegs m5 (WK + 676) 15%nat ltac:(replace (WK + 676 + 4 * Z.of_nat 15) with (WK + 676 + Z.of_nat 60) by lia; exact RS00) ltac:(lia) ltac:(lia)) as (rs0 & RS0 & RS0L & RS0N).
    assert (RS0LEN : zlen rs0 = 15) by (rewrite RS0L; reflexivity).
    assert (RS0NN : Forall (fun v : Z => 0 <= v) rs0) by (eapply Forall_impl; [| exact RS0N]; cbv beta; intros; lia).
    destruct (u32b_of_stk bsegs m5 WK 156%nat ltac:(replace (WK + 4 * Z.of_nat 156) with (WK + 624) by lia; exact WS1) ltac:(lia) ltac:(lia)) as (rv & RV & RVL & RVN).
    assert (RVLEN : zlen rv = 156) by (rewrite RVL; reflexivity).
    assert (RVNN : Forall (fun v : Z => 0 <= v) rv) by (eapply Forall_impl; [| exact RVN]; cbv beta; intros; lia).
    destruct (stk_open bsegs m5 (WK + 736) (WK + 992) (WK + 736) 256%nat WS2 ltac:(lia) ltac:(lia)) as (syb & SYC & _ & _).
    assert (SYLEN : zlen syb = 256) by (destruct SYC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; rewrite LJ; reflexivity).
    apply u8arr_of_rw_cells in SYC.
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_p1.x2_p1aA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k24 k32 k40 k48 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv) as P1AA.
    eapply (P1AA m5 dt rs0 rv syb).
    { eapply XB_close; [exact DTC0| exact DTLEN| exact DTBY| exact HWC| exact RK| exact RS0| exact RS0LEN| exact RS0NN| exact SYC| exact SYLEN| exact RV| exact RVLEN| exact RVNN
                      | exact WKR| exact NBC| exact STK| exact MI| apply munch_refl| apply wmono_refl| exact FR0]. }
    clear P1AA. intros m2 ya2 I2.
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_p1.x2_m_loopA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv) as M_LOOPA.
    eapply (M_LOOPA (Z.to_nat tl) m2 dt rs0 rv syb tl 0); [exact I2| lia| lia| lia| intros v Hv; exact (st_rank_high _ _ _ STATS v Hv)|].
    clear M_LOOPA. intros m3 maxW za4 za5 za6 za7 HMW RNZ HIGH I3.
    assert (HMW' : 1 <= maxW <= tl) by lia.
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_p1.x2_p1bA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv) as P1BA.
    eapply (P1BA m3 dt rs0 rv syb maxW); [exact I3| exact HMW'|].
    clear P1BA. intros m4 wa2 I4.
    pose proof (@AZ_hft_x2_p2.x2_r_loopA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv) as R_LOOPA.
    eapply (R_LOOPA (Z.to_nat maxW) m4 dt rs0 rv syb maxW 1); [exact I4| exact HMW'| lia| lia| rewrite (xs1_1 rank); reflexivity| unfold AZ_hft_x2_facts.RINV; intros; lia|].
    clear R_LOOPA. intros m6 rs1 w5 w6 w7 wr2 wa5 wa6 wa7 I6 RI6.
    pose proof (@AZ_hft_x2_p2.x2_p1cA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv) as P1CA.
    eapply (P1CA m6 dt rs1 rv syb maxW); [exact I6| exact HMW'| exact RI6|].
    clear P1CA. intros m7 rs2 v6 va2 va3 I7 RI7 R17 RM7.
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_s1.x2_s_loopA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv maxW HMW' HIGH) as S_LOOPA.
    eapply (S_LOOPA (Z.to_nat nbs) m7 dt rs2 rv syb 0); [exact I7| lia| lia| exact (AZ_hft_x2_facts.sinv0 hw rank nbs maxW rs2 RI7 R17)|].
    clear S_LOOPA. intros m8 rs3 syb3 ua1 u30 u31 I8 SI8.
    pose proof (@AZ_hft_x2_s2.x2_s_exitA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k32 k40 k48 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv maxW HMW') as S_EXITA.
    eapply (S_EXITA m8 dt rs3 rv syb3); [exact I8| exact SI8|].
    clear S_EXITA. intros m9 rs4 t5 t6 ta2 ta5 ta7 I9 RSF9.
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_s2.x2_v_loopA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k32 k40 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv maxW HMW' HIGH) as V_LOOPA.
    eapply (V_LOOPA (Z.to_nat maxW) m9 dt rs4 rv syb3 1); [exact I9| lia| lia| rewrite (rv0_1 rank tl TT); reflexivity| unfold AZ_hft_x2_facts.VINV; intros; lia|].
    clear V_LOOPA. intros m10 rv1 s5 s6 sa2 sa5 sa7 I10 VI10.
    (* [comment removed for export] *)
    assert (FILL : forall m11 (rv2 : list Z) z5 z6 z7 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs9 zs10 zs11 z28,
      XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 (Z_to_bv 64 (hdw mod 2 ^ 64 / 16777216)) (Z_to_bv 64 r) k32 k40 (Z_to_bv 64 maxW) (Z_to_bv 64 hdw) k72 (Z_to_bv 64 (tl + 1)) k88 k104
         k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 (Z_to_bv 64 (DT + 4)) k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392
         k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 TT) (Z_to_bv 64 (WK + 736))
         k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs4 syb3 rv2 m11 ->
      AZ_hft_x2_facts.ROWS rank tl maxW (TT - (tl + 1 - maxW) + 1) 1 rv2 ->
      evtF bsegs RNG POST (ST 0x97904 m11 xra z5 z6 z7 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs9 zs10 zs11
                             z28 (Z_to_bv 64 WK) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (WK + 676)))).
    { intros until z28; intros IX ROWSX.
      pose proof (AZ_hft_x2_facts.rvx_of_rows hw rank tl maxW rv2 ROWSX) as RVXX.
      pose proof (RSF9 : AZ_hft_x2_facts.RSF rank maxW rs4) as RSFX.
      pose proof (@AZ_hft_x2_wl.x2_fillsA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR TP POST hw rank nbs tl STATS NBSR LHW LRK
                    k0 k8 k32 k40 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392
                    k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712
                    maxW HMW' HIGH rs4 rv2 syb3 RSFX RVXX
                    (SKAG maxW HMW' HIGH rs4 rv2 syb3 RSFX RVXX) (JNAG maxW HMW' HIGH rs4 rv2 syb3 RSFX RVXX) (SLAG maxW HMW' HIGH rs4 rv2 syb3 RSFX RVXX)) as FILLSA.
      eapply FILLSA; [exact IX| apply x2pref_0|]. clear FILLSA.
      intros m13 dt' y88 y104 y152 y168 y176 y184 y264 y272 y280 y288 y544 y568 y576 J K yra e5 e6 e7 ea0 ea1 ea2 ea3 ea4 ea5 ea6 ea7 es2 es3 es4 es5 es6 es7 es9 es10 es11 e28 e29 e30 e31 PRE13.
      pose proof (@AZ_hft_x2_ex.x2_exitA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HM HR POST hw rank nbs tl STATS LHW LRK k0 k8
                    (nth 0 J (Z_to_bv 64 0)) (nth 1 J (Z_to_bv 64 0)) (nth 2 J (Z_to_bv 64 0)) (nth 3 J (Z_to_bv 64 0)) (nth 4 J (Z_to_bv 64 0)) (nth 5 J (Z_to_bv 64 0)) (nth 6 J (Z_to_bv 64 0)) (nth 7 J (Z_to_bv 64 0))
                    (nth 8 J (Z_to_bv 64 0)) (nth 9 J (Z_to_bv 64 0)) (nth 10 J (Z_to_bv 64 0)) (nth 11 J (Z_to_bv 64 0)) (nth 12 J (Z_to_bv 64 0)) (nth 13 J (Z_to_bv 64 0)) (nth 14 J (Z_to_bv 64 0)) (nth 15 J (Z_to_bv 64 0))
                    (nth 16 J (Z_to_bv 64 0)) (nth 17 J (Z_to_bv 64 0)) (nth 18 J (Z_to_bv 64 0)) (nth 19 J (Z_to_bv 64 0)) (nth 20 J (Z_to_bv 64 0)) (nth 21 J (Z_to_bv 64 0)) (nth 22 J (Z_to_bv 64 0)) (nth 23 J (Z_to_bv 64 0))
                    (nth 24 J (Z_to_bv 64 0)) (nth 25 J (Z_to_bv 64 0)) (nth 26 J (Z_to_bv 64 0)) (nth 27 J (Z_to_bv 64 0)) (nth 28 J (Z_to_bv 64 0)) (nth 29 J (Z_to_bv 64 0)) (nth 30 J (Z_to_bv 64 0))
                    (nth 31 J (Z_to_bv 64 0)) (nth 32 J (Z_to_bv 64 0))
                    (nth 0 K (Z_to_bv 64 0)) (nth 1 K (Z_to_bv 64 0)) (nth 2 K (Z_to_bv 64 0)) (nth 3 K (Z_to_bv 64 0)) (nth 4 K (Z_to_bv 64 0)) (nth 5 K (Z_to_bv 64 0)) (nth 6 K (Z_to_bv 64 0)) (nth 7 K (Z_to_bv 64 0))
                    (nth 8 K (Z_to_bv 64 0)) (nth 9 K (Z_to_bv 64 0)) (nth 10 K (Z_to_bv 64 0)) k704 k712 maxW HMW' rs4 rv2 syb3) as EXITA.
      eapply EXITA; [exact PRE13|]. clear EXITA.
      intros m14 dt'' eb0 eb1 eb2 eb3 PRE14 Z0 Z1 Z2 IB.
      eapply KENDX; [exact HMW'| exact IB| exact PRE14| exact Z0| exact Z1| exact Z2]. }
    (* [comment removed for export] *)
    pose proof (@AZ_hft_x2_s3.x2_w_entA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k32 k40 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv maxW HMW') as W_ENTA.
    eapply (W_ENTA m10 dt rs4 rv1 syb3); [exact I10| exact VI10| |]; clear W_ENTA.
    - intros m11 q6 q7 qa2 q28 LE I11 ROWS11.
      pose proof (@AZ_hft_x2_s3.x2_w_loopA _ RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r HY UDT UW ART0 Hr HR POST hw rank nbs tl STATS NBSR LHW LRK k0 k8 k32 k40 k72 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 xnv xflv maxW HMW' HIGH) as W_LOOPA.
      eapply (W_LOOPA 13%nat m11 dt rs4 rv1 syb3 (tl - maxW + 1)); [exact I11| lia| lia| exact ROWS11|]. clear W_LOOPA.
      intros m12 rv2 g5 g6 g7 ga0 ga1 ga2 ga3 ga4 ga5 ga6 ga7 gs2 gs3 gs4 gs5 gs6 gs7 gs9 gs10 gs11 g28 I12 ROWS12. eapply FILL; [exact I12| exact ROWS12].
    - intros m11 g5 g6 g7 ga0 ga1 ga2 ga3 ga4 ga5 ga6 ga7 gs2 gs3 gs4 gs5 gs6 gs7 gs9 gs10 gs11 g28 LT I11 ROWS11. eapply FILL; [exact I11| exact ROWS11].
  Qed.
  End GLUEG.

End X2B.
End CANSEC1.
