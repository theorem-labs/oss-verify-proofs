(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs AZ_hft_x1_fk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
Lemma byte_land : forall a b k, 0 <= k -> (Z.land a b / 2^k) mod 256 = Z.land ((a / 2^k) mod 256) ((b / 2^k) mod 256).
Proof.
  intros a b k Hk. rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_land.
  change 256 with (2^8). rewrite <- !Z.land_ones by lia.
  rewrite <- (Z.land_diag (Z.ones 8)) at 1. rewrite !Z.land_assoc. f_equal. rewrite <- !Z.land_assoc. f_equal. apply Z.land_comm.
Qed.
Lemma byte_lor : forall a b k, 0 <= k -> (Z.lor a b / 2^k) mod 256 = Z.lor ((a / 2^k) mod 256) ((b / 2^k) mod 256).
Proof.
  intros a b k Hk. rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_lor.
  change 256 with (2^8). rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l.
Qed.
(* [comment removed for export] *)
Lemma hdr_bytes : forall h t, 0 <= h < 4294967296 -> h mod 256 = 12 -> 0 <= t < 256 ->
  let v := Z.lor (Z.land h 18446744073692774655) (t * 65536) in
  v mod 256 = 12 /\ (v / 256) mod 256 = 0 /\ (v / 65536) mod 256 = t /\ (v / 16777216) mod 256 = (h / 16777216) mod 256 /\ 0 <= v < 4294967296.
Proof.
  intros h t Hh H0 Ht v. subst v.
  assert (B : forall k, 0 <= k -> (Z.lor (Z.land h 18446744073692774655) (t * 65536) / 2^k) mod 256
                = Z.lor (Z.land ((h / 2^k) mod 256) ((18446744073692774655 / 2^k) mod 256)) (((t * 65536) / 2^k) mod 256)).
  { intros k Hk. rewrite byte_lor by lia. rewrite byte_land by lia. reflexivity. }
  split; [| split; [| split; [| split]]].
  - pose proof (B 0 ltac:(lia)) as B0. rewrite !Z.div_1_r in B0. rewrite B0. rewrite H0.
    change (18446744073692774655 mod 256) with 255. change (Z.land 12 255) with 12.
    replace ((t * 65536) mod 256) with 0 by (clear - Ht; Z.div_mod_to_equations; lia). reflexivity.
  - pose proof (B 8 ltac:(lia)) as B8. change (2^8) with 256 in B8. rewrite B8.
    change ((18446744073692774655 / 256) mod 256) with 0. rewrite Z.land_0_r.
    replace ((t * 65536 / 256) mod 256) with 0 by (clear - Ht; Z.div_mod_to_equations; lia). reflexivity.
  - pose proof (B 16 ltac:(lia)) as B16. change (2^16) with 65536 in B16. rewrite B16.
    change ((18446744073692774655 / 65536) mod 256) with 0. rewrite Z.land_0_r.
    replace ((t * 65536 / 65536) mod 256) with t by (rewrite Z.div_mul by lia; rewrite Z.mod_small; lia). apply Z.lor_0_l.
  - pose proof (B 24 ltac:(lia)) as B24. change (2^24) with 16777216 in B24. rewrite B24.
    change ((18446744073692774655 / 16777216) mod 256) with 255.
    replace ((t * 65536 / 16777216) mod 256) with 0 by (rewrite Z.div_small by lia; reflexivity).
    rewrite Z.lor_0_r. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_mod. lia.
  - change 4294967296 with (2^32). apply lor_lt_pow2; [| lia]. split; [apply Z.land_nonneg; lia|].
    pose proof (KXSound.KXS.land_le_l h 18446744073692774655 ltac:(lia) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma rsinv_step : forall (rank r : list Z) k x, 0 <= k -> k + 1 < zlen r -> x = xsym rank (k + 1) ->
  (forall v, 0 <= v <= k -> Znth v r = xsym rank v) -> forall v, 0 <= v <= k + 1 -> Znth v (Zupd (k + 1) x r) = xsym rank v.
Proof.
  intros rank r k x Hk HL -> H v Hv. destruct (Z.eq_dec v (k + 1)) as [->|NE].
  - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity.
  - rewrite Znth_Zupd_other by lia. apply H. lia.
Qed.
Lemma rsinv_0 : forall (rank r : list Z), 0 < zlen r -> forall v, 0 <= v <= 0 -> Znth v (Zupd 0 0 r) = xsym rank v.
Proof. intros rank r HL v Hv. replace v with 0 by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.
  Hypothesis Hr : 0 <= r < 2^32.
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
  Local Ltac x1_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x1_unp_dtM _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x1_unp_wkM _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x1_artM _ _ _ _ _ _ _ _ _ HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x1_open :=
    open_hx HY; unfold KHIGH in *;
    pose proof (x1_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    assert (RSTA : rng RNG SPA 312) by (lazymatch goal with H : rng RNG lo (SPV - lo) |- _ => eapply rng_sub'; [exact H| lia] end);
    lazymatch goal with H1 : DT + 16388 <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 448 <= SPA <= SPV - 416 |- _ =>
      assert (SDSA : DT + 16388 <= SPA \/ SPA + 312 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA \/ SPA + 312 <= WK) by (clear - H2 H3 H4; lia) end;
    hide_all_disj; x1_reunp.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5488) (2^47 - 432); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x625000 (2^47 - 16388); KZRange WK 0x625000 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT 16388 SPA 312; KZDisj WK wksz SPA 312; KZDisj DT 16388 WK wksz] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).
  Notation FRA0 jA jC jD jB jE := ([CB 80 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); CB 16 jC;
                                    C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK); CB 64 jD; CB 80 jB; CB 24 jE; C8 (Z_to_bv 64 FF)]).
  Notation STR pc mm xra dtd tl' nbs x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dtd) (Z_to_bv 64 tl') (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Notation XBm := (XB m5 SPV SPA lo DT WK wksz FF r).
  (* [comment removed for export] *)
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.

  Section TL.
  Variables (hw rank : list Z) (nbs tl dtd : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 11 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis DTD : 0 <= dtd < 4294967296.
  Hypothesis DTD12 : dtd mod 256 = 12.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 312 FF 64; KZRange tl 11 12; KZRange nbs 2 256; KZRange dtd 12 4294967295]) (only parsing).
  (* [comment removed for export] *)
  Notation STS mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x9652c mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 dtd) (Z_to_bv 64 tl)
        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation ST4 mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x964a8 mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 dtd) (Z_to_bv 64 tl)
        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  (* [comment removed for export] *)
  Lemma x1_h3aA : forall m1 (dt rst : list Z) (syb jA jC jD jB jE j3 j5 j6 : list byte) (tl0 fl : Z) xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt ->
    Znth 0 dt + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt = dtd ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) -> zlen rst = 13 -> Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) -> u8arr bsegs m1 (WK + 980) syb -> zlen syb = 256 -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA -> mem_inv bsegs m1 -> munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (FRA0 jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    rw_cells bsegs m1 (SPA + 56) [C8 (Z_to_bv 64 r)] ->
    (forall m2 (dt' : list Z) (k176 : word) (jA' jA2 jC' jD' jB' : list byte) (ya0 ya1 ya2 ya3 : word),
       XBm hw rank tl k176 jA' jA2 jC' jD' jB' jE dt' rst syb m2 -> x1pref tl 0 dt' ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (ST4 m2 xra x5 x6 ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STR 0x96440 m1 xra dtd tl nbs x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC DTLEN DTBY HDTD HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR FFC FR56 K. x1_open.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    assert (LHK : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    assert (LRSB : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length2, RSTLEN; reflexivity).
    unfold X1FFHDR in FFC.
    (* [comment removed for export] *)
    unfold hidden in BFF.
    kx_autoFLAc FR [KAUnp DT 4; KAApp DT 16388; KAShp (0x7fff8000 + DT / 8) DT] [0x964a8; 0x970d8] 60%nat
      (KZB2 ++ [KZRange (DT / 8) 0 (2^44 - 2049); KZWr DT 16388; KZWr (SPA + 104) 16])
      [(SPA, 312)] [(DT, 16388); (SPA, 312)].
    all: try (exfalso; clear - KXBR TLR; lia).
    all: lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_z | _ => idtac end.
    all: lazymatch goal with
         | |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd UDT1
         | |- accP _ _ _ => kx_sh_acc RSDT
         | |- _ => idtac end.
    all: try (first [kx_sh_dead UDT1 1 | x1_sh_deadp UDT1 1]).
    all: kxk_keepg DTC. all: kx_mem. all: kx_tidy_run.
    all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
    try clear KXUL.
    (* [comment removed for export] *)
    match type of DTC with context [Zupd ?i3 _ (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ _)))] =>
      replace i3 with 3 in DTC by lia; replace i2 with 2 in DTC by lia; replace i1 with 1 in DTC by lia; replace i0 with 0 in DTC by lia end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mm _ (CB 80 ?j :: ?rest) =>
      apply (rw_cells_split_CB bsegs _ _ [] 80 j rest [56; 8; 16]%nat) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR end.
    lazymatch type of FR with rw_cells _ ?mm _ (CB 56 ?a :: CB 8 ?b :: ?rest) =>
      destruct (proj1 (ZdWalkKit.rw_cells_app bsegs mm SPA [CB 56 a] (CB 8 b :: rest)) FR) as [FRa FR2];
      destruct (proj1 (ZdWalkKit.rw_cells_app bsegs mm _ [CB 8 b] rest) FR2) as [_ FRr];
      assert (FR' : rw_cells bsegs mm SPA (CB 56 a :: C8 (Z_to_bv 64 r) :: rest))
        by exact (proj2 (ZdWalkKit.rw_cells_app bsegs mm SPA [CB 56 a] (C8 (Z_to_bv 64 r) :: rest))
                    (conj FRa (proj2 (ZdWalkKit.rw_cells_app bsegs mm (SPA + 56) [C8 (Z_to_bv 64 r)] rest) (conj FR56 FRr))));
      clear FR FR2 FRa FRr end.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?l) =>
      assert (DTLEN' : zlen l = 16388) by (rewrite !Zupd_length; exact DTLEN);
      assert (DTBY' : Forall isbyte l) by (repeat apply Forall_Zupd; first [exact DTBY| cbv beta; clear - TLR; Z.div_mod_to_equations; lia]) end.
    eapply (K _ _ (Z_to_bv 64 0)).
    - unfold XB, X1FRB. repeat (split; [eassumption|]). exact FR'.
    - split; [| split; [| split; [| intros u Hu; exfalso; clear - Hu; lia]]].
      + rewrite !Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia).
        first [reflexivity | exact DTD12 | clear - DTD DTD12; rewrite ?(Z.mod_small dtd (2 ^ 64)) by lia; Z.div_mod_to_equations; lia].
      + rewrite !Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). reflexivity.
      + rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia).
        first [reflexivity | clear - TLR; rewrite ?(Z.mod_small tl (2 ^ 64)) by lia; Z.div_mod_to_equations; lia].
    - exact FFC.
  Qed.
  End TL.
End X1B.
End CANSEC1.
