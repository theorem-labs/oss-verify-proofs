(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs AZ_hft_x1_fk AZ_hft_x1_c16.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit AZ_hft_x1_d4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Lemma lxor_low_ones : forall c n, 0 < n -> 0 <= c < 2^n -> Z.lxor c (Z.ones n) = Z.ones n - c.
Proof.
  intros c n Hn Hc.
  assert (ON : Z.ones n = 2^n - 1) by (rewrite Z.ones_equiv; lia).
  assert (LG : Z.log2 c < n) by (destruct (Z.eq_dec c 0) as [->|NZ]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
  rewrite <- Z.ldiff_ones_l_low by lia.
  symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
Qed.
Lemma lxor_km32 : forall c, 0 <= c < 2147483648 -> Z.lxor c 2147483647 = 2147483647 - c.
Proof. intros c Hc. change 2147483647 with (Z.ones 31). apply (lxor_low_ones c 31); lia. Qed.

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

  Variables (n0 SRC : Z) (flags : word).
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  (* [comment removed for export] *)
  Ltac kxv_reveal :=
    repeat match goal with
    | E : hidden (?v = (?a + 256 * ?x) mod 256) |- _ => unfold hidden in E; rewrite (Z.mul_comm 256), Z_mod_plus_full, (Z.mod_small a 256) in E by lia; subst v
    | E : hidden (?v = ?e) |- _ =>
        first [ lazymatch e with context [ev _ _] => fail | context [edenot _ _] => fail | _ => idtac end; unfold hidden in E; subst v
              | let B := fresh "KB" in assert (B : 0 <= v < 256) by (unfold hidden in E; rewrite E; apply Z.mod_pos_bound; lia); clear E ]
    end.

  Section C16.
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 11 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XFm := (XF m5 SPV SPA lo DT WK wksz FF r hw rank tl).
  Notation XCm := (XC m5 SPV SPA lo DT WK wksz FF r hw rank tl).
  Ltac open_xc I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FR1 & FR2 & FR4);
                    unfold X1FR1 in FR1; unfold X1FR4 in FR4.
  Ltac close_xc := unfold XC, X1FR1, X1FR4; repeat (split; [eassumption|]); eassumption.
  Local Ltac x1_lens :=
    first [ assert (zlen (map (Z_to_bv 8) hw) = 256) by assumption | assert (zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW) ];
    first [ assert (zlen (map (Z_to_bv 8) (u32b rank)) = 52) by assumption
          | assert (zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity) ];
    try lazymatch goal with
    | RST : u8arr _ _ (WK + 52) (map _ (u32b ?rs)) |- _ =>
        first [ assert (zlen (map (Z_to_bv 8) (u32b rs)) = 52) by assumption
              | assert (zlen (map (Z_to_bv 8) (u32b rs)) = 52) by (rewrite length_map, u32b_length2, ?Zupd_length2; lia) ]
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
  Lemma fill_facts : forall w, 1 <= w <= tl ->
    0 <= Znth w rank <= 256 /\ 0 <= xsym rank w /\ xsym rank w + Znth w rank <= 256 /\ 0 <= xcur rank w /\
    0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl /\ 2^tl <= 4096 /\ 1 <= hw_cells w <= 2048.
  Proof.
    intros w Hw. pose proof STATS as (TL0 & _).
    pose proof (rank_small w ltac:(lia)) as CNTR.
    pose proof (xcur_nonneg _ _ _ STATS w ltac:(lia)) as CUR0. pose proof (xsym_nonneg _ _ _ STATS w ltac:(lia)) as SYM0.
    assert (P2TL : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (WSL : FseNCount.Zlength (firstn (Z.to_nat nbs) hw) = nbs) by (unfold FseNCount.Zlength; rewrite length_firstn; lia).
    assert (SYMH : xsym rank w + Znth w rank <= 256).
    { rewrite <- (xsym_step rank w ltac:(lia)). pose proof (xsym_mono _ _ _ STATS (w + 1) 13 ltac:(lia) ltac:(lia)) as X.
      rewrite (xsym_total _ _ _ STATS), WSL in X. lia. }
    assert (LENR : 1 <= hw_cells w <= 2048).
    { split; [unfold hw_cells; destruct (Z.eqb_spec w 0); [lia|]; pose proof (Z.pow_pos_nonneg 2 (w - 1) ltac:(lia) ltac:(lia)); lia | apply hw_cells_bound; lia]. }
    assert (CLB : 0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl).
    { rewrite <- (xcur_step rank w ltac:(lia)). pose proof (xcur_mono _ _ _ STATS (w + 1) (tl + 1) ltac:(lia) ltac:(lia)) as X.
      rewrite (xcur_end _ _ _ STATS) in X. split; [nia | lia]. }
    repeat split; lia.
  Qed.
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 312 FF 64; KZRange tl 11 12; KZRange nbs 2 256]) (only parsing).
  (* [comment removed for export] *)
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000) xs5
             xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STC pc mm nb len xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 (Z_to_bv 64 nb) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (SF 0x968a4 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation XDm j0 j192 dt rst syb w cur sym cnt nb len q k192 k288 :=
    (XCm j0 j192 dt rst syb w cur sym cnt (Z_to_bv 64 nb) (Z_to_bv 64 (2 * len)) k192
         (Z_to_bv 64 (DT + 2 * (q - cur) + 4)) (Z_to_bv 64 (DT + 2 * (q - cur) + 11)) (Z_to_bv 64 (DT + 2 * (q - cur) + 28))
         (Z_to_bv 64 (DT + 2 * (q - cur) + 35)) (Z_to_bv 64 (DT + 2 * (q - cur) + 19)) (Z_to_bv 64 (DT + 2 * (q - cur) + 20))
         (Z_to_bv 64 (DT + 2 * (q - cur) + 27)) (Z_to_bv 64 (DT + 2 * (q - cur) + 20)) (Z_to_bv 64 (DT + 2 * (q - cur) + 12))
         (Z_to_bv 64 (DT + 4 + 2 * q)) k288).
  (* [comment removed for export] *)
  Notation STO mm s cur len xra x5 x6 x7 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 (Z_to_bv 64 s) xa3 xa4 xa5 xa6 xa7
             xs2 xs3 (Z_to_bv 64 0x7fff8000) xs5 xs6 (Z_to_bv 64 (2 * cur)) xs8 xs9 xs10 (Z_to_bv 64 len)
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x96ca4) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STI mm u q cur len d xra x5 x6 x7 xa0 xa2 xa4 xa5 xs3 x28 x29 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 (0x7fff8000 + (DT + 4 + 2 * q + 32 * u) / 8)) xa2 (Z_to_bv 64 (DT + 2 * (q - cur) + 11 + 32 * u)) xa4 xa5
             (Z_to_bv 64 d) (Z_to_bv 64 (DT + 2 * (q - cur) + 12 + 32 * u))
             (Z_to_bv 64 (16 * u)) xs3 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (DT + 2 * (q - cur) + 28 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 20 + 32 * u))
             (Z_to_bv 64 (2 * cur)) (Z_to_bv 64 (DT + 2 * (q - cur) + 27 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 35 + 32 * u))
             (Z_to_bv 64 (DT + 2 * (q - cur) + 4 + 32 * u)) (Z_to_bv 64 len)
             x28 x29 (Z_to_bv 64 (DT + 2 * (q - cur) + 20 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 19 + 32 * u)))
        F (Z_to_bv 64 0x96d18) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STI2 mm u q cur len d xa0 xa2 x28 :=
    (MS (mkR (Z_to_bv 64 (d / 281474976710656)) (Z_to_bv 64 SPA) gp tp (Z_to_bv 64 (d / 256)) (Z_to_bv 64 (d / 16777216)) (Z_to_bv 64 len) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 (0x7fff8000 + (DT + 4 + 2 * q + 32 * u) / 8)) xa2 (Z_to_bv 64 (DT + 2 * (q - cur) + 11 + 32 * u)) (Z_to_bv 64 (DT + (2 * q + 32 * u) + 20)) (Z_to_bv 64 (d / 1099511627776))
             (Z_to_bv 64 d) (Z_to_bv 64 (DT + 2 * (q - cur) + 12 + 32 * u))
             (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (d / 4294967296)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (DT + 2 * (q - cur) + 28 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 20 + 32 * u))
             (Z_to_bv 64 (2 * cur)) (Z_to_bv 64 (DT + 2 * (q - cur) + 27 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 35 + 32 * u))
             (Z_to_bv 64 (DT + 2 * (q - cur) + 4 + 32 * u)) (Z_to_bv 64 (d / 65536))
             x28 (Z_to_bv 64 (d / 72057594037927936)) (Z_to_bv 64 (DT + 2 * (q - cur) + 20 + 32 * u)) (Z_to_bv 64 (DT + 2 * (q - cur) + 19 + 32 * u)))
        F (Z_to_bv 64 0x96dc0) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STDL mm cur len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 (Z_to_bv 64 0x7fff8000) xs5 xs6 (Z_to_bv 64 (2 * cur)) xs8 xs9 xs10 (Z_to_bv 64 len)
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x96c18) fc None mm (seg_rom bsegs)).
  Ltac close_cells := first [eassumption | eapply rw_cells_eqv; [eassumption| repeat (first [apply cells_eq8; [clear; lia|] | apply cells_eqc]); reflexivity]].
  Ltac close_xd := unfold XC, X1FR1, X1FR4; repeat (split; [close_cells|]); close_cells.
  Ltac setreg_sh r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z')
                        by (f_equal; rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8; Z.div_mod_to_equations; lia)
    end.
  Ltac sti_regs q cur u :=
    setreg_sh 11 (0x7fff8000 + (DT + 4 + 2 * q + 32 * u) / 8);
    setreg_m 13 (DT + 2 * (q - cur) + 11 + 32 * u); setreg_m 17 (DT + 2 * (q - cur) + 12 + 32 * u); setreg_m 18 (16 * u);
    setreg_m 21 (DT + 2 * (q - cur) + 28 + 32 * u); setreg_m 22 (DT + 2 * (q - cur) + 20 + 32 * u);
    setreg_m 24 (DT + 2 * (q - cur) + 27 + 32 * u); setreg_m 25 (DT + 2 * (q - cur) + 35 + 32 * u);
    setreg_m 26 (DT + 2 * (q - cur) + 4 + 32 * u); setreg_m 30 (DT + 2 * (q - cur) + 20 + 32 * u);
    setreg_m 31 (DT + 2 * (q - cur) + 19 + 32 * u).

  (* [comment removed for export] *)
  Ltac c16_cells DTC DTLEN DTBY b dt0 PF :=
    match type of DTC with context [Zupd ?i15 _ (Zupd ?i14 _ (Zupd ?i13 _ (Zupd ?i12 _ (Zupd ?i11 _ (Zupd ?i10 _ (Zupd ?i9 _ (Zupd ?i8 _ (Zupd ?i7 _ (Zupd ?i6 _ (Zupd ?i5 _ (Zupd ?i4 _ (Zupd ?i3 _ (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ (_))))))))))))))))] =>
         replace i0 with (4 + 2 * (b + 2)) in DTC by lia;
         replace i1 with (4 + 2 * (b + 2) + 1) in DTC by lia;
         replace i2 with (4 + 2 * (b + 3)) in DTC by lia;
         replace i3 with (4 + 2 * (b + 3) + 1) in DTC by lia;
         replace i4 with (4 + 2 * (b + 0)) in DTC by lia;
         replace i5 with (4 + 2 * (b + 0) + 1) in DTC by lia;
         replace i6 with (4 + 2 * (b + 1)) in DTC by lia;
         replace i7 with (4 + 2 * (b + 1) + 1) in DTC by lia;
         replace i8 with (4 + 2 * (b + 6)) in DTC by lia;
         replace i9 with (4 + 2 * (b + 6) + 1) in DTC by lia;
         replace i10 with (4 + 2 * (b + 7)) in DTC by lia;
         replace i11 with (4 + 2 * (b + 7) + 1) in DTC by lia;
         replace i12 with (4 + 2 * (b + 4)) in DTC by lia;
         replace i13 with (4 + 2 * (b + 4) + 1) in DTC by lia;
         replace i14 with (4 + 2 * (b + 5)) in DTC by lia;
         replace i15 with (4 + 2 * (b + 5) + 1) in DTC by lia end;
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d0) =>
      assert (PF' : x1pref tl (b + 8) d0)
        by (replace (b + 8) with (b + Z.of_nat 8) by lia;
            eapply (prf_close_c tl b [5; 4; 7; 6; 1; 0; 3; 2]); [| lia| vm_compute; reflexivity];
            eapply (prf_st_sy tl b [5; 4; 7; 6; 1; 0; 3; 2] _ 5); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [4; 7; 6; 1; 0; 3; 2] _ 5); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [4; 7; 6; 1; 0; 3; 2] _ 4); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [7; 6; 1; 0; 3; 2] _ 4); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [7; 6; 1; 0; 3; 2] _ 7); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [6; 1; 0; 3; 2] _ 7); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [6; 1; 0; 3; 2] _ 6); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [1; 0; 3; 2] _ 6); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [1; 0; 3; 2] _ 1); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [0; 3; 2] _ 1); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [0; 3; 2] _ 0); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [3; 2] _ 0); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [3; 2] _ 3); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [2] _ 3); [| lia| lia| reflexivity| rewrite !Zupd_length2; lia| lia];
            eapply (prf_st_sy tl b [2] _ 2); [| lia| lia| reflexivity];
            eapply (prf_st_nb tl b [] dt0 2); [apply prf_open; exact PF| lia| lia| reflexivity| lia| lia]);
      assert (DTLEN' : zlen d0 = 16388) by (rewrite !Zupd_length2; exact DTLEN);
      assert (DTBY' : Forall isbyte d0) by (repeat (apply Forall_Zupd; [| lia]); exact DTBY)
    end.

  (* [comment removed for export] *)
  Lemma x1_cd_in1A : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q u sv d : Z) (k288 : word)
      xra x5 x6 x7 xa0 xa2 xa4 xa5 xs3 x28 x29,
    XDm j0 j192 dt rst syb w cur sym cnt nb len q (Z_to_bv 64 s) k288 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> cur <= q -> q + len <= 4096 -> 0 <= u -> 16 * u + 16 <= len ->
    0 <= sv < 256 -> d4f d sv nb -> x1pref tl (q + 16 * u) dt ->
    (forall m2 (dt' : list Z) (ya0 ya2 y28 : word),
       XDm j0 j192 dt' rst syb w cur sym cnt nb len q (Z_to_bv 64 s) k288 m2 -> x1pref tl (q + 16 * u + 8) dt' ->
       evtF bsegs RNG POST (STI2 m2 u q cur len d ya0 ya2 y28)) ->
    evtF bsegs RNG POST (STI m1 u q cur len d xra x5 x6 x7 xa0 xa2 xa4 xa5 xs3 x28 x29).
  Proof.
    intros until x29; intros I HW HC HS HCN W5 HL HNB HSR Q0 QH U0 UH SVR D4F PF K. open_xc I. x1_open. x1_lens.
    pose proof (fill_facts w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR). rewrite <- HL in CL0, CLH, LENR. rewrite <- HC, <- HS, <- HCN in *.
    pose proof (proj1 (len16 w ltac:(lia))) as LEN16. rewrite <- HL in LEN16.
    pose proof D4F as (DR & D4X). clear D4F.
    kx_autoFLAc tt [KAUnp DT 16388; KAApp DT 16388; KAShp (0x7fff8000 + (DT + 4 + 2 * q + 32 * u) / 8) (DT + 4 + 2 * q + 32 * u)] [0x96dc0; 0x970d8] 120%nat
      (KZB2 ++ [KZRange w 1 12; KZRange nb 0 12; KZRange cnt 1 256; KZRange sym 0 256; KZRange cur 0 4096; KZRange len 16 2048;
               KZRange s 0 255; KZRange q 0 4080; KZRange (q - cur) 0 4080; KZRange u 0 127; KZRange (q + 16 * u) 0 4080; KZRange d 0 18446744073709551615;
               KZWr (DT + 4 + 2 * q + 32 * u) 32])
      [(SPA, 136)] [(DT, 16388); (SPA, 312)].
    all: lazymatch goal with
         | |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd UDT1
         | |- accP _ _ _ => kx_sh_acc RSDT
         | |- _ => idtac end.
    all: try (first [kx_sh_dead UDT1 1 | x1_sh_deadp UDT1 1]).
    all: kxk_keepg DTC. all: kx_mem.
    all: pose proof D4X as (D4M & D40 & D41 & D42 & D43 & D44 & D45 & D46 & D47).
    all: repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; rewrite ?D4M, ?D40, ?D41, ?D42, ?D43, ?D44, ?D45, ?D46, ?D47 in E; subst v end.
    all: clear D4M D40 D41 D42 D43 D44 D45 D46 D47. all: kx_tidy_run.
    all: try clear KXUL.
    all: c16_cells DTC DTLEN DTBY (q + 16 * u) dt PF.
    all: pose proof D4X as (D4M & D4R); rewrite ?D4M; clear D4M D4R.
    all: eapply K; [close_xd| exact PF'].
  Qed.
  End C16.
End X1B.
End CANSEC1.
