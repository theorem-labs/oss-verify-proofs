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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs AZ_hft_x1_h3.
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
Lemma u32b_upd4' : forall ws i x a b c d, 0 <= i < Z.of_nat (length ws) -> a = 4 * i -> b = 4 * i + 1 -> c = 4 * i + 2 -> d = 4 * i + 3 ->
  Zupd d ((x / 16777216) mod 256) (Zupd c ((x / 65536) mod 256) (Zupd b ((x / 256) mod 256) (Zupd a (x mod 256) (u32b ws))))
  = u32b (Zupd i x ws).
Proof. intros ws i x a b c d Hi -> -> -> ->. apply u32b_upd4. exact Hi. Qed.

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
  Notation XBm := (XB m5 SPV SPA lo DT WK wksz FF r).
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
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 312 FF 64; KZRange tl 11 12; KZRange nbs 2 256]) (only parsing).
  Notation ST4 mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x964a8 mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 dtd) (Z_to_bv 64 tl)
        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  Notation STS mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x9652c mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 dtd) (Z_to_bv 64 tl)
        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  (* [comment removed for export] *)
  Local Ltac rs_ix RST :=
    repeat match type of RST with
    | context [Zupd (WK + ?c - (WK + 52)) _ _] => let d := eval cbv in (c - 52) in replace (WK + c - (WK + 52)) with d in RST by (clear; lia)
    | context [Zupd (?c + WK - (WK + 52)) _ _] => let d := eval cbv in (c - 52) in replace (c + WK - (WK + 52)) with d in RST by (clear; lia)
    end;
    repeat match type of RST with
    | context [Zupd (?a + ?b) _ _] => lazymatch a with context [WK] => fail | _ => let d := eval cbv in (a + b) in change (a + b) with d in RST end
    end.
  (* [comment removed for export] *)
  Local Ltac rs_fold RST RSL :=
    lazymatch type of RST with
    | u8arr _ _ _ (map _ (Zupd ?i3 ((?x / 16777216) mod 256) (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ (u32b ?l)))))) =>
        let k := eval cbv in (i0 / 4) in
        rewrite (u32b_upd4' l k x i0 i1 i2 i3) in RST by (clear - RSL; rewrite ?Zupd_length; lia)
    end.
  Local Ltac rs_xsym r k :=
    let rec go j := lazymatch j with
      | 0 => change (xsym r 0) with 0
      | _ => let j' := eval cbv in (j - 1) in
             replace (xsym r j) with (xsym r j' + Znth j' r) by (rewrite <- (xsym_step r j') by (clear; lia); f_equal; clear; lia); go j'
      end in
    go k.
  (* [comment removed for export] *)
  Local Ltac rs_next rk RST RSI RSL k :=
    lazymatch type of RST with
    | u8arr _ _ _ (map _ (u32b (Zupd _ ?x ?l))) =>
        let E := fresh "ERS" in let rs := fresh "rs" in
        let RSI' := fresh "RSI" in let RSL' := fresh "RSL" in
        assert (RSI' : forall v, 0 <= v <= k -> Znth v (Zupd k x l) = xsym rk v)
          by (let km := eval cbv in (k - 1) in
              apply (rsinv_step rk l km x); [clear; lia| clear - RSL; lia| change (xsym rk (km + 1)) with (xsym rk k); rs_xsym rk k; clear; lia| exact RSI]);
        assert (RSL' : zlen (Zupd k x l) = 13) by (rewrite Zupd_length; exact RSL);
        let RSN' := fresh "RSN" in
        lazymatch goal with RSN : Forall (fun v : Z => 0 <= v) l |- _ =>
          assert (RSN' : Forall (fun v : Z => 0 <= v) (Zupd k x l)) by (apply Forall_Zupd; [exact RSN| lia]); clear RSN end;
        repeat match goal with H : zlen (map _ (u32b l)) = _ |- _ => clear H end;
        remember (Zupd k x l) as rs eqn:E; clear E RSI RSL; try clear l; rename RSI' into RSI; rename RSL' into RSL; rename RSN' into RSNN
    end.
  (* [comment removed for export] *)
  Local Ltac rs_side :=
    lazymatch goal with
    | |- _ /\ _ /\ _ /\ rdn _ _ (wa (WK + ?o)) _ = Some (word_to_le_bytes _ (Z_to_bv 64 (Znth ?i _))) =>
        split; [lia| split; [lia| split; [lia| replace (WK + o) with (WK + 4 * i) by (clear; lia);
          lazymatch goal with RK : u8arr _ ?mm WK _ |- rdn _ _ _ _ = _ => apply (rdn_u32b bsegs mm WK rank i RK); lia end]]]
    | |- _ => idtac
    end.
  Local Ltac rs_post rk RST RSI RSL k :=
    kxk_keepg RST; kx_mem; kx_tidy_run;
    repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end;
    repeat match goal with U : Z.of_nat (length (map _ (Zupd _ _ _))) = _ |- _ => clear U end; rs_ix RST; rs_fold RST RSL; rs_next rk RST RSI RSL k; x1_reunp.

  (* [comment removed for export] *)
  Notation STK pc mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 dtd) (Z_to_bv 64 tl)
        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_rs0A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE j3 j5 j6 : list byte) (tl0 fl : Z) (k176 : word) xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 -> x1pref tl 0 dt ->
    rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    (forall m2 (rs : list Z) (ya2 ya5 ya6 ya7 : word),
       XBm hw rank tl k176 jA jA2 jC jD jB jE dt rs syb m2 -> (forall v, 0 <= v <= 0 -> Znth v rs = xsym rank v) ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (STK 0x964c4 m2 xra x5 x6 (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 4)) ya2 (Z_to_bv 64 (WK + 4)) (Z_to_bv 64 (Znth 0 rank)) ya5 ya6 ya7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (ST4 m1 xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PF FFC K. open_xb I. x1_open.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    assert (LHK : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    assert (LRSB : zlen (map (Z_to_bv 8) (u32b rst)) = 52) by (rewrite length_map, u32b_length2, RSTLEN; reflexivity).
    pose proof (rank_small 0 ltac:(lia)) as R0. pose proof RSTLEN as RSL.
    assert (RSI : forall v, 0 <= v <= -1 -> Znth v rst = xsym rank v) by (intros; exfalso; lia).
    unfold X1FFHDR in FFC.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4] 30%nat (KZB2 ++ [KZRange (tl + 1) 12 13]) [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    kx_mem; kx_tidy_run; repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end; x1_reunp.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 0) 4%nat (Znth 0 rank); KZRange (Znth 0 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd UW1 | |- accP _ _ _ => kx_sh_acc RSW | _ => idtac end.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x5adcc) _ _ _ _) => kx_sh_dead UW1 4 | _ => idtac end.
    all: kxk_keepg RST; kx_mem; kx_tidy_run; repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end; try clear KXUL.
    all: rs_ix RST.
    all: lazymatch type of RST with u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ _ (Zupd _ _ (Zupd _ _ (u32b ?l)))))) =>
           rewrite (u32b_upd4' l 0 0 0 1 2 3) in RST by (clear - RSL; lia) end.
    all: setreg_m 10 tl; setreg_m 11 (WK + 4); setreg_m 13 (WK + 4); setreg_m 14 (Znth 0 rank).
    all: eapply K; [close_xb| apply rsinv_0; clear - RSL; lia| exact FFC].
    all: first [rewrite Zupd_length; exact RSL | apply Forall_Zupd; [exact RSTNN| clear; lia]].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_rsA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE j3 j5 j6 : list byte) (tl0 fl : Z) (k176 : word) xa2 xa5 xa6 xa7 xra x5 x6 x28 x29 x30 x31,
    XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 -> (forall v, 0 <= v <= 0 -> Znth v rst = xsym rank v) ->
    rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
    (forall m2 (rst' : list Z) (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word),
       XBm hw rank tl k176 jA jA2 jC jD jB jE dt rst' syb m2 -> (forall v, 0 <= v <= tl -> Znth v rst' = xsym rank v) ->
       rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl0) (Z_to_bv 64 nbs)) ->
       evtF bsegs RNG POST (STS m2 xra x5 x6 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STK 0x964c4 m1 xra x5 x6 (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 4)) xa2 (Z_to_bv 64 (WK + 4)) (Z_to_bv 64 (Znth 0 rank)) xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RSI FFC K. open_xb I. x1_open.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    assert (LHK : zlen (map (Z_to_bv 8) hw) = 256) by (rewrite length_map; exact LHW).
    assert (LRKB : zlen (map (Z_to_bv 8) (u32b rank)) = 52) by (rewrite length_map, u32b_length2, LRK; reflexivity).
    pose proof RSTLEN as RSL. rename RSTNN into RSNN.
    pose proof rank_small as RKS.
    pose proof (RKS 0 ltac:(lia)) as R0. pose proof (RKS 1 ltac:(lia)) as R1. pose proof (RKS 2 ltac:(lia)) as R2. pose proof (RKS 3 ltac:(lia)) as R3.
    pose proof (RKS 4 ltac:(lia)) as R4. pose proof (RKS 5 ltac:(lia)) as R5. pose proof (RKS 6 ltac:(lia)) as R6. pose proof (RKS 7 ltac:(lia)) as R7.
    pose proof (RKS 8 ltac:(lia)) as R8. pose proof (RKS 9 ltac:(lia)) as R9. pose proof (RKS 10 ltac:(lia)) as R10. pose proof (RKS 11 ltac:(lia)) as R11.
    pose proof (RKS 12 ltac:(lia)) as R12. clear RKS.
    unfold X1FFHDR in FFC.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB1 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 1) 4%nat (Znth 1 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 1 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB2 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 2) 4%nat (Znth 2 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 2 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB3 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 3) 4%nat (Znth 3 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 3 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB4 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 4) 4%nat (Znth 4 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 4 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB5 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 5) 4%nat (Znth 5 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 5 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB6 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 6) 4%nat (Znth 6 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 6 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB7 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 7) 4%nat (Znth 7 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 7 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB8 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 8) 4%nat (Znth 8 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 8 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB9 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 9) 4%nat (Znth 9 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 9 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB10 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 10) 4%nat (Znth 10 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 10 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB11 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x964c4; 0x9652c] 60%nat
      (KZB2 ++ [KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 11) 4%nat (Znth 11 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 11 | _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with RST : u8arr _ _ (WK + 52) (map _ (u32b ?l)) |- _ => assert (LRSB12 : zlen (map (Z_to_bv 8) (u32b l)) = 52) by (rewrite length_map, u32b_length2, RSL; reflexivity) end.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x964c4) _ _ _ _) => idtac | _ => shelve end.
    all: kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x9652c] 60%nat
      (KZB2 ++ [KZRange tl 12 12; KZRange (tl + 1) 12 13; KZWr (WK + 52) 52; KZWord (WK + 4 * 12) 4%nat (Znth 12 rank);
                KZRange (Znth 0 rank) 0 256; KZRange (Znth 1 rank) 0 256; KZRange (Znth 2 rank) 0 256; KZRange (Znth 3 rank) 0 256; KZRange (Znth 4 rank) 0 256;
                KZRange (Znth 5 rank) 0 256; KZRange (Znth 6 rank) 0 256; KZRange (Znth 7 rank) 0 256; KZRange (Znth 8 rank) 0 256; KZRange (Znth 9 rank) 0 256;
                KZRange (Znth 10 rank) 0 256; KZRange (Znth 11 rank) 0 256; KZRange (Znth 12 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187)])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: rs_side.
    all: lazymatch goal with |- evtF _ _ _ _ => rs_post rank RST RSI RSL 12 | _ => idtac end.
    Unshelve.
    (* [comment removed for export] *)
    all: eapply K; [close_xb| intros v Hv; apply RSI; clear - Hv KXBR TLR; lia| exact FFC].
  Qed.
  End TL.
End X1B.
End CANSEC1.
