(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs.
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
Ltac x1_sh_deadp H k :=
  match goal with
  | KB : bv_unsigned (ev ?E ?j) <> 0 |- _ =>
      let HR := fresh "KXSH" in kx_read_eq j HR;
      lazymatch type of HR with
      | ev E j = rdval ?segs ?m (wa (?P / 8 + 2147450880)) 1 true =>
          replace (P / 8 + 2147450880) with (shad P) in HR by (rewrite shad_div; unfold ASHOFF; lia);
          lazymatch type of H with
          | unpoisoned m ?R (?R + ?n) =>
              let b := fresh "sb" in let Hb := fresh "Hsb" in let Hv := fresh "Hsv" in let SR := fresh "SR" in
              destruct (unp_shadow_val m R n P k H ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & Hb & Hv);
              rewrite (rdval_sh1 m _ b Hb) in HR; pose proof (sval_range b) as SR; exfalso; rewrite HR in *;
              repeat match goal with K : context [Z_to_bv 64 (sval b)] |- _ => progress kx_sh_simpl_hyp K end;
              rewrite Z_to_bv_unsigned in KB; unfold bv_wrap, bv_modulus in KB; change (2 ^ Z.of_N 64) with 18446744073709551616 in KB;
              destruct Hv as [Hv|Hv]; [rewrite Hv in KB; apply KB; reflexivity | Z.div_mod_to_equations; lia]
          end
      end
  end.

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
  Ltac wordify8_go H segs m A pre rest :=
    lazymatch rest with
    | CB 8 ?j :: ?post =>
        let w := fresh "k" in let H' := fresh "WH" in
        destruct (cb8_as_c8 segs m A pre j post H) as [w H']; clear H; rename H' into H;
        let pre' := eval cbn [app] in (pre ++ [C8 w]) in wordify8_go H segs m A pre' post
    | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in wordify8_go H segs m A pre' post
    | nil => cbn [app] in H
    end.
  Ltac wordify8 H := lazymatch type of H with rw_cells ?segs ?m ?A ?cs => wordify8_go H segs m A (@nil cell) cs end.
  Ltac cbsplit8_go H segs m A pre rest :=
    lazymatch rest with
    | CB ?n ?j :: ?post =>
        let b := eval vm_compute in (Nat.ltb 8 n) in
        lazymatch b with
        | true =>
            let sz := eval vm_compute in (repeat 8%nat (Nat.div n 8)) in
            apply (rw_cells_split_CB segs m A pre n j post sz) in H; [| reflexivity];
            cbn [mk_CB_cells app] in H
        | false => let pre' := eval cbn [app] in (pre ++ [CB n j]) in cbsplit8_go H segs m A pre' post
        end
    | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in cbsplit8_go H segs m A pre' post
    end.
  Ltac cbsplit8 H := repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs => cbsplit8_go H segs m A (@nil cell) cs end).

  Section FK.
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 11 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XBm := (XB m5 SPV SPA lo DT WK wksz FF r hw rank tl).
  Notation XFm := (XF m5 SPV SPA lo DT WK wksz FF r hw rank tl).
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
  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 312 FF 64; KZRange tl 11 12; KZRange nbs 2 256]) (only parsing).
  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  (* [comment removed for export] *)
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000) xs5
             xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STF mm xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST 0x96800 mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation STW mm w xra x5 x6 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x968dc mm xra x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 (Z_to_bv 64 1) (Z_to_bv 64 w) xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_fsetA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte)
      xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XBm (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE dt rst syb m1 ->
    (forall m2 (j0 j192 : list byte) (ya0 ya1 ya2 : word),
       XFm j0 j192 dt rst syb 0 (Znth 0 rank) m2 ->
       evtF bsegs RNG POST (STW m2 1 xra x5 x6 ya0 ya1 ya2 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STF m1 xra x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I K. open_xb I. x1_open. x1_lens.
    pose proof (rank_small 0 ltac:(lia)) as R0.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x968dc; 0x970d8; 0x970d4] 60%nat
      (KZB2 ++ [KZWord (WK + 4 * 0) 4%nat (Znth 0 rank); KZRange (Znth 0 rank) 0 256; KZRange (WK / 8) 0 (2^44 - 187); KZWr (SPA + 0) 312])
      [(SPA, 312)] [(WK, 1492); (SPA, 312)].
    all: lazymatch goal with
         | |- _ /\ _ /\ _ /\ rdn _ _ (wa (WK + ?o)) _ = Some _ =>
             split; [lia| split; [lia| split; [lia| replace (WK + o) with (WK + 4 * 0) by (clear; lia); apply (rdn_u32b bsegs m1 WK rank 0 RK); lia]]]
         | |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd UW1
         | |- accP _ _ _ => kx_sh_acc RSW
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x5adcc) _ _ _ _) => first [kx_sh_dead UW1 4 | x1_sh_deadp UW1 4]
         | |- _ => idtac end.
    all: try (exfalso; clear - KXBR TLR; lia).
    all: kx_mem; kx_tidy_run.
    (* [comment removed for export] *)
    all: cbsplit8 FR.
    all: lazymatch type of FR with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?rest) =>
           pose proof (proj1 (rw_cells_app bsegs mm SPA [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] rest) FR) as [FR1 FRX]; clear FR;
           cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in FRX end.
    all: lazymatch type of FRX with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?rest) =>
           pose proof (proj1 (rw_cells_app bsegs mm A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19] rest) FRX) as [FR2 FR4]; clear FRX;
           cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in FR4 end.
    all: wordify8 FR2.
    all: lazymatch type of FR4 with rw_cells _ _ ?a _ => replace a with (SPA + 296) in FR4 by (clear; lia) end;
         lazymatch type of FR2 with rw_cells _ _ ?a _ => replace a with (SPA + 136) in FR2 by (clear; lia) end.
    all: eapply K; unfold XF, X1FR1, X1FR4; repeat (split; [eassumption|]); try eassumption.
    all: split; [unfold XFR2; do 16 eexists; exact FR2| exact FR4].
  Qed.

  (* [comment removed for export] *)
  Notation FR2W mm w cur sym cnt k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 :=
    (rw_cells bsegs mm (SPA + 136) [C8 (Z_to_bv 64 w); C8 k144; C8 (Z_to_bv 64 cur); C8 k160; C8 (Z_to_bv 64 (WK + 980)); C8 (Z_to_bv 64 sym);
                                    C8 (Z_to_bv 64 cnt); C8 k192; C8 (Z_to_bv 64 281479271743489); C8 k208; C8 k216; C8 k224; C8 k232; C8 k240;
                                    C8 k248; C8 k256; C8 k264; C8 k272; C8 k280; C8 k288]).
  (* [comment removed for export] *)
  Notation STC pc mm nb len xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 (Z_to_bv 64 nb) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) x28 x29 x30 x31).
  (* [comment removed for export] *)
  Definition XC (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt : Z)
      (k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 : word) (m1 : amem) : Prop :=
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) /\ zlen dt = 16388 /\ Forall isbyte dt
    /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank))
    /\ u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) /\ zlen rst = 13
    /\ stk bsegs m1 (WK + 104) (WK + 980) /\ u8arr bsegs m1 (WK + 980) syb /\ zlen syb = 256 /\ stk bsegs m1 (WK + 1492) (WK + wksz)
    /\ stk bsegs m1 lo SPA /\ mem_inv bsegs m1 /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 /\ wmono bsegs m5 m1
    /\ rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0) /\ FR2W m1 w cur sym cnt k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288
    /\ rw_cells bsegs m1 (SPA + 296) (X1FR4 DT WK FF j192).
  Ltac open_xc I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & STK & MI & MU & WM & FR1 & FR2 & FR4);
                    unfold X1FR1 in FR1; unfold X1FR4 in FR4.
  Ltac close_xc := unfold XC, X1FR1, X1FR4; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma x1_wheadA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym : Z)
      xra x5 x6 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XFm j0 j192 dt rst syb cur sym m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w ->
    (forall m2 k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 1 ->
       XC j0 j192 dt rst syb w cur sym (Znth w rank) k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m2 ->
       evtF bsegs RNG POST (STC 0x96ef8 m2 (tl + 1 - w) 1 xra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    (forall m2 k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 2 ->
       XC j0 j192 dt rst syb w cur sym (Znth w rank) k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m2 ->
       evtF bsegs RNG POST (STC 0x96924 m2 (tl + 1 - w) 2 xra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    (forall m2 k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 3 ->
       XC j0 j192 dt rst syb w cur sym (Znth w rank) k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m2 ->
       evtF bsegs RNG POST (STC 0x96fb8 m2 (tl + 1 - w) 4 xra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    (forall m2 k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = 4 ->
       XC j0 j192 dt rst syb w cur sym (Znth w rank) k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m2 ->
       evtF bsegs RNG POST (STC 0x96a3c m2 (tl + 1 - w) 8 xra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    (forall m2 k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word) (len : Z),
       5 <= w -> len = 2^(w - 1) ->
       XC j0 j192 dt rst syb w cur sym (Znth w rank) k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m2 ->
       evtF bsegs RNG POST (STC 0x96ba4 m2 (tl + 1 - w) len xra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STW m1 w xra x5 x6 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW12 HC HS K1 K2 K4 K8 KD. open_xf I. x1_open. x1_lens.
    pose proof (rank_small w ltac:(lia)) as CNTR.
    (* [comment removed for export] *)
    kx_autoFLAc (FR1, FR2) [KAUnp WK 1492; KAApp WK 1492] [0x968fc; 0x970d8] 30%nat
      (KZB2 ++ [KZRange w 1 12; KZRange (Znth w rank) 0 256; KZWord (WK + 4 * w) 4%nat (Znth w rank); KZWr (SPA + 136) 160])
      [(SPA, 136); (SPA + 136, 160); (SPA + 296, 16)] [(WK, 1492); (SPA, 312)].
    all: lazymatch goal with
         | |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 WK rank w RK); lia]]]
         | |- _ => idtac end.
    all: kx_mem; kx_tidy_run.
    (* [comment removed for export] *)
    zstep. rewrite (sllw_pow2 w) by lia.
    zstep.
    assert (ENUM : forall (f g : Z -> Z) (lo0 : Z) (nn : nat), forallb (fun x => f x =? g x) (ZdSeqTable.zseq nn lo0) = true -> forall x, lo0 <= x < lo0 + Z.of_nat nn -> f x = g x).
    { intros f g lo0 nn B x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply ZdSeqBuildThm.zseq_In_iff. lia. }
    lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
      let v := StepF.reg_val 27 in
      lazymatch v with Z_to_bv 64 ?e =>
        let f := eval pattern w in e in
        lazymatch f with ?F w => replace e with (2 ^ (w - 1)) by (symmetry; apply (ENUM F (fun x => 2 ^ (x - 1)) 1 12%nat); [vm_compute; reflexivity | lia]) end end end.
    clear ENUM.
    assert (LENR : 1 <= 2 ^ (w - 1) <= 2048) by (split; [apply Z.pow_le_mono_r with (b := 0) | change 2048 with (2^11); apply Z.pow_le_mono_r]; lia).
    (* [comment removed for export] *)
    kx_autoFLAc (FR1, FR2) (@nil kza) [0x96ef8; 0x96924; 0x96fb8; 0x96a3c; 0x96ba4; 0x970d8] 30%nat
      (KZB2 ++ [KZRange w 1 12; KZRange (2 ^ (w - 1)) 1 2048; KZWr (SPA + 136) 160])
      [(SPA, 136); (SPA + 136, 160)] [(SPA, 312)].
    all: assert (WCASE : (w = 1 /\ 2^(w-1) = 1) \/ (w = 2 /\ 2^(w-1) = 2) \/ (w = 3 /\ 2^(w-1) = 4) \/ (w = 4 /\ 2^(w-1) = 8) \/ (5 <= w /\ 16 <= 2^(w-1)))
      by (destruct (Z.eq_dec w 1) as [->|N1]; [left; split; reflexivity|]; destruct (Z.eq_dec w 2) as [->|N2]; [right; left; split; reflexivity|];
          destruct (Z.eq_dec w 3) as [->|N3]; [right; right; left; split; reflexivity|]; destruct (Z.eq_dec w 4) as [->|N4]; [right; right; right; left; split; reflexivity|];
          right; right; right; right; split; [lia|]; change 16 with (2^4); apply Z.pow_le_mono_r; lia).
    all: kx_mem; kx_tidy_run.
    all: setreg_m 10 (tl + 1 - w).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96ef8) _ _ _ _) => setreg_m 27 1; eapply K1; [lia | close_xc]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96924) _ _ _ _) => setreg_m 27 2; eapply K2; [lia | close_xc]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96fb8) _ _ _ _) => setreg_m 27 4; eapply K4; [lia | close_xc]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96a3c) _ _ _ _) => setreg_m 27 8; eapply K8; [lia | close_xc]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96ba4) _ _ _ _) => first [eapply KD; [lia | reflexivity | close_xc] | exfalso; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (SF 0x968a4 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) x28 x29 x30 x31).
  (* [comment removed for export] *)
  Lemma x1_latchA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt len : Z)
      (k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    XC j0 j192 dt rst syb w cur sym cnt k144 k160 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 m1 ->
    1 <= w <= tl -> 0 <= cnt <= 256 -> 0 <= sym -> sym + cnt <= 256 ->
    0 <= cur -> 1 <= len <= 2048 -> 0 <= cnt * len -> cur + cnt * len <= 4096 ->
    (forall m2 (y5 y6 ya0 ya1 ya2 ya5 ya6 ya7 y28 y29 y30 y31 : word), w + 1 <= tl -> XFm j0 j192 dt rst syb (cur + cnt * len) (sym + cnt) m2 ->
       evtF bsegs RNG POST (STW m2 (w + 1) xra y5 y6 ya0 ya1 ya2 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) y28 y29 y30 y31)) ->
    (forall m2 (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), w = tl -> XFm j0 j192 dt rst syb (cur + cnt * len) (sym + cnt) m2 ->
       evtF bsegs RNG POST (SF 0x970d4 m2 xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 len) y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STL m1 len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW HCNT HS0 HS1 HC0 HLEN HP0 HP1 KH KE. open_xc I. x1_open. x1_lens.
    (* [comment removed for export] *)
    kx_autoFLAc (FR1, FR2) (@nil kza) [0x968b4; 0x970d8] 20%nat
      (KZB2 ++ [KZRange w 1 12; KZRange cnt 0 256; KZRange sym 0 256; KZRange (sym + cnt) 0 256; KZWr (SPA + 136) 160])
      [(SPA, 136); (SPA + 136, 160)] [(SPA, 312)].
    all: kx_mem; kx_tidy_run.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    kx_autoFLAc (FR1, FR2) (@nil kza) [0x968dc; 0x970d4; 0x970d8] 30%nat
      (KZB2 ++ [KZRange w 1 12; KZRange cnt 0 256; KZRange cur 0 4096; KZRange len 1 2048;
                KZRange (cnt * len) 0 4096; KZRange (cur + cnt * len) 0 4096; KZWr (SPA + 136) 160])
      [(SPA, 136); (SPA + 136, 160)] [(SPA, 312)].
    all: kx_mem; kx_tidy_run.
    all: try replace (cnt + sym) with (sym + cnt) in FR2 by lia.
    all: try replace (cnt * len + cur) with (cur + cnt * len) in FR2 by lia.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x968dc) _ _ _ _) => setreg_m 14 (w + 1); eapply KH; [lia | close_xf]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x970d4) _ _ _ _) => eapply KE; [lia | close_xf]
         end.
    all: try (unfold XFR2; do 16 eexists; exact FR2). all: try exact FR4.
  Qed.

  (* [comment removed for export] *)
  Hypothesis KEND : forall m2 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    XFm j0 j192 dt rst syb rsacc sym m2 -> x1pref tl (2^tl) dt ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
                                  xs5 (Z_to_bv 64 r) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                           F (Z_to_bv 64 0x970d8) fc None m2 (seg_rom bsegs)).
  (* [comment removed for export] *)
  Lemma x1_fdoneA : forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XFm j0 j192 dt rst syb rsacc sym m1 -> x1pref tl (2^tl) dt ->
    evtF bsegs RNG POST (SF 0x970d4 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PF. open_xf I. x1_open.
    kx_autoFLAc FR1 (@nil kza) [0x970d8] 10%nat (KZB ++ []) [(SPA, 136)] [(SPA, 312)].
    all: kx_mem; kx_tidy_run.
    eapply KEND; [close_xf| exact PF]. all: try (unfold XFR2; do 16 eexists; exact FR2). all: try exact FR4.
  Qed.
  End FK.
End X1B.
End CANSEC1.
