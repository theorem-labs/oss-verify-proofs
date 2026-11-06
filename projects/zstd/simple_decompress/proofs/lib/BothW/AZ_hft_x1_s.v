(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

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
    assert (RSTA : rng RNG SPA 216) by (lazymatch goal with H : rng RNG lo (SPV - lo) |- _ => eapply rng_sub'; [exact H| lia] end);
    lazymatch goal with H1 : DT + 16388 <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 336 <= SPA <= SPV - 320 |- _ =>
      assert (SDSA : DT + 16388 <= SPA \/ SPA + 216 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - H2 H3 H4; lia) end;
    hide_all_disj; x1_reunp.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5600) (2^47 - 336); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x629000 (2^47 - 16388); KZRange WK 0x629000 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT 16388 SPA 216; KZDisj WK wksz SPA 216; KZDisj DT 16388 WK wksz] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n0 SRC : Z) (flags : word).   (* [comment removed for export] *)
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.

  Section SRT.
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 11 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XBm := (XB m5 SPV SPA lo DT WK wksz FF r hw rank tl).
  Notation ws := (firstn (Z.to_nat nbs) hw).
  (* [comment removed for export] *)
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
  Definition SINV (i : Z) (rst : list Z) : Prop := forall v, 0 <= v <= tl -> Znth v rst = xsym rank v + hcount (firstn (Z.to_nat i) ws) v.
  Lemma ws_len : FseNCount.Zlength ws = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i ws = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.
  Lemma sinv0 : forall rst, (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) -> SINV 0 rst.
  Proof. intros rst H v Hv. rewrite (H v Hv). change (Z.to_nat 0) with 0%nat. rewrite firstn_O. unfold hcount. cbn. lia. Qed.
  Lemma sinv_end : forall i rst, nbs <= i -> SINV i rst -> SINV nbs rst.
  Proof. intros i rst Hi H v Hv. rewrite (H v Hv). rewrite !firstn_firstn. do 2 f_equal. f_equal. lia. Qed.
  (* [comment removed for export] *)
  Lemma sort_unit : forall j rst, 0 <= j < nbs -> SINV j rst -> zlen rst = 13 ->
    0 <= Znth j hw <= tl /\ 0 <= Znth (Znth j hw) rst < nbs /\ SINV (j + 1) (Zupd (Znth j hw) (Znth (Znth j hw) rst + 1) rst).
  Proof.
    intros j rst Hj SI RL. pose proof ws_len as WL.
    destruct (sort_slot ws rank tl STATS j (Znth j hw) ltac:(rewrite WL; lia) (ws_nth j Hj)) as [WR SL].
    rewrite <- (SI (Znth j hw) WR) in SL. rewrite WL in SL.
    split; [exact WR|]. split; [exact SL|].
    intros v Hv. unfold SINV in SI.
    rewrite (sort_step ws rank tl STATS j (Znth j hw) rst ltac:(rewrite WL; lia) (ws_nth j Hj) ltac:(unfold FseNCount.Zlength; lia) SI v Hv). reflexivity.
  Qed.

  Notation KZB2 := (KZB ++ [KZDisj WK wksz FF 64; KZDisj DT 16388 FF 64; KZDisj SPA 216 FF 64; KZRange tl 11 12; KZRange nbs 2 256]) (only parsing).
  Notation NHW := (18446744073709551615 - (WK + 1236)) (only parsing).
  Notation NRS := (18446744073709551615 - (WK + 52)) (only parsing).
  Notation NSY := (18446744073709551615 - (WK + 980)) (only parsing).
  (* [comment removed for export] *)
  Notation STQ pc mm x5 x6 x7 xa0 xa2 xa3 xa4 xa5 x28 x29 x30 x31 :=
    (ST pc mm (Z_to_bv 64 0x97960) x5 x6 x7 xa0 (Z_to_bv 64 (WK + 52)) xa2 xa3 xa4 xa5 (Z_to_bv 64 nbs) (Z_to_bv 64 (WK / 8))
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n0) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation STS mm dtd xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29 :=
    (STQ 0x9812c mm (Z_to_bv 64 (nbs - 4)) x6 x7 xa0 xa2 xa3 xa4 xa5 x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).
  (* [comment removed for export] *)
  Notation STU pc mm n xa2 xa5 x29 x30 x31 :=
    (STQ pc mm (Z_to_bv 64 (nbs - 4)) (Z_to_bv 64 13) (Z_to_bv 64 255) (Z_to_bv 64 NSY) xa2 (Z_to_bv 64 NRS) (Z_to_bv 64 NHW) xa5 (Z_to_bv 64 n) x29 x30 x31).
  (* [comment removed for export] *)
  Notation STT mm n x5 x6 xa2 x28 x30 x31 :=
    (STQ 0x98400 mm x5 x6 (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 NSY) xa2 (Z_to_bv 64 NRS) (Z_to_bv 64 13) (Z_to_bv 64 255) x28 (Z_to_bv 64 n) x30 x31).
  (* [comment removed for export] *)
  Notation STF mm x5 x6 xa0 xa2 xa4 xa5 x28 x29 x30 x31 :=
    (STQ 0x984b4 mm x5 x6 (Z_to_bv 64 (WK + 980)) xa0 xa2 (Z_to_bv 64 NRS) xa4 xa5 x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation XS jA jA2 jC jD jB jE := (XBm (Z_to_bv 64 (WK + 980)) jA jA2 jC jD jB jE).

  (* [comment removed for export] *)
  Local Ltac unit_facts j rst w rs :=
    pose proof (sort_unit j rst ltac:(lia) ltac:(assumption) ltac:(assumption)) as (HWR & HSL & SI');
    set (w := Znth j hw) in *; set (rs := Znth w rst) in *;
    pose proof (Forall_Znth _ hw j BHW ltac:(lia)) as WB; cbv beta in WB; fold w in WB.
  (* [comment removed for export] *)
  Local Ltac unit_post RST RSTLEN RSTNN SYLEN w rs rst syb :=
    kxk_keepg RST; kx_mem; kx_tidy_run;
    repeat match goal with U : Z.of_nat (length (map _ (Zupd _ _ _))) = _ |- _ => clear U end;
    match type of RST with context [Zupd ?i3 _ (Zupd ?i2 _ (Zupd ?i1 _ (Zupd ?i0 _ _)))] =>
      replace i3 with (4 * w + 3) in RST by lia; replace i2 with (4 * w + 2) in RST by lia; replace i1 with (4 * w + 1) in RST by lia; replace i0 with (4 * w) in RST by lia end;
    repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end;
    rewrite (u32b_upd4 rst w (rs + 1)) in RST by lia;
    assert (RSTLEN' : zlen (Zupd w (rs + 1) rst) = 13) by (rewrite Zupd_length2; exact RSTLEN);
    assert (RSTNN' : Forall (fun v : Z => 0 <= v) (Zupd w (rs + 1) rst)) by (apply Forall_Zupd; [exact RSTNN| lia]);
    lazymatch goal with U : length ?kb = length syb |- _ => assert (SYLEN' : zlen kb = 256) by (rewrite U; exact SYLEN) | _ => idtac end.

  (* [comment removed for export] *)
  Lemma x1_su0A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 0) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y30 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 0 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x981c8 m2 n ya2 ya5 (Z_to_bv 64 (WK + n)) y30 x31)) ->
    evtF bsegs RNG POST (STU 0x98154 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI K. open_xb I. x1_open. x1_lens. unit_facts (n + 0) rst w rs.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x981c8; 0x97b24; 0x98ed8] 50%nat
      (KZB2 ++ [KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
               KZWord (WK + 1236 + (n + 0)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u8Z bsegs m1 (WK + 1236) hw (n + 0) HWC); lia]]].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 52) rst w RST); lia]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: unit_post RST RSTLEN RSTNN SYLEN w rs rst syb.
    all: setreg_m 29 (WK + n); eapply K; [close_xb | exact SI'].
  Qed.
  (* [comment removed for export] *)
  Lemma x1_su1A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 1) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x9823c m2 n ya2 ya5 (Z_to_bv 64 (WK + n)) (Z_to_bv 64 (n + 2)) x31)) ->
    evtF bsegs RNG POST (STU 0x981c8 m1 n xa2 xa5 (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI K. open_xb I. x1_open. x1_lens. unit_facts (n + 1) rst w rs.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x9823c; 0x97b24; 0x98ed8] 50%nat
      (KZB2 ++ [KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
               KZWord (WK + 1236 + (n + 1)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u8Z bsegs m1 (WK + 1236) hw (n + 1) HWC); lia]]].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 52) rst w RST); lia]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: unit_post RST RSTLEN RSTNN SYLEN w rs rst syb.
    all: setreg_m 29 (WK + n); setreg_m 30 (n + 2); eapply K; [close_xb | exact SI'].
  Qed.
  (* [comment removed for export] *)
  Lemma x1_su2A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 2) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 2 + 1) rst' ->
       evtF bsegs RNG POST (STU 0x982ac m2 n ya2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) y30 y31)) ->
    evtF bsegs RNG POST (STU 0x9823c m1 n xa2 xa5 (Z_to_bv 64 (WK + n)) (Z_to_bv 64 (n + 2)) x31).
  Proof.
    intros until x31; intros I HN HN3 SI K. open_xb I. x1_open. x1_lens. unit_facts (n + 2) rst w rs.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x982ac; 0x97b24; 0x98ed8] 50%nat
      (KZB2 ++ [KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
               KZWord (WK + 1236 + (n + 2)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u8Z bsegs m1 (WK + 1236) hw (n + 2) HWC); lia]]].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 52) rst w RST); lia]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: unit_post RST RSTLEN RSTNN SYLEN w rs rst syb.
    all: setreg_m 29 (WK + n); setreg_m 15 (n + 3); eapply K; [close_xb | exact SI'].
  Qed.
  (* [comment removed for export] *)
  Lemma x1_su3A : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV (n + 3) rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x98154 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x982ac m1 n xa2 (Z_to_bv 64 (n + 3)) (Z_to_bv 64 (WK + n)) x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI KH KT KE. open_xb I. x1_open. x1_lens. unit_facts (n + 3) rst w rs.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x98154; 0x98400; 0x984b4; 0x97b24; 0x98ed8] 60%nat
      (KZB2 ++ [KZRange n 0 252; KZRange w 0 12; KZRange rs 0 255;
               KZWord (WK + 1236 + (n + 3)) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u8Z bsegs m1 (WK + 1236) hw (n + 3) HWC); lia]]].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 52) rst w RST); lia]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: unit_post RST RSTLEN RSTNN SYLEN w rs rst syb.
    all: replace (n + 3 + 1) with (n + 4) in SI' by lia.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98154) _ _ _ _) => setreg_m 28 (n + 4); eapply KH; [lia | close_xb | exact SI']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98400) _ _ _ _) => setreg_m 29 (n + 4); eapply KT; [lia | lia | close_xb | exact SI']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x984b4) _ _ _ _) => eapply KE; [lia | close_xb | exact SI']
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_su_iterA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (ya2 ya5 y29 y30 y31 : word), n + 4 <= nbs - 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STU 0x98154 m2 (n + 4) ya2 ya5 y29 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), nbs - 4 < n + 4 -> n + 4 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 4) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), nbs <= n + 4 ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 4) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x98154 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    intros until x31; intros I HN HN3 SI KH KT KE.
    eapply x1_su0A; [exact I| exact HN| exact HN3| replace (n + 0) with n by lia; exact SI|]. intros m2 r2 b2 ya2 ya5 y30 I2 S2.
    eapply x1_su1A; [exact I2| exact HN| exact HN3| replace (n + 1) with (n + 0 + 1) by lia; exact S2|]. intros m3 r3 b3 za2 za5 I3 S3.
    eapply x1_su2A; [exact I3| exact HN| exact HN3| replace (n + 2) with (n + 1 + 1) by lia; exact S3|]. intros m4 r4 b4 wa2 w30 w31 I4 S4.
    eapply x1_su3A; [exact I4| exact HN| exact HN3| replace (n + 3) with (n + 2 + 1) by lia; exact S4| exact KH| exact KT| exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_st_bodyA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) x5 x6 xa2 x28 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n < nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya2 y28 y30 y31 : word), n + 1 < nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1) rst' ->
       evtF bsegs RNG POST (STT m2 (n + 1) y5 y6 ya2 y28 y30 y31)) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word), n + 1 = nbs ->
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV (n + 1) rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STT m1 n x5 x6 xa2 x28 x30 x31).
  Proof.
    intros until x31; intros I HN SI KH KE. open_xb I. x1_open. x1_lens. unit_facts n rst w rs.
    kx_autoFLAc FR [KAUnp WK 1492; KAApp WK 1492] [0x98400; 0x984b4; 0x97b24; 0x98ed8] 50%nat
      (KZB2 ++ [KZRange n 0 255; KZRange w 0 12; KZRange rs 0 255;
               KZWord (WK + 1236 + n) 1%nat w; KZWord (WK + 52 + 4 * w) 4%nat rs; KZWr (WK + 52) 52; KZWr (WK + 980) 256])
      [(SPA, 216)] [(WK, 1492); (SPA, 216)].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u8Z bsegs m1 (WK + 1236) hw n HWC); lia]]].
    1: split; [lia| split; [lia| split; [lia| apply (rdn_u32b bsegs m1 (WK + 52) rst w RST); lia]]].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: unit_post RST RSTLEN RSTNN SYLEN w rs rst syb.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98400) _ _ _ _) => setreg_m 29 (n + 1); eapply KH; [lia | close_xb | exact SI']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x984b4) _ _ _ _) => eapply KE; [lia | close_xb | exact SI']
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_st_loopA : forall (f : nat) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) x5 x6 xa2 x28 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + Z.of_nat (S f) = nbs -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV nbs rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STT m1 n x5 x6 xa2 x28 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HN HF SI KE.
    - eapply (x1_st_bodyA m1 dt rst syb jA jA2 jC jD jB jE n); [exact I| lia| exact SI| intros; exfalso; lia|].
      intros m2 rst' syb' y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 Hn I2 S2. eapply KE; [exact I2| eapply sinv_end; [| exact S2]; lia].
    - eapply (x1_st_bodyA m1 dt rst syb jA jA2 jC jD jB jE n); [exact I| lia| exact SI| | intros; exfalso; lia].
      intros m2 rst' syb' y5 y6 ya2 y28 y30 y31 Hn I2 S2.
      eapply (IH m2 dt rst' syb' jA jA2 jC jD jB jE (n + 1)); [exact I2| lia| lia| exact S2| exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_su_loopA : forall (f : nat) m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (n : Z) xa2 xa5 x29 x30 x31,
    XS jA jA2 jC jD jB jE dt rst syb m1 -> 0 <= n -> n + 3 < nbs -> nbs - n <= 4 * Z.of_nat f -> SINV n rst ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 -> SINV nbs rst' ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STU 0x98154 m1 n xa2 xa5 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HN HN3 HF SI KE; [exfalso; lia|].
    eapply x1_su_iterA; [exact I| exact HN| exact HN3| exact SI| | |].
    - intros m2 rst' syb' ya2 ya5 y29 y30 y31 Hn I2 S2.
      eapply (IH m2 dt rst' syb' jA jA2 jC jD jB jE (n + 4)); [exact I2| lia| lia| lia| exact S2| exact KE].
    - intros m2 rst' syb' y5 y6 ya2 y28 y30 y31 Hn1 Hn2 I2 S2.
      eapply (x1_st_loopA (Z.to_nat (nbs - (n + 4) - 1)) m2 dt rst' syb' jA jA2 jC jD jB jE (n + 4)); [exact I2| lia| lia| exact S2|].
      intros m3 rst3 syb3 z5 z6 za0 za2 za4 za5 z28 z29 z30 z31 I3 S3. eapply KE; [exact I3| exact S3].
    - intros m2 rst' syb' y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 Hn I2 S2. eapply KE; [exact I2| eapply sinv_end; [exact Hn| exact S2]].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_sortA : forall m1 (dt rst : list Z) (syb jA jA2 jC jD jB jE : list byte) (k176 : word) (dtd : Z) xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29,
    XBm k176 jA jA2 jC jD jB jE dt rst syb m1 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
    (forall m2 (rst' : list Z) (syb' : list byte) (y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31 : word),
       XS jA jA2 jC jD jB jE dt rst' syb' m2 ->
       evtF bsegs RNG POST (STF m2 y5 y6 ya0 ya2 ya4 ya5 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STS m1 dtd xa0 xa2 xa3 xa4 xa5 x6 x7 x28 x29).
  Proof.
    intros until x29; intros I RS0 KE. pose proof (sinv0 rst RS0) as SI. open_xb I. x1_open. x1_lens.
    kx_autoFLAc FR (@nil kza) [0x98154; 0x98400; 0x984b4; 0x97b24; 0x98ed8] 30%nat
      (KZB2 ++ [KZWr (SPA + 176) 8]) [(SPA, 216)] [(SPA, 216)].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ed8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem; kx_tidy_run.
    all: setreg_m 10 (18446744073709551615 - (WK + 980)); setreg_m 13 (18446744073709551615 - (WK + 52)); try setreg_m 14 (18446744073709551615 - (WK + 1236)).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98154) _ _ _ _) =>
             eapply (x1_su_loopA (Z.to_nat nbs) _ dt rst syb jA jA2 jC jD jB jE 0); [close_xb| lia| lia| lia| exact SI|];
             intros; eapply KE; eassumption
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98400) _ _ _ _) =>
             eapply (x1_st_loopA (Z.to_nat (nbs - 1)) _ dt rst syb jA jA2 jC jD jB jE 0); [close_xb| lia| lia| exact SI|];
             intros; eapply KE; eassumption
         end.
  Qed.
  End SRT.
End X1B.
End CANSEC1.
