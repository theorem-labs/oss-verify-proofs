(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseRdKit FseRdKit2 ZdCellKit ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AZ_hft_rstats_a AZ_hft_fdec_epi.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition AGOT_SUAR_D : Z := 0xcb9f8.    (* [comment removed for export] *)
Definition AGOT_SHB_D : Z := 0xcb9a0.     (* [comment removed for export] *)
Definition AGOT_FDPC : Z := 0xcc620.      (* [comment removed for export] *)

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SPV SPB lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 5024.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis ESPB : (SPV + -256) - (SPV + -256) mod 2^5 = SPB.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  Lemma spb_props : SPV - 272 <= SPB <= SPV - 256 /\ SPB mod 32 = 0.
  Proof. clear - SP16 ESPB. change (2^5) with 32 in ESPB. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition FDFR0 (jA : list byte) (dstw : word) (jB : list byte) : list cell := [CB 48 jA; C8 dstw; CB 96 jB].

  (* [comment removed for export] *)
  Lemma fd_pro : forall (t0 t1 t2 a7 t3 t4 t5 t6 : word) m (DST cap SRC n ml WK wksz : Z),
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_D [C8 (Z_to_bv 64 0xd4300)] -> rw_cells bsegs m 0xd4300 [C4 (Z_to_bv 64 1)] ->
    0 <= DST < 2^64 -> 0 <= cap < 2^64 -> 0 <= SRC < 2^64 -> 0 <= n < 2^64 -> 0 <= ml < 2^64 -> 0 <= WK < 2^64 -> 0 <= wksz < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0xafa18) (Z_to_bv 64 SPB) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xd42f8) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 ml) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) a7
                     s2 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 cap) (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) (Z_to_bv 64 SRC) (Z_to_bv 64 ml)
                     s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x3ef30) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 272, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ rw_cells bsegs m' SPB (FDFR0 jA (Z_to_bv 64 DST) jB)
        /\ stk bsegs m' lo SPB /\ stk bsegs m' (SPB + 152) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 cap) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 ml)
               (Z_to_bv 64 WK) (Z_to_bv 64 wksz) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xaf990) fc None m (seg_rom bsegs)).
  Proof.
    intros until wksz. intros ST MI GOT SHB GSU SUA RD RC RS RN RM RW RZ. unfold AGOT_SUAR_D in *.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof spb_props as (SPBB & SPB32).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 272, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 152%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPB.
    (* [comment removed for export] *)
    release_frame FR0 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (SPB + 152) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPB + 152) 152 ST1 ltac:(cbn; lia)) as [STL [jX FRA]]. clear ST1.
    change (Z.of_nat 152) with 152 in STL, FRA. replace (SPB + 152 - 152) with SPB in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 152 jX [] [48; 8; 96]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0] _ _ FRA) as [wd FR1]; cbn [app] in FR1; clear FRA; rename FR1 into FRA end.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [unfold FDFR0; eassumption|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Definition FDHDR (FF FLG : Z) (j24 : list byte) (tlw : word) (j36 j52 : list byte) : list cell :=
    [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d980); C8 (Z_to_bv 64 0xaf990); CB 8 j24; C4 tlw; CB 12 j36; C4 (Z_to_bv 64 255); CB 4 j52; C8 (Z_to_bv 64 FLG)].
  (* [comment removed for export] *)
  Definition FDFRAME (jA : list byte) (w24 w32 w40 dstw sbw : word) (j64 : list byte) (FF : Z) (j80 j96 j112 : list byte) : list cell :=
    [CB 24 jA; C8 w24; C8 w32; C8 w40; C8 dstw; C8 sbw; CB 8 j64; C8 (Z_to_bv 64 FF); CB 16 j80; CB 16 j96; CB 40 j112].

  (* [comment removed for export] *)
  Lemma fd_hdr : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 : word) m (FF FLG DST cap ml n SRC WK wksz : Z)
      (j0 j1 j2 : word) (junk : list byte) (jA jB : list byte),
    rw_cells bsegs m SPB (FDFR0 jA (Z_to_bv 64 DST) jB) ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m AGOT_FDPC [C8 (Z_to_bv 64 0xaf990)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    0 <= wksz < 2^32 -> 0 <= DST < 2^64 -> 4096 <= WK -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
    evtF bsegs RNG (fun ms' => exists m' jA' (w24 w32 w40 : word) j64 j80 j96 j112 j24 tlw j36 j52,
        munch [(SPB, SPB + 80); (FF, FF + 24); (FF + 48, FF + 52); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' /\
        wmono bsegs m m' /\ mem_inv bsegs m' /\
        rw_cells bsegs m' FF (FDHDR FF FLG j24 tlw j36 j52) /\ rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) FDSH /\
        ( (512 <= wksz /\
              w32 = Z_to_bv 64 FF /\ w40 = Z_to_bv 64 FF /\
              rw_cells bsegs m' SPB (FDFRAME jA' w24 w32 w40 (Z_to_bv 64 DST) (Z_to_bv 64 2147450880) j64 FF j80 j96 j112) /\
              ms' = MS (mkR (Z_to_bv 64 0xafb30) (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
                           (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 FF) x17
                           (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (WK + 512)) (Z_to_bv 64 cap) (Z_to_bv 64 n) (Z_to_bv 64 WK)
                           (Z_to_bv 64 wksz) (Z_to_bv 64 SRC) (Z_to_bv 64 ml) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
                       F (Z_to_bv 64 0xae224) fc None m' (seg_rom bsegs))
          \/ (wksz < 512 /\
              rw_cells bsegs m' SPB (FDFRAME jA' w24 w32 w40 (Z_to_bv 64 DST) (Z_to_bv 64 2147450880) j64 FF j80 j96 j112) /\
              exists (y11 y12 y13 y14 y15 y17 y20 y21 y22 y23 y24 y25 y26 y27 : word),
              ms' = MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
                           (Z_to_bv 64 18446744073709551615) y11 y12 y13 y14 y15 (Z_to_bv 64 FF) y17
                           (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) y20 y21 y22 y23 y24 y25 y26 y27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0xafb50) fc None m' (seg_rom bsegs)) ))
      (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 2147450880) (Z_to_bv 64 cap) (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) (Z_to_bv 64 SRC) (Z_to_bv 64 ml)
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xafa18) fc None m (seg_rom bsegs)).
  Proof.
    intros until jB. intros FRA FFC SHF GPC MI FH FC F64 RF RSF WKSZ RD WKL WKH WKA.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AGOT_FDPC in *. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spb_props as (SPBB & SPB32).
    apply shadow8_c1sA in SHF. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.   (* [comment removed for export] *)
    pose proof (munch_refl [(SPB, SPB + 80); (FF, FF + 24); (FF + 48, FF + 52); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    unfold FDFR0 in FRA.
    apply (rw_cells_split_CB bsegs _ _ [] 48 jA _ [24; 8; 8; 8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; CB 96 ?j] => apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4] 96 j [] [8; 8; 8; 16; 16; 40]%nat) in FRA; [| reflexivity] end.
    cbn [mk_CB_cells app] in FRA.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0] _ _ FRA) as [w24 FR1]; cbn [app] in FR1; clear FRA end.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0; c1] _ _ FR1) as [w32 FR2]; cbn [app] in FR2; clear FR1 end.
    lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0; c1; c2] _ _ FR2) as [w40 FR3]; cbn [app] in FR3; clear FR2 end.
    lazymatch type of FR3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0; c1; c2; c3; c4] _ _ FR3) as [w56 FR4]; cbn [app] in FR4; clear FR3 end.
    lazymatch type of FR4 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: _) => destruct (cb8_as_c8 bsegs _ _ [c0; c1; c2; c3; c4; c5; c6] _ _ FR4) as [w72 FRA]; cbn [app] in FRA; clear FR4 end.
    (* [comment removed for export] *)
    lazymatch type of FFC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 32 ?j :: ?post) =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2] 32 j post [8; 4; 12; 4; 4]%nat) in FFC; [| reflexivity] end.
    cbn [mk_CB_cells app] in FFC.
    lazymatch type of FFC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 4 ?j :: ?post) => destruct (hcb4_as_c4 bsegs _ _ [c0; c1; c2; c3] j post FFC) as [tlw FF1]; cbn [app] in FF1; clear FFC end.
    lazymatch type of FF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 4 ?j :: ?post) => destruct (hcb4_as_c4 bsegs _ _ [c0; c1; c2; c3; c4; c5] j post FF1) as [mw FFC]; cbn [app] in FFC; clear FF1 end.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-513)) with (Z_to_bv 64 18446744073709551103) by (apply Z_to_bv_eqm; reflexivity).
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. if_cases G; zify_cond G; [ clear G | exfalso; clear - G WKH WKSZ WKL; lia ].
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. if_cases G; zify_cond G; [ clear G | ug_dead G ].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K1.                              (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. if_cases G; zify_cond G; [ clear G | exfalso; clear - G WKL; lia ].   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      assert (E1 : Z.land WK 1 = WK mod 2) by (change 1 with (Z.ones 1) at 1; rewrite Z.land_ones by lia; reflexivity).
      zstep. if_cases G; zify_cond G; [ clear G E1 | exfalso; rewrite E1 in G; clear - G WKA; Z.div_mod_to_equations; lia ].   (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      apply evtF_done. do 13 eexists.
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [rewrite ?unsigned_lit in K1 by lia; lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [eassumption| reflexivity].
    - (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      apply evtF_done. do 13 eexists.
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. split; [rewrite ?unsigned_lit in K1 by lia; lia|]. split; [eassumption|]. do 14 eexists. reflexivity.
  Qed.
End S.
End CANSEC1.
