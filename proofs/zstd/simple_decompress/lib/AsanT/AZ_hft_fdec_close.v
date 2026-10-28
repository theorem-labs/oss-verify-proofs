(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_fkit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_rstats_a AZ_hft_fdec_defs AZ_hft_fdec_epi.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
(* [comment removed for export] *)
Notation FD_MUNCH DST cap WK wksz SPV L := ([(DST, DST + cap); (WK, WK + wksz); (SPV - 4992, SPV)] ++ fake_area L) (only parsing).
Notation FD_WL DST cap WK wksz := [(DST, DST + cap); (WK, WK + wksz)] (only parsing).

(* [comment removed for export] *)
Definition fdA_fr (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m mA : amem) (SPV DST cap WK wksz FF FLG : Z) (j0 : word) : Prop :=
  rw_cells bsegs mA (Z.shiftr FF 3 + 2147450880) FDSH
  /\ rw_cells bsegs mA FF [C8 j0]
  /\ rw_cells bsegs mA (FF + 56) [C8 (Z_to_bv 64 FLG)]
  /\ rw_cells bsegs mA (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) mA
  /\ munch (FD_MUNCH DST cap WK wksz SPV L) m mA /\ wmono bsegs m mA
  /\ ffr_pres (FD_WL DST cap WK wksz) LB m mA.

(* [comment removed for export] *)
Definition fd_qexit (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mA : amem) (SPV SPB lo DST cap FF : Z) : machine_state -> Prop :=
  fun ms' => (exists mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EXB mA SPV SPB lo DST cap mx /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= cap) /\
    ms' = MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 x17
                    (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0xac208) fc None mx (seg_rom bsegs))
  \/ (exists mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EXB mA SPV SPB lo DST cap mx /\ 0 <= r < 2^64 /\ (zd_is_error r = true \/ r <= cap) /\
    ms' = MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 (Z_to_bv 64 FF)
                    (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0xac20c) fc None mx (seg_rom bsegs)).

Lemma fd_qx : forall gp tp F fc mA SPV SPB lo DST cap FF, fd_exitK (fd_qexit gp tp F fc mA SPV SPB lo DST cap FF) gp tp F fc mA SPV SPB lo DST cap FF.
Proof. intros. unfold fd_exitK. intros. unfold fd_qexit. left. do 26 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. reflexivity. Qed.
Lemma fd_qxc : forall gp tp F fc mA SPV SPB lo DST cap FF, fd_exitKc (fd_qexit gp tp F fc mA SPV SPB lo DST cap FF) gp tp F fc mA SPV SPB lo DST cap FF.
Proof. intros. unfold fd_exitKc. intros. unfold fd_qexit. right. do 25 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. reflexivity. Qed.

Lemma fd_ffr_pres_mono_nil : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.
Lemma fd_ainblk_cons : forall b LB X n, ainblk LB X n -> ainblk (b :: LB) X n.
Proof. intros b LB X n (b' & Hb & H1 & H2). exists b'. split; [right; exact Hb| split; [exact H1| exact H2]]. Qed.
Lemma fd_ffr_pres_tail : forall W b LB (m m' : amem), ffr_pres W (b :: LB) m m' -> ffr_pres W LB m m'.
Proof.
  intros W b LB m m' H a Ha HP. apply (H a Ha).
  destruct HP as [[(c & A & n & Hin & Hr) HO]|(a' & (c & A & n & Hin & Hr) & E)].
  - left. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact HO].
  - right. exists a'. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact E].
Qed.

(* [comment removed for export] *)
Section CG.
  Variables (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z).
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Variables (SPV SPB lo DST cap WK wksz FF : Z) (j0 : word).
  Hypothesis LBH : ablkLB LB.
  Hypothesis INDST : ainblk LB DST cap.
  Hypothesis INWK : ainblk LB WK wksz.
  Hypothesis FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF.
  Hypothesis FFA1 : al_fake L <= FF.
  Hypothesis FFA2 : FF + 64 <= al_fake L + FAKESZ.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypotheses (SPA : SPV mod 16 = 0) (LO0 : 4096 <= lo) (LOS : lo <= SPV - 4992) (BOT : ATOP + 4096 <= lo) (KLO : KHIGH <= lo)
             (SPB0 : SPV - 240 <= SPB) (SPB1 : SPB <= SPV - 224)
             (F64 : FF mod 64 = 0) (FFH : ablk FF (FF + 64)) (FFT : FF + 64 <= ATOP) (RFF : rng RNG FF 64) (RSFF : rng RNG (shad FF) 8)
             (RSTK : rng RNG lo (SPV - lo)) (RI : rng_aimg RNG)
             (CAP0 : 0 <= cap) (DSTH : DST + cap < 2^47) (WKSZ0 : 0 <= wksz) (WKH : WK + wksz < 2^47).
  Notation POST := (fse_dec_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).

  Lemma fd_exit_gen : forall mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FDSH -> rw_cells bsegs mx FF [C8 j0] -> rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
    rw_cells bsegs mx (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> stk bsegs mx lo (SPV + -104) -> mem_inv bsegs mx ->
    stk bsegs mx DST (DST + cap) -> stk bsegs mx WK (WK + wksz) ->
    munch (FD_MUNCH DST cap WK wksz SPV L) m mx -> wmono bsegs m mx -> ffr_pres (FD_WL DST cap WK wksz) LB m mx -> AHEAP AI L RNG st (FB0 FF :: LB) mx ->
    0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 (Z_to_bv 64 FF)
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xac20c) fc None mx (seg_rom bsegs)).
  Proof.
    intros until x31. intros SHFx FF0x FF56x FRBx STG MI STD WKS MUx WMx FFRx AHx RR RES.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof (AI_layout AI _ _ _ _ _ AHx) as (LY1 & LY2 & LY3 & LY4 & _).
    pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
    pose proof (ablk_lin _ _ FFH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    destruct (FFLAG _ _ _ _ _ _ _ _ AHx ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI & GFA).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FHa FHb FHc FHd ATR; Z.div_mod_to_equations; lia).
    unfold KHIGH in KLO.
    assert (LOC : ATOP <= lo) by (clear - BOT; lia).
    pose proof (fd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV SPB lo SPA LOS LOC RNG RSTK) as EPI0.
    pose proof (EPI0 x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mx FF (fflag L 0 FF) r j0) as EPI. clear EPI0.
    specialize (EPI SHFx FF0x FF56x FLC FRBx STG MI FFH FFT F64 GH GC GF RFF RSFF RG RR).
    eapply evtF_cut; [exact EPI|]. clear EPI.
    cbv beta. intros ms' (mp & m5 & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
    assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
    { eapply (AI_frame AI); [exact AHx| exact MU1| exact WM1|].
      constructor; [| constructor; [| constructor]]; cbn.
      - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
        rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. unfold ASHOFF. clear - F64 FHa FHd. Z.div_mod_to_equations. lia.
      - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; clear; lia]. }
    assert (AH5 : AHEAP AI L RNG st LB m5).
    { eapply (fk_release AI fflag); [exact FREL| exact AHp| clear - GHa GHb GHc GHd; lia| clear - GHa GHb GHc GHd ATR; lia| clear - GHa; lia| exact MU2| exact FLC5]. }
    assert (TC : forall X k, ainblk LB X k -> 0 <= k -> X + k <= 2^47 ->
              disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] X k
              /\ disjoint_from [(fflag L 0 FF, fflag L 0 FF + 1)] X k).
    { intros X k (b & Hb & Hb1 & Hb2) Hk HH.
      pose proof (FFD b Hb) as D1. pose proof (GBL b ltac:(right; exact Hb)) as D2. pose proof (ablk_disj_band _ _ (LBH b Hb)) as D3.
      unfold KLS in D3. cbn [disjoint_from]. clear - Hb1 Hb2 Hk HH D1 D2 D3 BSF. repeat split; lia. }
    destruct (TC DST cap INDST CAP0 ltac:(clear - DSTH; lia)) as [DD1 DD2].
    destruct (TC WK wksz INWK WKSZ0 ltac:(clear - WKH; lia)) as [DW1 DW2].
    apply evtF_done. unfold fse_dec_postA. do 14 eexists. exists m5, r.
    split; [reflexivity|].
    split.
    { eapply munch_trans; [exact MUx|]. eapply munch_trans.
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app fake_area] in *.
        rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by (clear; lia). change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
        clear - Hx FFA1 FFA2 F64. Z.div_mod_to_equations. lia.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. unfold FAKESZ in *. clear - Hx GFA. lia. }
    split; [eapply wmono_trans; [exact WMx| eapply wmono_trans; [exact WM1| exact WM2]]|].
    split; [exact MI5|]. split; [exact ST5|].
    split.
    { eapply ffr_pres_trans; [exact FFRx|]. apply fd_ffr_pres_mono_nil.
      eapply (fk_ffr_fin AI L RNG st LB mx mx m5 0 FF 64 (shad FF) 8 [] [(FF, FF + 8); (fflag L 0 FF, fflag L 0 FF + 1)]);
        [exact AHx| exact LBH| exact FFH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| clear; lia| clear; lia| | constructor| apply ffr_pres_refl| |
         eapply wmono_trans; [exact WM1| exact WM2]].
      - constructor; [cbn; split; [clear; lia| right; split; [intros b Hb; destruct (FFD b Hb); [left|right]; clear - H; lia| exists FF, (FF + 64); split; [exact FFH| clear; lia]]]|].
        constructor; [cbn; split; [clear; lia| right; split; [intros b Hb; exact (GBL b ltac:(right; exact Hb))| exists (fflag L 0 FF), (fflag L 0 FF + 1); split; [exact GH| clear; lia]]]| constructor].
      - eapply munch_trans.
        + eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
          rewrite ?Z.shiftr_div_pow2 in * by (clear; lia). change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia.
        + eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    split; [exact AH5|].
    split.
    { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact STD| exact MU1| exact WM1| replace (DST + cap - DST) with cap by (clear; lia); exact DD1]
                                     | exact MU2| exact WM2| replace (DST + cap - DST) with cap by (clear; lia); exact DD2]. }
    split.
    { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact WKS| exact MU1| exact WM1| replace (WK + wksz - WK) with wksz by (clear; lia); exact DW1]
                                     | exact MU2| exact WM2| replace (WK + wksz - WK) with wksz by (clear; lia); exact DW2]. }
    split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_exit_gen38 : forall mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mx (SPB + 24) [C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FDSH -> rw_cells bsegs mx FF [C8 j0] -> rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
    rw_cells bsegs mx (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> stk bsegs mx lo (SPV + -104) -> mem_inv bsegs mx ->
    stk bsegs mx DST (DST + cap) -> stk bsegs mx WK (WK + wksz) ->
    munch (FD_MUNCH DST cap WK wksz SPV L) m mx -> wmono bsegs m mx -> ffr_pres (FD_WL DST cap WK wksz) LB m mx -> AHEAP AI L RNG st (FB0 FF :: LB) mx ->
    0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xac208) fc None mx (seg_rom bsegs)).
  Proof.
    intros until x31. intros FA32 SHFx FF0x FF56x FRBx STG MI STD WKS MUx WMx FFRx AHx RR RES.
    pose proof (ablk_lin _ _ FFH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. unfold KHIGH in KLO.
    zstep.
    eapply fd_exit_gen; eassumption.
  Qed.
  Lemma fd_exit_gen3c : forall mx r (x1 x2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells bsegs mx (SPB + 24) [C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FDSH -> rw_cells bsegs mx FF [C8 j0] -> rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
    rw_cells bsegs mx (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> stk bsegs mx lo (SPV + -104) -> mem_inv bsegs mx ->
    stk bsegs mx DST (DST + cap) -> stk bsegs mx WK (WK + wksz) ->
    munch (FD_MUNCH DST cap WK wksz SPV L) m mx -> wmono bsegs m mx -> ffr_pres (FD_WL DST cap WK wksz) LB m mx -> AHEAP AI L RNG st (FB0 FF :: LB) mx ->
    0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xac204) fc None mx (seg_rom bsegs)).
  Proof.
    intros until x31. intros FA32 SHFx FF0x FF56x FRBx STG MI STD WKS MUx WMx FFRx AHx RR RES.
    pose proof (ablk_lin _ _ FFH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. unfold KHIGH in KLO.
    zstep. zstep.
    eapply fd_exit_gen; eassumption.
  Qed.
End CG.

Section CL.
  Variables (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Variables (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte) (j0 : word).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FR : fdA_fr AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mA SPV DST cap WK wksz FF (fflag L 0 FF) j0.
  Hypothesis LBH : ablkLB LB.
  Hypothesis INDST : ainblk LB DST cap.
  Hypothesis INWK : ainblk LB WK wksz.
  Hypothesis FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF.
  Hypothesis FFA1 : al_fake L <= FF.
  Hypothesis FFA2 : FF + 64 <= al_fake L + FAKESZ.
  Hypothesis SPT : SPV + 16 < al_top L.
  Notation POST := (fse_dec_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation QEXIT := (fd_qexit gp tp F fc mA SPV SPB lo DST cap FF).

  (* [comment removed for export] *)
  Lemma fd_post_facts : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx ->
    munch (FD_MUNCH DST cap WK wksz SPV L) m mx /\ wmono bsegs m mx /\ ffr_pres (FD_WL DST cap WK wksz) LB m mx /\ AHEAP AI L RNG st (FB0 FF :: LB) mx.
  Proof.
    intros mx MU WM. open_hy HY. destruct FR as (_ & _ & _ & _ & AHj & MU0 & WM0 & FFR0).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof (AI_layout AI _ _ _ _ _ AHj) as (LY1 & LY2 & LY3 & LY4 & _).
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx SPB0 SPB1. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|].
    split.
    { eapply ffr_pres_trans; [exact FFR0|].
      apply (fd_ffr_pres_tail _ (FB0 FF)).
      eapply (ffr_pres_appw AI L RNG st (FB0 FF :: LB) mA mx (FD_WL DST cap WK wksz) [(DST, DST + cap)] [(SPB - 2224, SPB); (SPB + 48, SPB + 120)]);
        [exact AHj| | | | exact MU| exact WM].
      - intros b [<-|Hb]; [exact FFH| exact (LBH b Hb)].
      - constructor; [cbn [fst snd]; clear - LOS BOT SPB0 SPB1 SPT LY3; unfold KEND in *; lia|].
        constructor; [cbn [fst snd]; clear - LOS BOT SPB0 SPB1 SPT LY3; unfold KEND in *; lia| constructor].
      - destruct (fk_inblk_ablk LB DST cap LBH INDST CAP0) as (A1 & N1 & AB1 & L1 & H1).
        constructor; [cbn [fst snd]; split; [exists A1, N1; split; [exact AB1| clear - L1 H1; lia]| split; [clear - CAP0; lia| left; reflexivity]]| constructor]. }
    eapply (AI_frame AI); [exact AHj| exact MU| exact WM|].
    constructor; [cbn [fst snd]; replace (DST + cap - DST) with cap by (clear; lia); apply (fk_acr_inblk AI); apply fd_ainblk_cons; exact INDST|].
    constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LOS SPB0 SPB1 SPR; lia|].
    constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LOS SPB0 SPB1 SPR; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_close2 : forall mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EXB mA SPV SPB lo DST cap mx -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 (Z_to_bv 64 FF)
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xac20c) fc None mx (seg_rom bsegs)).
  Proof.
    intros until x31. intros EX RR RES. pose proof HY as HY'. open_hy HY'. fd_atP HY AN.
    destruct EX as (MU & WM & MI & STL & STD & cs & CS & CSZ).
    destruct FR as (SHFj & FF0j & FF56j & FRBj & AHj & MU0 & WM0 & FFR0).
    destruct (fd_post_facts mx MU WM) as (MUx & WMx & FFRx & AHx).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof (AI_layout AI _ _ _ _ _ AHj) as (LY1 & LY2 & LY3 & LY4 & _).
    pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
    pose proof (ablk_lin _ _ FFH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    destruct (FFLAG _ _ _ _ _ _ _ _ AHx ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI & GFA).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FHa FHb FHc FHd ATR; Z.div_mod_to_equations; lia).
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    unfold KHIGH in KLO.
    (* [comment removed for export] *)
    assert (SHFx : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) FDSH)
      by (eapply rw_cells_transport; [exact SHFj| exact MU| exact WM| cbn; clear - BSF DSTB KLO LOS SPB0 CAP0; lia]).
    assert (FF0x : rw_cells bsegs mx FF [C8 j0])
      by (eapply rw_cells_transport; [exact FF0j| exact MU| exact WM| cbn; clear - FFDST FHc BOT LOS SPB0 CAP0; lia]).
    assert (FF56x : rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))])
      by (eapply rw_cells_transport; [exact FF56j| exact MU| exact WM| cbn; clear - FFDST FHc BOT LOS SPB0 CAP0; lia]).
    assert (FRBx : rw_cells bsegs mx (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact FRBj| exact MU| exact WM| cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; lia]).
    (* [comment removed for export] *)
    pose proof (fd_sk0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK0. pose proof (fd_sk1M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK1.
    pose proof (fd_sk2M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK2.
    pose proof (fd_faM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as FA. pose proof (fd_fbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as FB.
    apply stk_of_rw_cells in FB. apply stk_of_rw_cells in CS. rewrite CSZ in CS.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FB, CS.
    apply stk_of_rw_cells in FA. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA.
    assert (STG : stk bsegs mx lo (SPV + -104)).
    { apply (stk_merge bsegs mx lo SPB (SPV + -104) STL); [| clear - SPB0 SPB1 LOS LO0; lia].
      apply (stk_merge bsegs mx SPB (SPB + 8) _ SK0); [| clear - SPB1; lia].
      apply (stk_merge bsegs mx (SPB + 8) (SPB + 8 + 24) _ FA); [| clear - SPB1; lia].
      replace (SPB + 8 + 24) with (SPB + 32) by (clear; lia).
      apply (stk_merge bsegs mx (SPB + 32) (SPB + 40) _ SK1); [| clear - SPB1; lia].
      apply (stk_merge bsegs mx (SPB + 40) (SPB + 40 + 8) _ FB); [| clear - SPB1; lia].
      replace (SPB + 40 + 8) with (SPB + 48) by (clear; lia).
      apply (stk_merge bsegs mx (SPB + 48) (SPB + 48 + 72) _ CS); [| clear - SPB1; lia].
      replace (SPB + 48 + 72) with (SPB + 120) by (clear; lia). exact SK2. }
    assert (LOC : ATOP <= lo) by (clear - BOT; lia).
    (* [comment removed for export] *)
    pose proof (fd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV SPB lo SPA LOS LOC RNG RSTK) as EPI0.
    pose proof (EPI0 x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mx FF (fflag L 0 FF) r j0) as EPI. clear EPI0.
    specialize (EPI SHFx FF0x FF56x FLC FRBx STG MI FFH FFT F64 GH GC GF RFF RSFF RG RR).
    eapply evtF_cut; [exact EPI|]. clear EPI.
    cbv beta. intros ms' (mp & m5 & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
    assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
    { eapply (AI_frame AI); [exact AHx| exact MU1| exact WM1|].
      constructor; [| constructor; [| constructor]]; cbn.
      - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
        rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. unfold ASHOFF. clear - F64 FHa FHd. Z.div_mod_to_equations. lia.
      - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; clear; lia]. }
    assert (AH5 : AHEAP AI L RNG st LB m5).
    { eapply (fk_release AI fflag); [exact FREL| exact AHp| clear - GHa GHb GHc GHd; lia| clear - GHa GHb GHc GHd ATR; lia| clear - GHa; lia| exact MU2| exact FLC5]. }
    (* [comment removed for export] *)
    assert (TC : forall X k, ainblk LB X k -> 0 <= k -> X + k <= 2^47 ->
              disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] X k
              /\ disjoint_from [(fflag L 0 FF, fflag L 0 FF + 1)] X k).
    { intros X k (b & Hb & Hb1 & Hb2) Hk HH.
      pose proof (FFD b Hb) as D1. pose proof (GBL b ltac:(right; exact Hb)) as D2. pose proof (ablk_disj_band _ _ (LBH b Hb)) as D3.
      unfold KLS in D3. cbn [disjoint_from]. clear - Hb1 Hb2 Hk HH D1 D2 D3 BSF. repeat split; lia. }
    destruct (TC DST cap INDST CAP0 ltac:(clear - DSTH; lia)) as [DD1 DD2].
    destruct (TC WK wksz INWK WKSZ0 ltac:(clear - WKH; lia)) as [DW1 DW2].
    (* [comment removed for export] *)
    assert (WKS : stk bsegs mx WK (WK + wksz)).
    { pose proof (fd_wkloM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as W1.
      pose proof (fd_dthM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as W2. apply stk_of_rw_cells in W2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W2.
      pose proof (fd_tbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as W3. apply rw_cells_of_u8arr in W3. apply stk_of_rw_cells in W3.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W3. rewrite length_map, Nat.add_0_r in W3.
      lazymatch type of W3 with stk _ _ _ ?e => replace e with (DT + 4 + 4 * 2^tl) in W3 by (clear - TBL; lia) end.
      pose proof (fd_wsM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as W4.
      apply (stk_merge bsegs mx WK DT _ W1); [| clear - DTE ROOM P2; lia].
      apply (stk_merge bsegs mx DT (DT + 4) _ W2); [| clear - DTE ROOM P2; lia].
      apply (stk_merge bsegs mx (DT + 4) (DT + 4 + 4 * 2^tl) _ W3); [exact W4 | clear - DTE ROOM P2; lia]. }
    apply evtF_done. unfold fse_dec_postA. do 14 eexists. exists m5, r.
    split; [reflexivity|].
    split.
    { eapply munch_trans; [exact MUx|]. eapply munch_trans.
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app fake_area] in *.
        rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by (clear; lia). change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
        clear - Hx FFA1 FFA2 F64. Z.div_mod_to_equations. lia.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. unfold FAKESZ in *. clear - Hx GFA. lia. }
    split; [eapply wmono_trans; [exact WMx| eapply wmono_trans; [exact WM1| exact WM2]]|].
    split; [exact MI5|]. split; [exact ST5|].
    split.
    { eapply ffr_pres_trans; [exact FFRx|]. apply fd_ffr_pres_mono_nil.
      eapply (fk_ffr_fin AI L RNG st LB mx mx m5 0 FF 64 (shad FF) 8 [] [(FF, FF + 8); (fflag L 0 FF, fflag L 0 FF + 1)]);
        [exact AHx| exact LBH| exact FFH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| clear; lia| clear; lia| | constructor| apply ffr_pres_refl| |
         eapply wmono_trans; [exact WM1| exact WM2]].
      - constructor; [cbn; split; [clear; lia| right; split; [intros b Hb; destruct (FFD b Hb); [left|right]; clear - H; lia| exists FF, (FF + 64); split; [exact FFH| clear; lia]]]|].
        constructor; [cbn; split; [clear; lia| right; split; [intros b Hb; exact (GBL b ltac:(right; exact Hb))| exists (fflag L 0 FF), (fflag L 0 FF + 1); split; [exact GH| clear; lia]]]| constructor].
      - eapply munch_trans.
        + eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
          rewrite ?Z.shiftr_div_pow2 in * by (clear; lia). change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia.
        + eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
    split; [exact AH5|].
    split.
    { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact STD| exact MU1| exact WM1| replace (DST + cap - DST) with cap by (clear; lia); exact DD1]
                                     | exact MU2| exact WM2| replace (DST + cap - DST) with cap by (clear; lia); exact DD2]. }
    split.
    { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact WKS| exact MU1| exact WM1| replace (WK + wksz - WK) with wksz by (clear; lia); exact DW1]
                                     | exact MU2| exact WM2| replace (WK + wksz - WK) with wksz by (clear; lia); exact DW2]. }
    split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_close : forall ms', QEXIT ms' -> evtF bsegs RNG POST ms'.
  Proof.
    intros ms' QE. destruct QE as [(mx & r & x1 & x2 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x16 & x17 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31
                                   & EX & RR & RES & ->)
                                  |(mx & r & x1 & x2 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x16 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31
                                   & EX & RR & RES & ->)].
    - pose proof HY as HY'. open_hy HY'. pose proof EX as EX'. destruct EX' as (MU & WM & MI & _).
      pose proof (fd_faM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as FA.
      clear - FFLAG FREL HY AN FR LBH INDST INWK FFD FFA1 FFA2 SPT EX RR RES MI FA SPB0 SPB1 SPR LOS LO0 RSTK RI KLO.
      zstep.
      eapply fd_close2; [exact EX| exact RR| exact RES].
    - eapply fd_close2; [exact EX| exact RR| exact RES].
  Qed.
End CL.
End CANSEC1.
