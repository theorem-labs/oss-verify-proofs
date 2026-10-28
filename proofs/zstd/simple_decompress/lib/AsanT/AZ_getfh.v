(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_frame_iface AZ_libc_iface AZ_libc AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_getfh_a AZ_getfh_b AZ_getfh_c AZ_getfh_d AZ_getfh_e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma gf_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] /\ rw_cells bsegs m 0xc7fa0 [C8 (Z_to_bv 64 0x8324c)].
Proof.
  intros m R. split; [| split]; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 144 - 4096 - 16.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition GSPA : Z := (SPV - 128) - (SPV - 128) mod 32.
  Lemma spa_props : SPV - 144 <= GSPA <= SPV - 128 /\ GSPA mod 32 = 0 /\ (SPV + -128) - (SPV + -128) mod 2^5 = GSPA.
  Proof. unfold GSPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma gf_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] ->
    rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x832c4) (Z_to_bv 64 GSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 GSPA)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xcfcf8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 a0 a1 a2 a3 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3ee8c) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 144, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -96) (GFSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
        /\ rw_cells bsegs m' GSPA [CB 32 jA]
        /\ stk bsegs m' lo GSPA /\ stk bsegs m' (GSPA + 32) (SPV + -96))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x8324c) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof spa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 144, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 96%nat ST. carve_frame 32%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 12 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -96).
    destruct (stk_split bsegs _ lo (GSPA + 32) (SPV + -96) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (GSPA + 32) 32 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 32) with 32 in STL, FRA. replace (GSPA + 32 - 32) with GSPA in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma gf_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs2 xs7 xs8 xs10 : word) m (FF FLG ZFH SRCo size : Z)
      (j0 j1 j2 : word) (junk jA : list byte),
    rw_cells bsegs m GSPA [CB 32 jA] -> stk bsegs m lo GSPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m 0xc7fa0 [C8 (Z_to_bv 64 0x8324c)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    0 < SRCo < 2^64 -> 5 <= size < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' jA' y13,
        ms' = MS (mkR (Z_to_bv 64 0x834ac) (Z_to_bv 64 GSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 GSPA)
                     (Z_to_bv 64 ZFH) (Z_to_bv 64 0) (Z_to_bv 64 48) y13 x14 x15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 ZFH) (Z_to_bv 64 SRCo) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 FF)
                     (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) (Z_to_bv 64 SHB) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x53ca0) fc None m' (seg_rom bsegs)
        /\ munch [(GSPA, GSPA + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' GSPA [CB 24 jA'; C8 (Z_to_bv 64 FF)] /\ stk bsegs m' lo GSPA
        /\ rw_cells bsegs m' FF (GFHDR FLG junk) /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) GFSH)
      (MS (mkR (Z_to_bv 64 0x832c4) (Z_to_bv 64 GSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 GSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               xs2 (Z_to_bv 64 ZFH) (Z_to_bv 64 SRCo) (Z_to_bv 64 size) (Z_to_bv 64 0) xs7 xs8 (Z_to_bv 64 SHB) xs10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x832c4) fc None m (seg_rom bsegs)).
  Proof.
    intros until jA. intros FRA STL FFC SHF GPC MI FH FC F64 RF RSF HS HZ.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof spa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow8_c1sA in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(GSPA, GSPA + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [24; 8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + SHB) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + SHB) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep. if_true.                               (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].   (* [comment removed for export] *)
    zstep. bcase K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.            (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [eassumption|].
    split; [exact FRA|]. split; [exact STL|]. split; [unfold GFHDR; exact FFC| unfold GFSH; exact SHF].
  Qed.
End S.

(* [comment removed for export] *)
Section GF2.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 m2 m3 : amem) (SPV SPA ZFH SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z) (jF : list byte).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis Z8 : ZFH mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 2208 /\ SPV - 144 <= SPA <= SPV - 128 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_zfh : ablk ZFH (ZFH + 48) /\ (ZFH + 48 <= lo \/ SPV <= ZFH).
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH).
  Hypothesis G_ff : ablk FF (FF + 64) /\ FF mod 64 = 0 /\ FF + 64 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 64 <= al_fake L + FAKESZ
                    /\ (ZFH + 48 <= FF \/ FF + 64 <= ZFH) /\ (SRC + zlen src <= FF \/ FF + 64 <= SRC).
  Hypothesis G_flg : FLG = fflag L 0 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB0 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (ZFH + 48 <= FLG \/ FLG + 1 <= ZFH).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_zfh : rng RNG ZFH 48 /\ rng RNG (shad ZFH) (shspan ZFH 48).
  Hypothesis R_ff : rng RNG FF 64 /\ rng RNG SHF 8 /\ rng RNG FLG 1.
  Hypothesis R_tbl : rng RNG 136800 32 /\ rng RNG (shad 136800) (shspan 136800 32) /\ rng RNG 136864 32 /\ rng RNG (shad 136864) (shspan 136864 32).
  (* [comment removed for export] *)
  Hypothesis LBH : ablkLB LB.
  Hypothesis AINZ : ainblk LB ZFH 48.
  Hypothesis AH2 : AHEAP AI L RNG st (FB0 FF :: LB) m2.
  Hypothesis FFR2 : ffr_pres [] LB m0 m2.
  Hypothesis MU23 : munch [(ZFH, ZFH + 48); (SPA - 2208, SPA + 32); (FF, FF + 24); (SHF, SHF + 8)] m2 m3.
  Hypothesis WM23 : wmono bsegs m2 m3.
  Hypothesis MU03 : munch ([(ZFH, ZFH + 48); (SPV - 4320, SPV)] ++ fake_area L) m0 m3.
  Hypothesis WM03 : wmono bsegs m0 m3.

  Notation WB := [(ZFH, ZFH + 48)].
  Notation WX := [(ZFH, ZFH + 48); (FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)].
  Notation POST := (zd_getfh_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV ZFH src off size lo m0).

  Notation fhd := (Znth (off + 4) src).
  Notation sseg := (fhd_singleSegment fhd).
  Notation dcode := (fhd_dictIDSizeCode fhd).
  Notation fcsid := (fhd_fcsID fhd).
  Notation P1 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0)).
  Notation P2 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0) + did_fieldSize (fhd_dictIDSizeCode fhd)).
  Notation DID := (fh_read_dictID src P1 dcode).
  Notation FCS := (fh_read_fcs src P2 fcsid sseg).
  Notation WS := (if fhd_singleSegment fhd =? 0 then wl_windowSize (Znth (off + 5) src) else FCS).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 FF)
             (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation XINV := (AZ_getfh_a.XINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MINV := (AZ_getfh_a.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MAINP := (AZ_getfh_a.MAINP src off size).

  Lemma gf_body : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    MINV m1 (Z0A (Z_to_bv 64 0)) ->
    evtF bsegs RNG POST (STpc 0x834ac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    pose proof (AZ_getfh_a.p_fin AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  OK OFF0 N5 OFS Z8 G_lo G_zfh G_src G_ff G_flg RSTK RI R_src R_zfh R_ff R_tbl LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03) as PFIN.
    pose proof (AZ_getfh_b.p_fcs AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  OK OFF0 N5 OFS Z8 G_lo G_zfh G_src G_ff G_flg R_src LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03 PFIN) as PFCS.
    pose proof (AZ_getfh_c.p_did AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  OK OFF0 N5 OFS Z8 G_lo G_zfh G_src G_ff G_flg R_src LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03 PFCS) as PDID.
    pose proof (AZ_getfh_a.p_exit AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  G_lo G_zfh G_ff G_flg RSTK RI R_zfh R_ff LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03) as PEXIT.
    pose proof (AZ_getfh_d.p_magic AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  OK OFF0 N5 OFS Z8 G_lo G_zfh G_src G_ff G_flg R_src R_zfh R_tbl LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03 PEXIT PDID) as PMAGIC.
    exact (AZ_getfh_e.p_top AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 m2 m3 SPV SPA ZFH SRC src off size lo FF SHF FLG jF
                  OK OFF0 N5 OFS Z8 G_lo G_zfh G_src G_ff G_flg R_src R_zfh LBH AINZ AH2 FFR2 MU23 WM23 MU03 WM03 PEXIT PMAGIC).
  Qed.
End GF2.

(* [comment removed for export] *)
Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.

  Theorem zd_getfh_proofA : zd_getfh_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV ZFH SRC src off size cs0 lo
           SB OK OFF0 N5 OFS SRC0 ZC0 ZSZ Z8U ST LO SZF SSR SZS AFP ARO ARS AIS Z8 ARZ AHZ AINZ MI TP -> -> -> ->.   (* [comment removed for export] *)
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (gf_got_cells m (AI_relro AI _ _ _ _ _ AH)) as (G1 & G2 & _).
    assert (LOS : lo <= SPV - 144 - 4096 - 16) by lia.
    assert (LOC : ATOP <= lo) by lia.
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (spa_props SPV SP16) as (SPAB & SPA32 & _).
    unfold APZD_GETFH.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (gf_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOS LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
    clear C0 GOT RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
    (* [comment removed for export] *)
    pose proof (ASH 0 ltac:(lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM0K (Z.to_nat (4096 - 1)) ltac:(lia)) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (GSPA SPV)) by lia;
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (GSPA SPV)) in ST2, HPR2, MUF2 by lia.
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
    (* [comment removed for export] *)
    destruct (gf_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as (_ & _ & GPC2).
    pose proof (fk_ablk_lits _ _ (proj1 (ARS ltac:(lia)))) as SL.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    eapply evtF_cut.
    { eapply (gf_hdr gp tp s11 FR fc SPV lo SP16 LOS LOC RNG RSTK RI);
        [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F64| exact RFF| exact RSFF| lia| lia]. }
    cbv beta. intros ms' (m3 & jA' & y13 & -> & MU3 & WM3 & MI3 & FRA3 & STL3 & FFC3 & SHF3).
    (* [comment removed for export] *)
    pose proof (ARZ ltac:(lia)) as (ZB & UZ0 & RZ1 & RZ2). pose proof (fk_ablk_lits _ _ ZB) as ZL.
    pose proof (ARS ltac:(lia)) as (SBK & US0 & RS1 & RS2).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ ZFH 48 AH2 AINZ ltac:(lia)) as DZF.
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 144, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [lia| exact I]. }
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 144, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
      clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
    assert (D3Z : disjoint_from [(GSPA SPV, GSPA SPV + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] ZFH 48).
    { cbn [disjoint_from]. split; [clear - SZF SPAB LO; lia|]. split; [clear - DZF; lia|]. split; [clear - ZL BSF ATR; lia| exact I]. }
    assert (DS3Z : disjoint_from [(GSPA SPV, GSPA SPV + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] (shad ZFH) (shad (ZFH + 48 - 1) + 1 - shad ZFH)).
    { cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
      pose proof (fk_ablk_lits _ _ FH) as FL. clear - ZL FL DZF F64 SPAB LO BOT ATR. repeat split; Z.div_mod_to_equations; lia. }
    assert (ZC3 : rw_cells bsegs m3 ZFH cs0).
    { eapply rw_cells_transport; [| exact MU3| exact WM3| rewrite ZSZ; exact D3Z].
      eapply (fk_cells_pres AI); [exact HPR2| rewrite ZSZ; exact AINZ|].
      eapply rw_cells_transport; [exact ZC0| exact MU1| exact WM1| rewrite ZSZ; apply D1; [exact SZF| lia]]. }
    assert (UZ3 : unpoisoned m3 ZFH (ZFH + 48)).
    { eapply unpoisoned_munch; [| exact MU3| exact DS3Z].
      eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact AINZ| lia|].
      eapply unpoisoned_munch; [exact UZ0| exact MU1| apply DS1; clear - ZL ATR; lia]. }
    destruct (rw_cells_forget _ _ _ _ ZC3) as [junkZ ZC3']. rewrite ZSZ in ZC3'.
    assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
      constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
    assert (ART3 : art m3).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH3) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (zd_memsetZ_proofA RNG ZFH 48 0 (GSPA SPV)) with (lo := lo);
        [exact ZC3'| lia| lia| exact STL3| lia| lia| clear - SZF SPAB LO; lia
        | eapply aregU_app_blk; [exact (ARZ ltac:(lia))| lia]
        | split; [exact UZ3| split; [exact RZ1| exact RZ2]]
        | destruct AHZ as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists RLO, RHI; repeat (split; [assumption|]);
          split; [eapply wr_at_transport; [exact H7| exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))]| exact H8]
        | exact ART3
        | split; [exact KHI| split; [eapply rng_sub'; [exact RSTK| lia]| exact RI]]
        | exact MI3| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros ms' (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & ZC4).
    rd_retlit.
    eapply (gf_body AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m2 m4 SPV (GSPA SPV) ZFH SRC src off size lo
                    FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) junk OK OFF0 N5 OFS Z8).
    - (* [comment removed for export] *) unfold KEND in SPK. clear - BOT LO SPAB SPA32 SPK SP16. repeat split; lia.
    - (* [comment removed for export] *) split; [exact ZB| exact SZF].
    - (* [comment removed for export] *) split; [exact SBK| split; [exact SSR| exact SZS]].
    - (* [comment removed for export] *) split; [exact FH|]. split; [exact F64|]. split; [exact FC|]. split; [unfold shad, ASHOFF; lia|]. split; [exact FFA1|]. split; [exact FFA2|].
      split; [clear - DZF; lia|].
      destruct (AIS ltac:(clear - OFS N5 OFF0; lia)) as [IB|[IM1 IM2]];
        [pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 IB ltac:(clear - OFS N5 OFF0; lia)); lia| unfold AIMG_HI in IM2; lia].
    - (* [comment removed for export] *) destruct (FFLAG _ _ _ _ _ 0 FF 64 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
      split; [reflexivity|]. split; [exact LBK|]. split; [exact LTOP|]. split; [exact LFA|]. split; [exact LAP|].
      destruct AINZ as (b & Hb & Hb1 & Hb2). pose proof (LAP b ltac:(right; exact Hb)) as LZ. clear - LZ Hb1 Hb2. lia.
    - exact RSTK.
    - exact RI.
    - split; [exact RS1| exact RS2].
    - split; [exact RZ1| exact RZ2].
    - split; [exact RFF|]. split; [replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia); exact RSFF|].
      destruct (FFLAG _ _ _ _ _ 0 FF 64 AH2 ltac:(left; reflexivity)) as (_ & RL & _). exact RL.
    - destruct ARO as [AROT _].
      destruct (AROT 136800 32 ltac:(cbn; do 13 right; left; reflexivity)) as (_ & T1 & T2). destruct (AROT 136864 32 ltac:(cbn; do 14 right; left; reflexivity)) as (_ & T3 & T4).
      split; [exact T1|]. split; [exact T2|]. split; [exact T3| exact T4].
    - exact LBH.
    - exact AINZ.
    - exact AH2.
    - (* [comment removed for export] *) eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2.
    - (* [comment removed for export] *) eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia.
    - exact (wmono_trans _ _ _ _ WM3 WM4).
    - (* [comment removed for export] *) eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx SPAB LO; cbn [outside app fake_area] in *; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx SPAB LO; cbn [outside app fake_area] in *; unfold SMK_STACK in *; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; intros x Hx; clear - Hx FFA1 FFA2 SPAB LO BOT F64 FHb;
        cbn [outside app fake_area] in *; rewrite ?shad_div in *; rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold FAKESZ, ASHOFF in *;
        Z.div_mod_to_equations; lia.
    - exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 WM4))).
    - (* [comment removed for export] *)
      pose proof (fk_ablk_lits _ _ FH) as FL.
      destruct (FFLAG _ _ _ _ _ 0 FF 64 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
      pose proof (fk_ablk_lits _ _ LBK) as LL. pose proof (LAP _ ltac:(left; reflexivity)) as LFF. cbn [ab_addr ab_size] in LFF.
      destruct AINZ as (bz & Hbz & Hbz1 & Hbz2). pose proof (LAP bz ltac:(right; exact Hbz)) as LZ.
      (* [comment removed for export] *)
      assert (D4 : forall X n, (X + n <= lo \/ SPV <= X) -> (ZFH + 48 <= X \/ X + n <= ZFH) -> 0 <= n -> disjoint_from [(GSPA SPV - 2208, GSPA SPV); (ZFH, ZFH + 48)] X n).
      { intros X nn HX HZ Hn. cbn [disjoint_from]. split; [clear - HX SPAB LO Hn; lia|]. split; [clear - HZ Hn; lia| exact I]. }
      assert (DS4 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(GSPA SPV - 2208, GSPA SPV); (ZFH, ZFH + 48)] (shad X) (shad (X + n - 1) + 1 - shad X)).
      { intros X nn X0 Hn Hb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
        split; [left; clear - X0 Hn Hb ATR BOT LO SPAB; Z.div_mod_to_equations; lia|].
        split; [clear - X0 Hn Hb ZL ATR; Z.div_mod_to_equations; lia| exact I]. }
      assert (SRCAP : (SRC + zlen src <= FF \/ FF + 64 <= SRC)).
      { destruct (AIS ltac:(clear - OFS N5 OFF0; lia)) as [IB|[IM1 IM2]];
          [pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 IB ltac:(clear - OFS N5 OFF0; lia)); lia| unfold AIMG_HI in IM2; lia]. }
      assert (D3S : disjoint_from [(GSPA SPV, GSPA SPV + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] SRC (zlen src)).
      { cbn [disjoint_from]. split; [clear - SSR SPAB LO; lia|]. split; [clear - SRCAP; lia|]. split; [clear - SL BSF ATR; lia| exact I]. }
      split.
      { (* [comment removed for export] *)
        eapply bytes_at_transport; [| exact MU4| rewrite length_map; apply D4; [exact SSR| exact SZS| lia]].
        eapply bytes_at_transport; [| exact MU3| rewrite length_map; exact D3S].
        destruct (AIS ltac:(clear - OFS N5 OFF0; lia)) as [IB|[IM1 IM2]].
        - eapply (fk_bytes_pres AI); [exact HPR2| rewrite length_map; exact IB|].
          eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply D1; [exact SSR| lia]].
        - eapply bytes_at_transport; [| exact MUF2| rewrite length_map; cbn [disjoint_from fake_area app]; rewrite ?shad_div; unfold AIMG_HI, SMK_STACK, FAKESZ, ASHOFF in *;
            destruct LY5 as (_ & _ & FA1 & FA2); repeat split; clear - IM1 IM2 FA1 FA2 SPAB LO BOT ATR; Z.div_mod_to_equations; lia].
          eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply D1; [exact SSR| lia]]. }
      split.
      { (* [comment removed for export] *)
        apply (rw_cells_recell bsegs _ ZFH _ (Z0A (Z_to_bv 64 0))) in ZC4; [exact ZC4| clear; cbn; tauto | vm_compute; reflexivity]. }
      (* [comment removed for export] *)
      assert (FRB4 : rw_cells bsegs m4 (SPV + -96) (GFSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
      { eapply rw_cells_transport; [| exact MU4| exact WM4| cbn; clear - SZF SPAB LO; lia].
        eapply rw_cells_transport; [exact FRB2| exact MU3| exact WM3| cbn; clear - SPAB LO BOT FHc FL BSF ATR; lia]. }
      assert (FRA4 : rw_cells bsegs m4 (GSPA SPV) [CB 24 jA'; C8 (Z_to_bv 64 FF)]).
      { eapply rw_cells_transport; [exact FRA3| exact MU4| exact WM4| cbn; clear - SZF SPAB LO; lia]. }
      destruct (rw_cells_forget _ _ _ _ FRA4) as [jA4 FRA4']. cbn [cells_size csize Nat.add] in FRA4'.
      assert (STG4 : stk bsegs m4 (GSPA SPV + 32) (SPV + -96)).
      { eapply stk_transport_disjoint; [| exact MU4| exact WM4| cbn; clear - SZF SPAB LO; lia].
        eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn; clear - SPAB LO BOT FHc FL BSF ATR; lia]. }
      assert (XF4 : rw_cells bsegs m4 FF (GFHDR (fflag L 0 FF) junk)).
      { eapply rw_cells_transport; [exact FFC3| exact MU4| exact WM4| cbn; clear - DZF FHc FL LOC LO SPAB; lia]. }
      assert (XS4 : rw_cells bsegs m4 (Z.shiftr FF 3 + SHB) GFSH).
      { eapply rw_cells_transport; [exact SHF3| exact MU4| exact WM4| cbn; clear - BSF ZL BOT LO SPAB ATR; lia]. }
      assert (XL4 : rw_cells bsegs m4 (fflag L 0 FF) [C1 (Z_to_bv 8 1)]).
      { eapply rw_cells_transport; [| exact MU4| exact WM4| cbn; clear - LZ Hbz1 Hbz2 LL LTOP LOC LO SPAB; lia].
        eapply rw_cells_transport; [exact XL2| exact MU3| exact WM3| cbn; clear - LFF LL LTOP LOC LO SPAB BSF ATR; lia]. }
      assert (US4 : unpoisoned m4 SRC (SRC + zlen src)).
      { eapply unpoisoned_munch; [| exact MU4| apply DS4; clear - SL ATR; lia].
        eapply unpoisoned_munch; [| exact MU3|].
        - destruct (AIS ltac:(clear - OFS N5 OFF0; lia)) as [IB|[IM1 IM2]].
          + eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IB| clear - OFS N5 OFF0; lia|].
            eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR; lia].
          + eapply unpoisoned_munch; [| exact MUF2|].
            * eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR; lia].
            * cbn [disjoint_from fake_area app]. rewrite !shad_div. unfold AIMG_HI, SMK_STACK, FAKESZ, ASHOFF in *. destruct LY5 as (_ & _ & FA1 & FA2).
              clear - IM1 IM2 FA1 FA2 FABL SPAB LO BOT ATR OFS N5 OFF0. repeat split; Z.div_mod_to_equations; lia.
        - cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
          clear - SL FL SRCAP F64 SPAB LO BOT ATR OFS N5 OFF0. repeat split; Z.div_mod_to_equations; lia. }
      assert (UZ4 : unpoisoned m4 ZFH (ZFH + 48)).
      { eapply unpoisoned_munch; [exact UZ3| exact MU4| apply DS4; clear - ZL ATR; lia]. }
      destruct ARO as [AROT _].
      destruct (AROT 136800 32 ltac:(cbn; do 13 right; left; reflexivity)) as (UT1_0 & _). destruct (AROT 136864 32 ltac:(cbn; do 14 right; left; reflexivity)) as (UT2_0 & _).
      assert (TI : forall X, 0 <= X -> X + 32 <= AIMG_HI ->
              disjoint_from [(SPV - 144, SPV)] (shad X) (shad (X + 32 - 1) + 1 - shad X)
              /\ disjoint_from (fake_area L ++ [(GSPA SPV - SMK_STACK, GSPA SPV)]) (shad X) (shad (X + 32 - 1) + 1 - shad X)
              /\ disjoint_from [(GSPA SPV, GSPA SPV + 32); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] (shad X) (shad (X + 32 - 1) + 1 - shad X)
              /\ disjoint_from [(GSPA SPV - 2208, GSPA SPV); (ZFH, ZFH + 48)] (shad X) (shad (X + 32 - 1) + 1 - shad X)).
      { intros X X0 XH. unfold AIMG_HI in XH. destruct LY5 as (_ & _ & FA1 & FA2). unfold AIMG_HI, FAKESZ in FA1, FA2.
        cbn [disjoint_from fake_area app]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        unfold ASHOFF, SMK_STACK, FAKESZ in *. clear - X0 XH FA1 FA2 FABL SPAB LO BOT FHa FL F64 ZL ATR.
        repeat split; Z.div_mod_to_equations; lia. }
      assert (UT1_4 : unpoisoned m4 136800 (136800 + 32)).
      { destruct (TI 136800 ltac:(lia) ltac:(unfold AIMG_HI; lia)) as (Q1 & Q2 & Q3 & Q4).
        eapply unpoisoned_munch; [| exact MU4| exact Q4]. eapply unpoisoned_munch; [| exact MU3| exact Q3].
        eapply unpoisoned_munch; [| exact MUF2| exact Q2]. eapply unpoisoned_munch; [exact UT1_0| exact MU1| exact Q1]. }
      assert (UT2_4 : unpoisoned m4 136864 (136864 + 32)).
      { destruct (TI 136864 ltac:(lia) ltac:(unfold AIMG_HI; lia)) as (Q1 & Q2 & Q3 & Q4).
        eapply unpoisoned_munch; [| exact MU4| exact Q4]. eapply unpoisoned_munch; [| exact MU3| exact Q3].
        eapply unpoisoned_munch; [| exact MUF2| exact Q2]. eapply unpoisoned_munch; [exact UT2_0| exact MU1| exact Q1]. }
      split; [exact FRB4|]. split; [exists jA4; exact FRA4'|]. split; [exact ST4|]. split; [exact STG4|].
      split; [exact XF4|]. split; [exact XS4|]. split; [exact XL4|]. split; [exact US4|]. split; [exact UZ4|].
      split; [exact UT1_4|]. split; [exact UT2_4|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI4].
  Qed.
End Thm.
End CANSEC1.
