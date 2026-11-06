(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_frame_iface AZ_dframe_iface AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_dmf_a AZ_dmf_b.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.
Notation wz := (Z_to_bv 64 0).

Section CANSEC1. Context {rc : runConstT}.
Lemma dm_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xcb9f8 [C8 (Z_to_bv 64 0xd4300)] /\ rw_cells bsegs m 0xcb9a0 [C8 (Z_to_bv 64 0xd42f8)].
Proof.
  intros m R. split; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Notation B00 := (Z_to_bv 8 0).
Definition FSH00 : list cell :=
  [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma dm_shadow32_c1s : forall (m : amem) s, rw_cells bsegs m s [C8 wz; C8 wz; C8 wz; C8 wz] -> rw_cells bsegs m s FSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 7088.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition DSPA : Z := (SPV - 416) - (SPV - 416) mod 32.
  Lemma dspa_props : SPV - 447 <= DSPA <= SPV - 416 /\ DSPA mod 32 = 0 /\ (SPV + -416) - (SPV + -416) mod 2^5 = DSPA.
  Proof. unfold DSPA. change (2^5) with 32. clear - SP16. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma dm_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xcb9f8 [C8 (Z_to_bv 64 0xd4300)] -> rw_cells bsegs m 0xcb9a0 [C8 (Z_to_bv 64 0xd42f8)] ->
    rw_cells bsegs m 0xd4300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB jC jD,
        ms' = MS (mkR (Z_to_bv 64 0x84a1c) (Z_to_bv 64 DSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                     (Z_to_bv 64 160) (Z_to_bv 64 0xd42f8) (Z_to_bv 64 1) a3 a4 wz wz wz
                     s2 a1 s4 a4 (Z_to_bv 64 SHB) s7 s8 s9 a3 wz t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3f234) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 447, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' DSPA [CB 216 jA; C8 wz; C8 wz; CB 16 jB; C8 a0; CB 24 jC; C8 a2; CB 24 jD]
        /\ stk bsegs m' lo DSPA /\ stk bsegs m' (DSPA + 312) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 wz wz wz s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x84990) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof dspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 447, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 312%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (DSPA + 312) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (DSPA + 312) 312 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 312) with 312 in STL, FRA. replace (DSPA + 312 - 312) with DSPA in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma dm_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x23 x24 x25 x28 x29 x30 x31 : word) m (FF FLG DCTX CAP DST SRC size : Z)
      (j0 j1 j2 wD wC : word) (junk jA jB jC jD : list byte),
    rw_cells bsegs m DSPA [CB 216 jA; C8 wz; C8 wz; CB 16 jB; C8 wD; CB 24 jC; C8 wC; CB 24 jD] -> stk bsegs m lo DSPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 wz; C8 wz; C8 wz; C8 wz] ->
    mem_inv bsegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 -> rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    evtF bsegs RNG (fun ms' => exists m' jD' y10 y11 y12 y13,
        ms' = MS (mkR (Z_to_bv 64 0x84a1c) (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                     y10 y11 y12 y13 x14 x15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 DST) (Z_to_bv 64 FF) (Z_to_bv 64 size) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr FF 3 + SHB))
                     x24 x25 (Z_to_bv 64 SRC) wz x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x84b00) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA + 304, DSPA + 312); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 20)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA [CB 216 jA; C8 wz; C8 wz; CB 16 jB; C8 wD; CB 24 jC; C8 wC; CB 16 jD'; C8 (Z_to_bv 64 FF)] /\ stk bsegs m' lo DSPA
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20851); C8 (Z_to_bv 64 0x84990); CB 224 junk; C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) DSHC)
      (MS (mkR (Z_to_bv 64 0x84a1c) (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 DST) x20 (Z_to_bv 64 size) (Z_to_bv 64 SHB) x23 x24 x25 (Z_to_bv 64 SRC) wz x28 x29 x30 x31)
          FR (Z_to_bv 64 0x84a1c) fc None m (seg_rom bsegs)).
  Proof.
    intros until jD. intros FRA STL FFC SHF MI FH FC F256 RF RSF.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof dspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply dm_shadow32_c1s in SHF. unfold FSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; clear - FHa FHc ATR; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(DSPA + 304, DSPA + 312); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 20)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 5 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    do 8 zstep.                                   (* [comment removed for export] *)
    do 2 zstep.                                   (* [comment removed for export] *)
    do 2 zstep.                                   (* [comment removed for export] *)
    zstep. bcase KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; clear - KT; lia].   (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _, _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia|].
    split; [exact WM|]. split; [eassumption|]. split; [exact FRA|]. split; [exact STL|]. split; [exact FFC| exact SHF].
  Qed.

  (* [comment removed for export] *)
  Lemma dm_setup : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) m (FF DCTX CAP DST SRC size : Z)
      (jA jB jC jD : list byte),
    rw_cells bsegs m DSPA [CB 216 jA; C8 wz; C8 wz; CB 16 jB; C8 (Z_to_bv 64 DCTX); CB 24 jC; C8 (Z_to_bv 64 CAP); CB 16 jD; C8 (Z_to_bv 64 FF)] ->
    mem_inv bsegs m -> 4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
    evtF bsegs RNG (fun ms' => exists m' (y10 y11 y12 y13 y14 y15 y25 y28 y29 : word) (v8 v16 v24 v32 v40 vfl : word) (j0 : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x84a1c) (Z_to_bv 64 DSPA) gp tp (Z_to_bv 64 8) (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                     y10 y11 y12 y13 y14 y15 x16 x17
                     (Z_to_bv 64 DCTX) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + 0)) (Z_to_bv 64 size) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr FF 3 + SHB))
                     x24 y25 (Z_to_bv 64 (SRC + 0)) wz y28 y29 (Z_to_bv 64 1) x31)
                 FR (Z_to_bv 64 0x84c00) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA, DSPA + 312)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA (AZ_dmf_b.DFR DCTX DST FF v8 v16 v24 v32 v40 vfl (Z_to_bv 64 (CAP - 0)) j0 jD))
      (MS (mkR (Z_to_bv 64 0x84a1c) (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 DST) (Z_to_bv 64 FF) (Z_to_bv 64 size) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x24 x25 (Z_to_bv 64 SRC) wz x28 x29 x30 x31)
          FR (Z_to_bv 64 0x84b00) fc None m (seg_rom bsegs)).
  Proof.
    intros until jD. intros FRA MI RD0 RD1 RD8.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof dspa_props as (SPAB & SPA32 & _).
    pose proof (munch_refl [(DSPA, DSPA + 312)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    replace (CAP - 0) with CAP by (clear; lia). replace (SRC + 0) with SRC by (clear; lia). replace (DST + 0) with DST by (clear; lia).
    zstep.                                       (* [comment removed for export] *)
    zstep.                                       (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; [exfalso; clear - K1 RD0 RD1; lia| clear K1].   (* [comment removed for export] *)
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 RD0 RD8; change 7 with (Z.ones 3) in K2; rewrite Z.land_ones in K2 by lia; change (2^3) with 8 in K2; lia| clear K2].   (* [comment removed for export] *)
    do 59 zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    replace (Z.land (DCTX + 30104) 7 + 3) with 3 in FRA by (clear - RD8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    replace ((DCTX + 30104) ≫ 3 + SHB) with (SHB + (DCTX + 30104) / 8) in FRA by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 48 _ _ [8; 8; 8; 8; 8; 8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    destruct (cb8_as_c8 bsegs _ _ [CB 8 _] _ _ FRA) as [v8 FRA1]. clear FRA. cbn [app] in FRA1.
    destruct (cb8_as_c8 bsegs _ _ [CB 8 _; C8 v8] _ _ FRA1) as [v16 FRA2]. clear FRA1. cbn [app] in FRA2.
    destruct (cb8_as_c8 bsegs _ _ [CB 8 _; C8 v8; C8 v16] _ _ FRA2) as [v24 FRA3]. clear FRA2. cbn [app] in FRA3.
    destruct (cb8_as_c8 bsegs _ _ [CB 8 _; C8 v8; C8 v16; C8 v24] _ _ FRA3) as [v32 FRA4]. clear FRA3. cbn [app] in FRA4.
    destruct (cb8_as_c8 bsegs _ _ [CB 8 _; C8 v8; C8 v16; C8 v24; C8 v32] _ _ FRA4) as [v40 FRA5]. clear FRA4. cbn [app] in FRA5.
    lazymatch type of FRA5 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c23 :: ?c24 :: ?c25 :: ?c26 :: ?c27 :: ?c28 :: ?c29 :: ?c30 :: ?c31 :: ?c32 :: ?post) =>
      destruct (cb8_as_c8 bsegs _ _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22; c23; c24; c25; c26; c27; c28; c29; c30; c31; c32] _ _ FRA5) as [vfl FRA6] end.
    clear FRA5. cbn [app] in FRA6.
    do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. unfold AZ_dmf_b.DFR. exact FRA6.
  Qed.
End S.
End CANSEC1.
