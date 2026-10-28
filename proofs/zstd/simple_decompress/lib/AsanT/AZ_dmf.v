(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_frame_iface AZ_xxh_iface AZ_dframe_iface AZ_block_iface AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_dmf_a AZ_dmf_b AZ_dmf_c AZ_dmf_d AZ_dmf_e AZ_dmf_f AZ_dmf_f2 AZ_dmf_f3 AZ_dmf_g AZ_dmf_h AZ_dmf_h2 AZ_dmf_h2b AZ_dmf_h3 AZ_dmf_i.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation wz := (Z_to_bv 64 0).
Notation SPL w344 w352 w360 w368 jA jC FF :=
  ([CB 328 jA; C8 wz; C8 wz; C8 w344; C8 w352; C8 w360; C8 w368; C8 wz; CB 16 jC; C8 (Z_to_bv 64 FF)]).
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dm_stk_pres : forall AI LB SP (m m' : amem) lo hi,
  aheap_pres (aci AI) LB SP m m' -> ainblk LB lo (hi - lo) -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros AI LB SP m m' lo hi HP (b & Hb & H1 & H2) (A0 & A1 & HW). split; [exact A0|]. split; [exact A1|].
  intros i Hi. destruct (HP i ltac:(clear - Hi A0 A1; lia) ltac:(right; right; left; exists b; split; [exact Hb| clear - Hi H1 H2; lia])) as [E W].
  destruct (HW i Hi) as [W0 [bb Hbb]]. split; [apply W, W0|]. exists bb. unfold mrd in *. rewrite E. exact Hbb.
Qed.

(* [comment removed for export] *)
Lemma dm_dctx_any_pres : forall AI LB SP (m m' : amem) DCTX,
  aheap_pres (aci AI) LB SP m m' -> ainblk LB DCTX 95992 -> dctx_any m DCTX -> dctx_any m' DCTX.
Proof.
  intros AI LB SP m m' DCTX HP IB (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                   PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]).
  assert (TR : forall A cs, rw_cells bsegs m A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m' A cs).
  { intros A cs RC L1 L2. eapply aheap_pres_rw_cells; [exact HP | exact RC |]. apply fk_acr_inblk. destruct IB as (b & Hb & B1 & B2). exists b. split; [exact Hb| clear - L1 L2 B1 B2; lia]. }
  assert (TS : forall a b, stk bsegs m a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk bsegs m' a b).
  { intros a b SK L1 L2 L3. eapply dm_stk_pres; [exact HP | | exact SK]. destruct IB as (bb & Hb & B1 & B2). exists bb. split; [exact Hb| clear - L1 L2 L3 B1 B2; lia]. }
  unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
  exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
  split; [apply TR; [exact PT | clear; lia | cbn; clear; lia]|].
  split; [apply TR; [exact H1 | clear; lia | cbn; clear; lia]|].
  split; [split; [apply TR; [exact FPC | clear; lia | rewrite FPSZ; clear; lia]| exact FPSZ]|].
  split; [apply TR; [exact H3 | clear; lia | cbn; clear; lia]|].
  split; [split; [apply TR; [exact XSC | clear; lia | rewrite XSSZ; clear; lia]| exact XSSZ]|].
  split; [split; [apply TR; [exact H5C | clear; lia | rewrite (h5_cells_size _ H5L); clear; lia]| exact H5L]|].
  split; [exact H5OK|].
  split; [apply TR; [exact TX | clear; lia | cbn; clear; lia]|].
  split; (apply TS; [assumption| clear; lia| clear; lia| clear; lia]).
Qed.


Section S2.
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 7184.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Notation DSPA := (AZ_dmf_i.DSPA SPV).

  (* [comment removed for export] *)
  Lemma dm_fmt : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word) m
      (FF DCTX : Z) (w344 w352 w360 w368 : word) (jA jC : list byte),
    rw_cells bsegs m DSPA (SPL w344 w352 w360 w368 jA jC FF) -> mem_inv bsegs m ->
    unpoisoned m DCTX (DCTX + 95992) -> rng RNG (shad DCTX) (shspan DCTX 95992) ->
    6443008 <= DCTX -> DCTX + 95992 <= ATOP -> DCTX mod 8 = 0 ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 (Z_to_bv 64 SHB) x24 x25 x26 (Z_to_bv 64 (DCTX + 29912)) x28 x29 x30 (Z_to_bv 64 (DCTX + 30104)))
                 FR (Z_to_bv 64 0x848f4) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA + 360, DSPA + 368)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA (SPL w344 w352 (Z_to_bv 64 (SHB + (DCTX + 30104) / 8)) w368 jA jC FF))
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 SHB) x24 x25 x26 (Z_to_bv 64 (DCTX + 29912)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x848dc) fc None m (seg_rom bsegs)).
  Proof.
    intros until jC. intros FRA MI UD RDS D1 D2 RD8.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (dspa_props SPV SP16) as (SPAB & SPA32 & _).
    pose proof (munch_refl [(DSPA + 360, DSPA + 368)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m' end.
    assert (UD' : unpoisoned m' DCTX (DCTX + 95992)).
    { eapply unpoisoned_munch; [exact UD| exact MU|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
      clear - SPAB LOS LOC D1 D2 ATR. split; [| exact I]. Z.div_mod_to_equations. lia. }
    pose proof (AZ_dmf_b.dm_sh_rd0 m' DCTX 95992 (DCTX + 30104) UD' ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 ATR; lia)) as RDz.
    assert (RTz : rng RNG (SHB + (DCTX + 30104) / 8) 1).
    { eapply rng_sub'; [exact RDS|]. unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    assert (ESH : SHB + (DCTX + 30104) / 8 = (DCTX + 30104) ≫ 3 + SHB) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
    rewrite ESH in RDz, RTz.
    zstep.                                        (* [comment removed for export] *)
    clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                              (* [comment removed for export] *)
    apply evtF_done. exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    rewrite ESH. exact FRA.
  Qed.

  Lemma dm_go : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) m
      (FF DCTX size : Z) (ws : list word) (w344 w352 w360 w368 : word) (jA jC : list byte),
    rw_cells bsegs m DSPA (SPL w344 w352 w360 w368 jA jC FF) -> mem_inv bsegs m ->
    dctx_h5 bsegs m DCTX ws -> h5_frame_ok ws -> rng RNG DCTX 95992 ->
    6443008 <= DCTX -> DCTX + 95992 <= ATOP -> 5 <= size < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) (Z_to_bv 64 0) (Z_to_bv 64 5) x12 x13 x14 x15 x16 x17
                     x18 (Z_to_bv 64 FF) (Z_to_bv 64 size) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DCTX + 30104)))
                 FR (Z_to_bv 64 0x84908) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA + 344, DSPA + 352)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA (SPL (Z_to_bv 64 FF) w352 w360 w368 jA jC FF))
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 FF) (Z_to_bv 64 size) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DCTX + 30104)))
          FR (Z_to_bv 64 0x848f4) fc None m (seg_rom bsegs)).
  Proof.
    intros until jC. intros FRA MI [H5C H5L] H5OK RD D1 D2 HS.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (dspa_props SPV SP16) as (SPAB & SPA32 & _).
    pose proof (munch_refl [(DSPA + 344, DSPA + 352)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof H5OK as (K_FMT & _). h5_open ws H5L. lazymatch type of K_FMT with ?x = _ => subst x end. unfold wz0 in H5C.
    zstep. rewrite (sx32w_small 0) by (clear; lia).
    zstep. if_true.
    zstep. zstep.
    zstep. if_cases KS; zify_cond KS; try (exfalso; clear - KS HS; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m' end.
    apply evtF_done. exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    exact FRA.
  Qed.

  (* [comment removed for export] *)
  Lemma dm_empty : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word) m
      (FF DCTX DST size : Z) (ws : list word) (w344 w352 w360 w368 : word) (jA jC : list byte),
    rw_cells bsegs m DSPA (SPL w344 w352 w360 w368 jA jC FF) -> mem_inv bsegs m ->
    dctx_h5 bsegs m DCTX ws -> h5_frame_ok ws -> rng RNG DCTX 95992 ->
    6443008 <= DCTX -> DCTX + 95992 <= ATOP -> 0 <= DST < 2^47 -> 0 <= size < 5 ->
    evtF bsegs RNG (fun ms' => exists m' y10,
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) y10 (Z_to_bv 64 5) x12 x13 x14 x15 x16 x17
                     x18 (Z_to_bv 64 FF) (Z_to_bv 64 size) x21 x22 x23 x24 (Z_to_bv 64 (if size =? 0 then 0 else -72)) x26 x27
                     (Z_to_bv 64 DST) x29 x30 (Z_to_bv 64 (DCTX + 30104)))
                 FR (Z_to_bv 64 0x855a0) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA + 344, DSPA + 352); (DSPA + 368, DSPA + 376)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA (SPL (Z_to_bv 64 FF) w352 w360 (Z_to_bv 64 DST) jA jC FF))
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 x8 (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 FF) (Z_to_bv 64 size) x21 x22 x23 x24 (Z_to_bv 64 DST) x26 x27 x28 x29 x30 (Z_to_bv 64 (DCTX + 30104)))
          FR (Z_to_bv 64 0x848f4) fc None m (seg_rom bsegs)).
  Proof.
    intros until jC. intros FRA MI [H5C H5L] H5OK RD D1 D2 RDT HS.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (dspa_props SPV SP16) as (SPAB & SPA32 & _).
    pose proof (munch_refl [(DSPA + 344, DSPA + 352); (DSPA + 368, DSPA + 376)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    pose proof H5OK as (K_FMT & _). h5_open ws H5L. lazymatch type of K_FMT with ?x = _ => subst x end. unfold wz0 in H5C.
    zstep. rewrite (sx32w_small 0) by (clear; lia).   (* [comment removed for export] *)
    zstep. if_true.                               (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS; try (exfalso; clear - KS HS; lia).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.             (* [comment removed for export] *)
    - zstep. zstep. zstep.                        (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m' end.
      replace (size =? 0) with true by (symmetry; apply Z.eqb_eq; clear - KZ HS; lia).
      (let w := getreg 25 in replace w with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; f_equal; clear; lia)).
      apply evtF_done. exists m'. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      exact FRA.
    - zstep. zstep.                               (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m' end.
      replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KZ HS; lia).
      apply evtF_done. exists m'. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      exact FRA.
  Qed.
End S2.

Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable TBL : tbl_pred.
  Hypothesis SM2K : forall k, Z.of_nat k < 4096 -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis TBLL : tbl_laws TBL.
  Hypothesis ERRCODE : zd_errcode_stmtA.
  Hypothesis DBEGIN : zd_dbegin_stmtA.
  Hypothesis CHECKCONT : zd_checkcont_stmtA.
  Hypothesis DECODEFH : zd_decodefh_stmtA AI rng_fs.
  Hypothesis GETCB : zd_getcblock_stmtA.
  Hypothesis DBLOCK : zd_dblock_stmtA AI rng_fs TBL.
  Hypothesis XXHUPD : zd_xxh_update_stmtA2.
  Hypothesis XXHDIG : zd_xxh_digest_stmtA.
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
  Hypothesis MEMSET : zd_memsetZ_stmtA.

  Notation DSPA := AZ_dmf_i.DSPA.

  Theorem zd_dmf_proofA : zd_dmf_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV lo DCTX DST CAP SRC src size
           DA RD0 RD1 RD8 GOT SB OK N0 NLEN N40 RS0 RS1 DSK RC0 RC40 DNULL DNN DZ RDST ST RLO LO RSP S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS
           AFP TP AZS ARO ARS AIS AH_sr RD8' ARD AH_dc AID ADST MI -> -> -> -> -> -> -> ->.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOTr & RIC & REAL & SHBc & SUA & _).
    destruct (dm_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [G1 G2].
    assert (LOS : lo <= SPV - 7184) by (clear - LO; lia). assert (LOC : ATOP <= lo) by (clear - BOT; lia).
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; clear - RSP SPT LY3; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (dspa_props SPV SP16) as (SPAB & SPA32 & _).
    pose proof (ARD ltac:(clear; lia)) as (ABD & UD0 & RD & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    unfold APZD_DMF, wz0.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (dm_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOS LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & jB & jC & -> & MU1 & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    clear C0 GOTr RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. clear - BOT LO RSP; lia. }
    (* [comment removed for export] *)
    pose proof (ASH 2 ltac:(clear; lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM2K (Z.to_nat (4096 - 7)) ltac:(clear; lia)) as SMC. unfold stack_malloc_2k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (DSPA SPV)) by (clear - SPAB BOT LO RSP ATR; lia);
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS
              | unfold SMK_STACK; clear - SPAB BOT LO SPT; lia
              | lazymatch goal with |- ?Gg => idtac "SM2K-LEFT:" Gg end]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F256 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (DSPA SPV)) in ST2, HPR2, MUF2 by (clear - SPAB BOT LO RSP ATR; lia).
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. pose proof (fk_ablk_lits _ _ FH) as FL.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SAV1 ltac:(left; left; cbn; clear - SPAB BOT LO RSP; lia)) as SAV2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; clear - SPAB BOT LO RSP; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(clear - SPAB; lia) ltac:(clear - RSP; lia)) as STG2.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (dm_hdr gp tp FR fc SPV lo SP16 LOS LOC RNG RSTK) with (DCTX := DCTX) (CAP := CAP);
        [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact MI2| exact FH| exact FC| exact F256| exact RFF| exact RSFF]. }
    cbv beta. intros ms' (m3 & jC' & y10 & y11 & y12 & y13 & -> & MU3 & WM3 & MI3 & FRA3 & STL3 & FFC3 & XS3).

    (* [comment removed for export] *)
    assert (G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 7184 /\ SPV - 543 <= DSPA SPV <= SPV - 512 /\ DSPA SPV mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0).
    { unfold KEND in SPK. clear - BOT LO SPAB SPA32 SPK SP16. repeat split; lia. }
    assert (DCFF : DCTX + 95992 <= FF \/ FF + 256 <= DCTX) by (exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ DCTX 95992 AH2 AID ltac:(clear; lia))).
    assert (DSFF : DST + CAP <= FF \/ FF + 256 <= DST).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - destruct (ADST HC) as (_ & _ & IB). exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ DST CAP AH2 IB ltac:(clear - HC; lia)).
      - left. pose proof (DZ ltac:(clear - HC RC0; lia)) as D00. clear - D00 HC RC0 FHa. lia. }
    destruct (FFLAG _ _ _ _ _ 2 FF 256 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
    pose proof (fk_ablk_lits _ _ LBK) as LL. pose proof (LAP _ ltac:(left; reflexivity)) as LFF. cbn [ab_addr ab_size] in LFF.
    assert (G_ff_of : forall SRCv, (SRCv + zlen src <= FF \/ FF + 256 <= SRCv) ->
                   ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ Z.shiftr FF 3 + SHB = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                   /\ (DCTX + 95992 <= FF \/ FF + 256 <= DCTX) /\ (DST + CAP <= FF \/ FF + 256 <= DST) /\ (SRCv + zlen src <= FF \/ FF + 256 <= SRCv)).
    { intros SRCv HS. split; [exact FH|]. split; [exact F256|]. split; [exact FC|]. split; [unfold shad, ASHOFF; clear; lia|]. split; [exact FFA1|]. split; [exact FFA2|].
      split; [exact DCFF|]. split; [exact DSFF| exact HS]. }
    assert (G_flg : fflag L 2 FF = fflag L 2 FF /\ ablk (fflag L 2 FF) (fflag L 2 FF + 1) /\ fflag L 2 FF + 1 <= ATOP /\ (al_fake L <= fflag L 2 FF /\ fflag L 2 FF + 1 <= al_fake L + FAKESZ)
                    /\ (forall b, In b (FB2 FF :: LB) -> fflag L 2 FF + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L 2 FF)).
    { split; [reflexivity|]. split; [exact LBK|]. split; [exact LTOP|]. split; [exact LFA| exact LAP]. }
    assert (B_dc : ablk DCTX (DCTX + 95992) /\ ainblk LB DCTX 95992) by (split; [exact ABD| exact AID]).
    assert (B_ds : 0 < CAP -> ablk DST (DST + CAP) /\ ainblk LB DST CAP).
    { intros HC. destruct (ADST HC) as (AR & _ & IB). split; [exact (proj1 (AR HC))| exact IB]. }
    assert (R_dc : rng RNG DCTX 95992 /\ rng RNG (shad DCTX) (shspan DCTX 95992)) by (split; [exact RD| exact RDS]).
    assert (R_ds : 0 < CAP -> rng RNG DST CAP /\ rng RNG (shad DST) (shspan DST CAP)).
    { intros HC. destruct (ADST HC) as (AR & _). pose proof (AR HC) as (_ & _ & R1 & R2). split; [exact R1| exact R2]. }
    assert (R_ff : rng RNG FF 256 /\ rng RNG (Z.shiftr FF 3 + SHB) 32 /\ rng RNG (fflag L 2 FF) 1).
    { split; [exact RFF|]. split; [replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; clear; lia); exact RSFF| exact RL]. }
    assert (AH_ds : 0 < CAP -> ahull RNG m DST CAP) by (intros HC; destruct (ADST HC) as (_ & A & _); exact A).

    (* [comment removed for export] *)
    assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn [fst snd]; left; left; cbn; unfold KEND in SPK; clear - BOT LO SPAB SPK; lia|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd] | constructor].
      replace (Z.shiftr FF 3 + SHB + 20 - (Z.shiftr FF 3 + SHB)) with 20 by (clear; lia). replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 20); [left; reflexivity | clear; lia | clear; lia | clear - F256; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (FFR02 : ffr_pres [] LB m m2).
    { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; clear - BOT LO RSP; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2. }
    assert (FFR03 : ffr_pres [(DCTX, DCTX + 95992); (DST, DST + CAP)] LB m m3).
    { apply dm_ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m m2 m3 2 FF 256 (Z.shiftr FF 3 + SHB) 20 [] [(DSPA SPV + 400, DSPA SPV + 408); (FF, FF + 24)]);
        [ exact AH2 | exact LBH | exact FH | clear - F256; Z.div_mod_to_equations; lia | unfold shad, ASHOFF; clear; lia | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia| left; unfold KEND in SPK; clear - BOT LO SPAB SPK; lia]|];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact FH| clear; lia]]] | constructor]
        | constructor | exact FFR02 | | exact WM3 ].
      cbn [app]. eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU03 : munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] ++ fake_area L) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; unfold sub_fp, fake_area; cbn [outside app]; intros x Hx; clear - Hx; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; unfold sub_fp, fake_area, SMK_STACK; cbn [outside app]; intros x Hx; clear - Hx SPAB; repeat split; lia|].
      eapply munch_weaken; [| exact MU3]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      rewrite shad_div in Hx. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF, FAKESZ in *.
      clear - Hx FFA1 FFA2 FA8 F256 SPAB. Z.div_mod_to_equations. lia. }
    assert (WM03 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    assert (BI3 : AZ_dmf_f.BINV AI L RNG st LB m SPV DCTX DST CAP FF m3) by (split; [exact AH3| split; [exact FFR03| split; [exact MU03| split; [exact WM03| exact MI3]]]]).
    (* [comment removed for export] *)
    assert (BSF : SHB + 805376 <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 543, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [clear - HX Hn LO; lia| exact I]. }
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 543, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
      clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
    assert (D3 : forall X n, (X + n <= lo \/ SPV <= X) -> (X + n <= FF \/ FF + 256 <= X) -> ((6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP)) -> 0 <= n ->
                 disjoint_from [(DSPA SPV + 400, DSPA SPV + 408); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 20)] X n).
    { intros X nn HX HF HB Hn. cbn [disjoint_from]. split; [clear - HX Hn SPAB LO; lia|]. split; [clear - HF Hn; lia|]. split; [clear - HB BSF ATR Hn; lia| exact I]. }
    assert (DS3 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) ->
                 disjoint_from [(DSPA SPV + 400, DSPA SPV + 408); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 20)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF in *.
      split; [left; clear - X0 Hn Hb ATR BOT LO SPAB; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb HF F256; Z.div_mod_to_equations; lia| exact I]. }
    assert (INLB : forall b, In b LB -> In b (FB2 FF :: LB)) by (intros b Hb; right; exact Hb).
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [exact SAV2| exact MU3| exact WM3| unfold DSAVED; cbn; unfold KHIGH in KHI; clear - SPAB LO BOT FHc BSF KHI; lia]. }
    assert (STG3 : stk bsegs m3 (DSPA SPV + 408) (SPV + -104)).
    { eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn; unfold KHIGH in KHI; clear - SPAB LO BOT FHc BSF KHI; lia]. }
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)).
    { eapply unpoisoned_munch; [| exact MU3| apply DS3; [clear - DL; lia| clear; lia| clear - DL ATR; lia| exact DCFF]].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact AID| clear; lia|].
      eapply unpoisoned_munch; [exact UD0| exact MU1| apply DS1; clear - DL ATR; lia]. }
    assert (DA3 : dctx_any m3 DCTX).
    { eapply dm_dctx_any_transport; [| exact MU3| exact WM3| apply D3; [clear - S_DC; lia| exact DCFF| exact DL| clear; lia]].
      eapply (dm_dctx_any_pres AI); [exact HPR2| exact AID|].
      eapply dm_dctx_any_transport; [exact DA| exact MU1| exact WM1| apply D1; [exact S_DC| clear; lia]]. }
    assert (DSK3 : stk bsegs m3 DST (DST + CAP)).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - destruct (B_ds HC) as [ABS' IBS]. pose proof (fk_ablk_lits _ _ ABS') as DSL.
        eapply stk_transport_disjoint; [| exact MU3| exact WM3| replace (DST + CAP - DST) with CAP by (clear; lia); apply D3; [clear - S_DS; lia| exact DSFF| clear - DSL; lia| clear - HC; lia]].
        eapply (dm_stk_pres AI); [exact HPR2| replace (DST + CAP - DST) with CAP by (clear; lia); exact IBS|].
        eapply stk_transport_disjoint; [exact DSK| exact MU1| exact WM1| replace (DST + CAP - DST) with CAP by (clear; lia); apply D1; [exact S_DS| clear - HC; lia]].
      - pose proof DSK as (D0 & D1' & _). replace (DST + CAP) with DST in D1' |- * by (clear - HC RC0; lia). apply dm_stk_empty; [exact D0| exact D1']. }
    assert (DSTB : (0 < CAP /\ ((6443008 <= DST /\ DST + CAP <= 2147446784) \/ (17594333495296 <= DST /\ DST + CAP <= ATOP))) \/ (CAP = 0 /\ DST = 0)).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC]; [left; pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X HC; lia| right].
      pose proof (DZ ltac:(clear - HC RC0; lia)) as D00. clear - HC RC0 D00. lia. }
    assert (ARO3 : aro_client RNG m3).
    { eapply aro_client_transport_gen; [exact WM03 | exact ARO | exact MU03 |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (Q1 & Q2 & Q3). destruct LY5 as (_ & _ & FA1 & FA2).
      cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, FAKESZ in *.
      clear - Q1 Q2 Q3 DL DSTB FA1 FA2 FABL ATR BOT LO. repeat split; Z.div_mod_to_equations; lia. }
    assert (AZS3 : azstk RNG m3 lo SPV).
    { assert (AZS1 : azstk RNG m1 lo SPV).
      { eapply azstk_transport; [exact AZS| exact MU1| exact WM1| | clear - LO; lia]. apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; unfold KHIGH in KHI; clear - KHI LO; lia| apply Forall_nil]. }
      assert (AZS2 : azstk RNG m2 lo SPV).
      { eapply (azstk_transport_F RNG m1 m2 [(DSPA SPV - SMK_STACK, DSPA SPV)] L); [exact AZS1| | exact WM2| | exact FAB| exact FA8| clear - FABL BOT; lia| clear - LO; lia].
        - eapply munch_weaken; [| exact MUF2]. unfold sub_fp. intros x Hx. apply (proj1 (fk_outside_app _ _ _)) in Hx. destruct Hx as [Hx1 Hx2]. apply (proj2 (fk_outside_app _ _ _)). split; [exact Hx2| exact Hx1].
        - apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH, SMK_STACK; unfold KHIGH in KHI; clear - KHI LO SPAB; lia| apply Forall_nil]. }
      destruct AZS2 as (RLOz & RHIz & Uz & Hz & W0z & ABz & Rz). exists RLOz, RHIz.
      split; [| split; [exact Hz| split; [eapply wr_at_transport; [exact W0z| exact WM3]| split; [exact ABz| exact Rz]]]].
      eapply unpoisoned_munch; [exact Uz| exact MU3|]. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF.
      unfold KHIGH in KHI. clear - KHI LO BOT RSP SPAB FL FHc ATR. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (fk_relro_C8 AI _ _ _ _ _ 0xc7fd0 0 AH3 ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as GT1.
    pose proof (fk_relro_C8 AI _ _ _ _ _ 0xc7fd8 0 AH3 ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as GT2.
    assert (GOT3 : rw_cells bsegs m3 0xc7fd0 [C8 wz; C8 wz]).
    { apply (proj2 (rw_cells_app bsegs m3 0xc7fd0 [C8 wz] [C8 wz])). split; [exact GT1|]. cbn [cells_size csize Nat.add]. exact GT2. }
    clear GT1 GT2.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20853); C8 (Z_to_bv 64 0x84750)] 224 junk [C8 (Z_to_bv 64 (fflag L 2 FF))] [104; 12; 108]%nat) in FFC3; [| reflexivity].
    cbn [mk_CB_cells app] in FFC3.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20853); C8 (Z_to_bv 64 0x84750); CB 104 (firstn 104 junk)] _) FFC3) as [XA3 XBC].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XBC.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 12 (firstn 12 (skipn 104 junk))] _) XBC) as [XB3 XC3].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XB3, XC3.
    match type of XB3 with rw_cells _ _ ?a _ => replace a with (FF + 128) in XB3 by (clear; lia) end.
    match type of XC3 with rw_cells _ _ ?a _ => replace a with (FF + 140) in XC3 by (clear; lia) end.
    clear XBC FFC3.
    (* [comment removed for export] *)
    assert (AWF : aappW [(DSPA SPV, DSPA SPV + 408)]) by (apply Forall_cons; [cbn [fst snd]; right; unfold KHIGH; unfold KHIGH in KHI; clear - KHI LO SPAB; lia| apply Forall_nil]).
    assert (DF : forall X n, (X + n <= DSPA SPV \/ DSPA SPV + 408 <= X) -> disjoint_from [(DSPA SPV, DSPA SPV + 408)] X n) by (intros X n H; cbn [disjoint_from]; split; [exact H| exact I]).
    assert (TRX : forall mX, munch [(DSPA SPV, DSPA SPV + 408)] m3 mX -> wmono bsegs m3 mX -> mem_inv bsegs mX ->
       AZ_dmf_f.BINV AI L RNG st LB m SPV DCTX DST CAP FF mX
       /\ rw_cells bsegs mX (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
       /\ stk bsegs mX (DSPA SPV + 408) (SPV + -104)
       /\ rw_cells bsegs mX FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20853); C8 (Z_to_bv 64 0x84750); CB 104 (firstn 104 junk)]
       /\ rw_cells bsegs mX (FF + 128) [CB 12 (firstn 12 (skipn 104 junk))]
       /\ rw_cells bsegs mX (FF + 140) [CB 108 (firstn 108 (skipn 12 (skipn 104 junk))); C8 (Z_to_bv 64 (fflag L 2 FF))]
       /\ stk bsegs mX lo (DSPA SPV)
       /\ rw_cells bsegs mX (Z.shiftr FF 3 + SHB) DSHC
       /\ unpoisoned mX DCTX (DCTX + 95992)
       /\ stk bsegs mX DST (DST + CAP)
       /\ rw_cells bsegs mX 0xc7fd0 [C8 wz; C8 wz]
       /\ aro_client RNG mX /\ dctx_any mX DCTX /\ azstk RNG mX lo SPV
       /\ rw_cells bsegs mX (fflag L 2 FF) [C1 (Z_to_bv 8 1)]).
    { intros mX MUx WMx MIx.
      assert (AHx : AHEAP AI L RNG st (FB2 FF :: LB) mX).
      { eapply (AI_frame AI); [exact AH3| exact MUx| exact WMx|]. constructor; [cbn [fst snd]; left; left; cbn; unfold KEND in SPK; clear - BOT LO SPAB SPK; lia| constructor]. }
      split.
      { split; [exact AHx|]. split.
        { eapply ffr_pres_trans; [exact FFR03|]. apply dm_ffr_pres_mono_nil1. apply (dm_ffr_pres_tl [] (FB2 FF)).
          eapply (fk_ffr_stack AI); [exact AH3| exact MUx| exact WMx| constructor; [cbn [fst snd]; clear - BOT LO SPAB; lia| constructor]]. }
        split; [eapply munch_trans; [exact MU03| eapply munch_weaken; [| exact MUx]; unfold sub_fp, fake_area; cbn [outside app]; intros x Hx; clear - Hx SPAB; lia]|].
        split; [exact (wmono_trans _ _ _ _ WM03 WMx)| exact MIx]. }
      split; [eapply rw_cells_transport; [exact SAV3| exact MUx| exact WMx| apply DF; cbn; clear - SPAB; lia]|].
      split; [eapply stk_transport_disjoint; [exact STG3| exact MUx| exact WMx| apply DF; clear; lia]|].
      split; [eapply rw_cells_transport; [exact XA3| exact MUx| exact WMx| apply DF; cbn; clear - SPAB FHc BOT LO; lia]|].
      split; [eapply rw_cells_transport; [exact XB3| exact MUx| exact WMx| apply DF; cbn; clear - SPAB FHc BOT LO; lia]|].
      split; [eapply rw_cells_transport; [exact XC3| exact MUx| exact WMx| apply DF; cbn; clear - SPAB FHc BOT LO; lia]|].
      split; [eapply stk_transport_disjoint; [exact STL3| exact MUx| exact WMx| apply DF; clear - LOS; lia]|].
      split; [eapply rw_cells_transport; [exact XS3| exact MUx| exact WMx| apply DF; cbn; clear - SPAB BSF BOT LO ATR; lia]|].
      split; [eapply unpoisoned_munch; [exact UD3| exact MUx| apply DF; rewrite !shad_div; unfold ASHOFF; clear - DL ATR BOT LO SPAB; Z.div_mod_to_equations; lia]|].
      split; [eapply (AZ_dmf_f.dsk_keep DST CAP RC0); [exact DSK3| exact MUx| exact WMx| intros HC; apply DF; clear - S_DS SPAB LO; lia]|].
      split; [eapply rw_cells_transport; [exact GOT3| exact MUx| exact WMx| apply DF; cbn; clear - S_GT SPAB LO; lia]|].
      split; [eapply aro_client_transport; [exact ARO3| exact MUx| exact WMx| exact AWF]|].
      split; [eapply dm_dctx_any_transport; [exact DA3| exact MUx| exact WMx| apply DF; clear - S_DC SPAB LO; lia]|].
      split; [eapply azstk_transport; [exact AZS3| exact MUx| exact WMx| exact AWF| clear - LO; lia]|].
      destruct (FFLAG _ _ _ _ _ 2 FF 256 AHx ltac:(left; reflexivity)) as (X & _). exact X. }
    assert (RDT : 0 <= DST < 2^47) by (destruct (Z.eq_dec DST 0) as [Hd|Hd]; [clear - Hd RDST RC0; lia| pose proof (DNN Hd) as X; clear - X RDST RC0; lia]).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [CB 328 jA; C8 wz; C8 wz] 32 jB [C8 wz; CB 16 jC'; C8 (Z_to_bv 64 FF)] [8; 8; 8; 8]%nat) in FRA3; [| reflexivity].
    cbn [mk_CB_cells app] in FRA3.
    destruct (cb8_as_c8 bsegs _ _ [CB 328 jA; C8 wz; C8 wz] _ _ FRA3) as [w344 FRA3a]. clear FRA3. cbn [app] in FRA3a.
    destruct (cb8_as_c8 bsegs _ _ [CB 328 jA; C8 wz; C8 wz; C8 w344] _ _ FRA3a) as [w352 FRA3b]. clear FRA3a. cbn [app] in FRA3b.
    destruct (cb8_as_c8 bsegs _ _ [CB 328 jA; C8 wz; C8 wz; C8 w344; C8 w352] _ _ FRA3b) as [w360 FRA3c]. clear FRA3b. cbn [app] in FRA3c.
    destruct (cb8_as_c8 bsegs _ _ [CB 328 jA; C8 wz; C8 wz; C8 w344; C8 w352; C8 w360] _ _ FRA3c) as [w368 FRA3]. clear FRA3c. cbn [app] in FRA3.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (dm_fmt gp tp FR fc SPV lo SP16 LOS LOC RNG RSTK); [exact FRA3| exact MI3| exact UD3| exact RDS| clear - DL; lia| clear - DL ATR; lia| exact RD8]. }
    cbv beta. intros ms' (m4 & -> & MU4 & WM4 & MI4 & FRA4).
    assert (MU4w : munch [(DSPA SPV, DSPA SPV + 408)] m3 m4) by (eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    pose proof (TRX m4 MU4w WM4 MI4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DA4 & _).
    pose proof DA4 as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                      _ & _ & _ & _ & _ & H5 & H5OK & _).
    clear DA4.
    destruct (Z_le_gt_dec 5 size) as [S5|S5].
    { (* [comment removed for export] *)
      assert (NZ : 0 < zlen src) by (clear - S5 NLEN; lia).
      eapply evtF_cut.
      { eapply (dm_go gp tp FR fc SPV lo SP16 LOS LOC RNG RSTK); [exact FRA4| exact MI4| exact H5| exact H5OK| exact RD| clear - DL; lia| clear - DL ATR; lia| clear - S5 N40; lia]. }
      cbv beta. intros ms' (m5 & -> & MU5 & WM5 & MI5 & FRA5).
      apply (rw_cells_merge bsegs _ _ [CB 328 jA; C8 wz; C8 wz; C8 (Z_to_bv 64 FF)] [C8 w352] _) in FRA5. cbn [app cells_size csize Nat.add] in FRA5.
      apply (rw_cells_merge bsegs _ _ [CB 328 jA; C8 wz; C8 wz; C8 (Z_to_bv 64 FF); CB 8 (cells_bytes [C8 w352]); C8 (Z_to_bv 64 (SHB + (DCTX + 30104) / 8))] [C8 w368] _) in FRA5.
      cbn [app cells_size csize Nat.add] in FRA5.
      eapply evtF_cut.
      { eapply (dm_setup gp tp FR fc SPV lo SP16 LOS LOC RNG RSTK); [exact FRA5| exact MI5| exact RD0| exact RD1| exact RD8]. }
      cbv beta. intros ms' (m6 & u5 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u19 & u29 & v8 & v16 & v24 & v32 & vfl & i0 & -> & MU6 & WM6 & MI6 & FRA6).
      assert (MU6w : munch [(DSPA SPV, DSPA SPV + 408)] m3 m6).
      { eapply munch_trans; [exact MU4w|]. eapply munch_trans; [eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia| exact MU6]. }
      pose proof (TRX m6 MU6w (wmono_trans _ _ _ _ WM4 (wmono_trans _ _ _ _ WM5 WM6)) MI6) as (BI5 & SAV5 & STG5 & XA5 & XB5 & XC5 & STL5 & XS5 & UD5 & DSK5 & GOT5 & ARO5 & DA5 & AZS5 & XL5).
      clear TRX MU4 MU5 MU6 WM4 WM5 WM6 MU4w MU6w.
      pose proof BI5 as (AH5 & FFR5 & MU05 & WM05 & _).
      pose proof (ARS NZ) as (SL & US0 & RSa & RSb). pose proof (fk_ablk_lits _ _ SL) as SLL.
      assert (INS : ainblk LB SRC (zlen src)).
      { destruct (AIS NZ) as [IB|[IM1 IM2]]; [exact IB| unfold AIMG_HI in IM2; exfalso; clear - IM2 SLL NZ ATR; lia]. }
      assert (SRFF : SRC + zlen src <= FF \/ FF + 256 <= SRC) by (exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 INS ltac:(clear - NZ; lia))).
      pose proof (G_ff_of SRC SRFF) as G_ff. clear G_ff_of.
      assert (B_sr : ablk SRC (SRC + zlen src) /\ (0 < zlen src -> ainimg LB SRC (zlen src))) by (split; [exact SL| exact AIS]).
      assert (R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src))) by (split; [exact RSa| exact RSb]).
      assert (FFR5w : ffr_pres [(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] LB m m6).
      { eapply dm_ffr_pres_weaken; [exact FFR5|]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
      assert (AW3 : aappW [(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)]).
      { unfold aappW. apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - DL ATR; lia|].
        apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - DSTB ATR; lia|].
        apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; unfold KHIGH in KHI; clear - KHI LO; lia| apply Forall_nil]. }
      assert (SB5 : bytes_at bsegs m6 SRC (map (Z_to_bv 8) src)).
      { eapply (dm_fcall_bytes_pres AI FHL); [exact AH| rewrite length_map; exact INS| | exact MU05| exact FFR5w| exact SB].
        rewrite length_map. cbn [disjoint_from]. clear - SR_DC D_SR S_SR NZ LO. repeat split; lia. }
      assert (US5 : unpoisoned m6 SRC (SRC + zlen src)).
      { eapply (dm_fcall_unp_pres AI FHL); [exact AH| exact INS| exact NZ| unfold KEND; clear - SLL ATR; lia| exact AW3| exact MU05| exact FFR5w| exact US0]. }
      assert (UDS5 : 0 < CAP -> unpoisoned m6 DST (DST + CAP)).
      { intros HC. destruct (ADST HC) as (ARx & _ & IBx). pose proof (ARx HC) as (_ & UDS0 & _).
        eapply (dm_fcall_unp_pres AI FHL); [exact AH| exact IBx| exact HC| unfold KEND; clear - DSTB ATR HC; lia| exact AW3| exact MU05| exact FFR5w| exact UDS0]. }
      assert (SI5 : AZ_dmf_f.SINV RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV (DSPA SPV) lo DCTX DST CAP SRC src FF (fflag L 2 FF) m6).
      { split; [exact SAV5|]. split; [exact STG5|]. split; [eexists; exact XA5|]. split; [eexists; exact XC5|]. split; [exact SB5|]. split; [exact US5|].
        split; [exact UD5|]. split; [exact UDS5|]. split; [exact GOT5|]. split; [exact ARO5| exact AZS5]. }
      pose proof (AZ_dmf_f.dinv_of AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV (DSPA SPV) lo DCTX DST CAP SRC src FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) G_flg FFLAG
                    m6 0 v8 v16 v24 v32 vfl i0 jC' _ BI5 SI5 STL5 FRA6 XB5 eq_refl XS5 DSK5 DA5) as DI5.
      assert (AI5 : AZ_dmf_b.AINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) m6 0 size 0).
      { split; [exact DI5|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact N0|]. split; [clear - RC0; lia|].
        intros rr D. unfold decompress_ok. replace (CAP - 0) with CAP in D by (clear; lia). exact D. }
      (* [comment removed for export] *)
      pose proof (AZ_dmf_a.p_tail AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_ds RSTK RI R_dc R_ds R_ff LBH) as PTAIL.
      pose proof (AZ_dmf_b.p_xD AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH PTAIL) as PXD.
      pose proof (AZ_dmf_b.p_exit AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH PTAIL) as PEXIT.
      pose proof (AZ_dmf_b.p_x72 AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH PTAIL) as PX72.
      pose proof (AZ_dmf_b.p_res AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH ERRCODE PTAIL) as PRES.
      pose proof (AZ_dmf_b.p_res0 AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH ERRCODE PTAIL) as PRES0.
      pose proof (AZ_dmf_b.dinv_frame AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RS0 RS1 RC0 DNULL DNN RDST S_DC S_DS S_SR D_DC D_SR GT_DS G_lo G_ff G_flg B_dc B_sr B_ds R_ds PTAIL) as DFRAME.
      pose proof (AZ_dmf_g.p_fend AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds LBH PRES PRES0 FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL XXHDIG) as PFEND.
      pose proof (AZ_dmf_h.p_after AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK NLEN N40 RC0 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES PRES0 rng_fs FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL GETCB DZ DBLOCK XXHUPD MEMMOVE MEMSET PFEND) as PAFTER.
      pose proof (AZ_dmf_h2.p_raw AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 OK NLEN RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES PRES0 rng_fs FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL GETCB DZ DBLOCK XXHUPD MEMMOVE MEMSET PFEND PAFTER) as PRAW.
      pose proof (AZ_dmf_h2b.p_rle AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES PRES0 rng_fs FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL GETCB DZ DBLOCK XXHUPD MEMMOVE MEMSET PFEND PAFTER) as PRLE.
      pose proof (AZ_dmf_h3.p_blocks AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES PRES0 rng_fs FHL FFLAG ASH RFS TP SPT RSTKT AH_dc AH_sr AH_ds TBL GETCB DZ DBLOCK XXHUPD MEMMOVE MEMSET PFEND PAFTER PRAW PRLE) as PBLK.
      pose proof (AZ_dmf_f.p_gcb AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 OK NLEN N40 RC0 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES0 FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL GETCB PBLK) as PGCB.
      pose proof (AZ_dmf_f3.p_pcs AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds LBH rng_fs FHL RFS RSTKT AH_dc AH_sr AH_ds TBL PGCB) as PPCS.
      pose proof (AZ_dmf_f2.p_gfh AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 OK NLEN RC0 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES0 rng_fs FHL FFLAG ASH RFS TP SPT RSTKT AH_dc AH_sr AH_ds TBL TBLL DECODEFH PPCS) as PGFH.
      pose proof (AZ_dmf_e.p_hsz AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD8 OK N0 NLEN N40 RS0 RS1 DNULL DNN S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH PRES0 PGFH) as PHSZ.
      pose proof (AZ_dmf_d.p_frame AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK RI R_src R_dc R_ds R_ff LBH DBEGIN CHECKCONT AH_dc PXD DFRAME PHSZ) as PFRAME.
      pose proof (AZ_dmf_c.p_head AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 OK N0 NLEN N40 RS0 RS1 DNULL DNN S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff B_sr B_ds R_src R_ds PXD PX72 PEXIT) as PHEAD.
      (* [comment removed for export] *)
      assert (PLOOP : forall (n : nat) sz, sz < Z.of_nat n -> forall mm off tot (x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 : word),
          AZ_dmf_b.AINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) mm off sz tot ->
          evtF bsegs RNG (zd_dmf_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP src size lo m)
            (MS (mkR x1 (Z_to_bv 64 (DSPA SPV)) gp tp (Z_to_bv 64 8) (Z_to_bv 64 (-120)) x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (DSPA SPV)) x10 (Z_to_bv 64 5) x12 x13 x14
                     (Z_to_bv 64 25481893) (Z_to_bv 64 1) (Z_to_bv 64 4) (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) (Z_to_bv 64 DCTX) (Z_to_bv 64 SHB)
                     (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31)
                FR (Z_to_bv 64 0x84a88) fc None mm (seg_rom bsegs))).
      { induction n as [|n IH]; intros sz Hn mm off tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 AIV.
        - exfalso. pose proof AIV as (_ & _ & _ & RSZ0 & _). clear - Hn RSZ0. lia.
        - eapply PHEAD; [exact AIV| |].
          + intros off' sz' q1 q7 q10 q12 q13 q14 q19 q25 q27 q29 q31 LT AIV'. eapply (IH sz'); [clear - Hn LT; lia| exact AIV'].
          + intros q1 q7 q10 q12 q13 q14 q19 q25 q27 q29 q31 NSK. eapply PFRAME; [exact AIV| exact NSK|].
            intros m' off' sz' tot' q1' q7' q10' q12' q13' q14' q19' q25' q27' q29' q31' LT AIV'. eapply (IH sz'); [clear - Hn LT; lia| exact AIV']. }
      eapply (AZ_dmf_b.p_top AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 DNULL DNN S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH);
        [exact AI5| intros; eapply (PLOOP (S (Z.to_nat size)) size); [clear - N0; lia| exact AI5]]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (dm_empty gp tp FR fc SPV lo SP16 LOS LOC RNG RSTK); [exact FRA4| exact MI4| exact H5| exact H5OK| exact RD| clear - DL; lia| clear - DL ATR; lia| exact RDT| clear - N0 S5; lia]. }
    cbv beta. intros ms' (m5 & q10 & -> & MU5 & WM5 & MI5 & FRA5).
    assert (MU5w : munch [(DSPA SPV, DSPA SPV + 408)] m3 m5).
    { eapply munch_trans; [exact MU4w| eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]. }
    pose proof (TRX m5 MU5w (wmono_trans _ _ _ _ WM4 WM5) MI5) as (BI5 & SAV5 & STG5 & XA5 & XB5 & XC5 & STL5 & XS5 & UD5 & DSK5 & GOT5 & ARO5 & DA5 & AZS5 & XL5).
    clear TRX MU4 MU5 WM4 WM5 MU4w MU5w.
    apply (rw_cells_merge bsegs _ _ [] [CB 328 jA; C8 wz; C8 wz] _) in FRA5. cbn [app cells_size csize Nat.add] in FRA5.
    apply (rw_cells_merge bsegs _ _ [CB 344 (cells_bytes [CB 328 jA; C8 wz; C8 wz]); C8 (Z_to_bv 64 FF)] [C8 w352; C8 _; C8 (Z_to_bv 64 DST); C8 wz; CB 16 jC'; C8 (Z_to_bv 64 FF)] []) in FRA5.
    cbn [app cells_size csize Nat.add] in FRA5.
    destruct (rw_cells_forget _ _ _ _ XS5) as [shb XS']. cbn [cells_size csize Nat.add] in XS'.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 108 _] [C8 (Z_to_bv 64 (fflag L 2 FF))]) XC5) as [_ XP]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XP.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 248) in XP by (clear; lia) end.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XA5) as [XM _].
    replace (Z_to_bv 64 (if size =? 0 then 0 else -72)) with (Z_to_bv 64 (if size =? 0 then 0 else 18446744073709551544))
      by (destruct (size =? 0); [reflexivity| apply Z_to_bv_eqm; reflexivity]).
    assert (RR : 0 <= (if size =? 0 then 0 else 18446744073709551544) < 2^64) by (destruct (size =? 0); clear; lia).
    assert (RM : zd_is_error (if size =? 0 then 0 else 18446744073709551544) = false -> decompress_ok src size CAP (if size =? 0 then 0 else 18446744073709551544)).
    { destruct (size =? 0) eqn:ES; intros E; [apply Z.eqb_eq in ES; rewrite ES; unfold decompress_ok; apply DM_end| vm_compute in E; discriminate E]. }
    destruct (Z_lt_le_dec 0 (zlen src)) as [NZ|Z0].
    { pose proof (ARS NZ) as (SL & US0 & RSa & RSb). pose proof (fk_ablk_lits _ _ SL) as SLL.
      assert (INS : ainblk LB SRC (zlen src)).
      { destruct (AIS NZ) as [IB|[IM1 IM2]]; [exact IB| unfold AIMG_HI in IM2; exfalso; clear - IM2 SLL NZ ATR; lia]. }
      assert (SRFF : SRC + zlen src <= FF \/ FF + 256 <= SRC) by (exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 INS ltac:(clear - NZ; lia))).
      pose proof (G_ff_of SRC SRFF) as G_ff. clear G_ff_of.
      assert (B_sr : ablk SRC (SRC + zlen src) /\ (0 < zlen src -> ainimg LB SRC (zlen src))) by (split; [exact SL| exact AIS]).
      assert (R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src))) by (split; [exact RSa| exact RSb]).
      pose proof (AZ_dmf_a.p_tail AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) RD0 RD1 RD8 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_ds RSTK RI R_dc R_ds R_ff LBH) as PTAIL.
      eapply (AZ_dmf_b.p_stub AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP SRC src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF)
                RD0 RD1 RD8 OK N0 NLEN N40 RS0 RS1 RC0 RC40 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds RSTK R_src R_dc R_ds R_ff LBH PTAIL
                m5 _ _ _ _ shb);
        [exact BI5| exact SAV5| exact FRA5| exact STL5| exact STG5| exact XM| exact XP| exact XL5| exact XS'| exact DA5| exact DSK5| exact RR| exact RM]. }
    (* [comment removed for export] *)
    assert (ZL : zlen src = 0) by (clear - Z0; lia).
    assert (EXV : 4096 <= FF /\ FF + zlen src < 2^47 /\ (FF + zlen src <= lo \/ SPV <= FF) /\ (DST + CAP <= FF \/ FF + zlen src <= DST)
                  /\ (FF + zlen src <= DCTX \/ DCTX + 95992 <= FF) /\ (FF + zlen src <= FF \/ FF + 256 <= FF)).
    { rewrite ZL. clear - FL FHc ATR BOT RLO LO DSFF DCFF DNULL DNN RC0. repeat split; lia. }
    destruct EXV as (V0 & V1 & V_S & V_D & V_DC & V_FF).
    pose proof (G_ff_of FF V_FF) as G_ff. clear G_ff_of.
    assert (B_srv : ablk FF (FF + zlen src) /\ (0 < zlen src -> ainimg LB FF (zlen src))).
    { rewrite ZL. split; [clear - FH; unfold ablk in *; lia| intros H; exfalso; clear - H; lia]. }
    assert (R_srcv : rng RNG FF (zlen src) /\ rng RNG (shad FF) (shspan FF (zlen src))).
    { rewrite ZL. split; [eapply rng_sub'; [exact RFF| clear; lia]| eapply rng_sub'; [exact RSFF| unfold shspan; clear - F256; Z.div_mod_to_equations; lia]]. }
    pose proof (AZ_dmf_a.p_tail AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP FF src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF)
                  RD0 RD1 RD8 V0 V1 RC0 RC40 DNULL DNN RDST S_DC S_DS V_S S_GT D_DC V_D V_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_ds RSTK RI R_dc R_ds R_ff LBH) as PTAIL.
    eapply (AZ_dmf_b.p_stub AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (DSPA SPV) lo DCTX DST CAP FF src size FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF)
              RD0 RD1 RD8 OK N0 NLEN N40 V0 V1 RC0 RC40 DNULL DNN RDST S_DC S_DS V_S S_GT D_DC V_D V_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_srv B_ds RSTK R_srcv R_dc R_ds R_ff LBH PTAIL
              m5 _ _ _ _ shb);
      [exact BI5| exact SAV5| exact FRA5| exact STL5| exact STG5| exact XM| exact XP| exact XL5| exact XS'| exact DA5| exact DSK5| exact RR| exact RM].
  Qed.
End Thm.
End CANSEC1.
