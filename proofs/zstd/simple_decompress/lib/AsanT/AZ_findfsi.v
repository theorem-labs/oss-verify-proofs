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
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_frame_iface AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c AZ_findfsi_d AZ_findfsi_e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma fs_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)].
Proof.
  intros m R. split; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Definition FSH00 : list cell :=
  [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma shadow32_c1sA : forall (m : amem) s,
  rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m s FSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 176 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition FSPA : Z := (SPV - 160) - (SPV - 160) mod 32.
  Lemma fspa_props : SPV - 176 <= FSPA <= SPV - 160 /\ FSPA mod 32 = 0 /\ (SPV + -160) - (SPV + -160) mod 2^5 = FSPA.
  Proof. unfold FSPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma fs_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] ->
    rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x84130) (Z_to_bv 64 FSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 FSPA)
                     (Z_to_bv 64 160) (Z_to_bv 64 0xcfcf8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a3 a0 a1 a2 s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3f190) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 160, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' FSPA [CB 56 jA]
        /\ stk bsegs m' lo FSPA /\ stk bsegs m' (FSPA + 56) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x840b4) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof fspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 160, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (FSPA + 56) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (FSPA + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56 in STL, FRA. replace (FSPA + 56 - 56) with FSPA in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma fs_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xa3 : word) m (FF FLG FSIP SRCo size : Z)
      (j0 j1 j2 : word) (junk jA : list byte),
    rw_cells bsegs m FSPA [CB 56 jA] -> stk bsegs m lo FSPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    mem_inv bsegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 -> rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    evtF bsegs RNG (fun ms' => exists m' jA' y16 y17,
        ms' = MS (mkR (Z_to_bv 64 0x84130) (Z_to_bv 64 FSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 FSPA)
                     (Z_to_bv 64 8) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x840b4) xa3 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 18446744073709551601) y16 y17
                     (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 SRCo) (Z_to_bv 64 size) s6 s7 s8
                     (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x84200) fc None m' (seg_rom bsegs)
        /\ munch [(FSPA + 48, FSPA + 56); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' FSPA [CB 48 jA'; C8 (Z_to_bv 64 FF)] /\ stk bsegs m' lo FSPA
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 224 junk; C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) FSH0)
      (MS (mkR (Z_to_bv 64 0x84130) (Z_to_bv 64 FSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 FSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               xa3 (Z_to_bv 64 FSIP) (Z_to_bv 64 SRCo) (Z_to_bv 64 size) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x84130) fc None m (seg_rom bsegs)).
  Proof.
    intros until jA. intros FRA STL FFC SHF MI FH FC F256 RF RSF.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof fspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow32_c1sA in SHF. unfold FSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(FSPA + 48, FSPA + 56); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [48; 8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    do 4 zstep.                              (* [comment removed for export] *)
    do 2 zstep.                              (* [comment removed for export] *)
    do 2 zstep.                              (* [comment removed for export] *)
    do 2 zstep.                              (* [comment removed for export] *)
    do 2 zstep.                              (* [comment removed for export] *)
    zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                              (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [eassumption|].
    split; [exact FRA|]. split; [exact STL|]. split; [exact FFC| unfold FSH0; exact SHF].
  Qed.
End S.

(* [comment removed for export] *)
Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM2K : forall k, Z.of_nat k < 4096 -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis GETFH : zd_getfh_stmtA AI rng_fs.
  Hypothesis GETCB : zd_getcblock_stmtA.

  Theorem zd_findfsi_proofA : zd_findfsi_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV FSIP SRC src off size cs0 lo
           SB OK OFF0 N5 N40 OFS SRC0 SRCE FC0 FSZ ST LO SFS KHF F47 SSR SFSR AFP ARO ARS AIS F8 AFS MI TP -> -> -> ->.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (fs_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [G1 G2].
    assert (LOS : lo <= SPV - 176 - 4096) by lia.
    assert (LOC : ATOP <= lo) by lia.
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (fspa_props SPV SP16) as (SPAB & SPA32 & _).
    unfold APZD_FINDFSI.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fs_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOS LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    clear C0 GOT RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
    (* [comment removed for export] *)
    pose proof (ASH 2 ltac:(lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM2K (Z.to_nat (4096 - 2)) ltac:(lia)) as SMC. unfold stack_malloc_2k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (FSPA SPV)) by lia;
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F256 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (FSPA SPV)) in ST2, HPR2, MUF2 by lia.
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SAV1 ltac:(left; left; cbn; lia)) as SAV2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fs_hdr gp tp s6 s7 s8 s9 s10 FR fc SPV lo SP16 LOS LOC RNG RSTK);
        [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact MI2| exact FH| exact FC| exact F256| exact RFF| exact RSFF]. }
    cbv beta. intros ms' (m3 & jA' & y16 & y17 & -> & MU3 & WM3 & MI3 & FRA3 & STL3 & FFC3 & SHF3).
    (* [comment removed for export] *)
    assert (NZ : 0 < zlen src) by (clear - OFS N5 OFF0; lia).
    pose proof (ARS NZ) as (SBK & US0 & RS1 & RS2). pose proof (fk_ablk_lits _ _ SBK) as SL.
    pose proof AFS as (UP0 & RP1 & RP2). assert (PL : 17594333495296 <= FSIP /\ FSIP + 32 <= 2^47) by (unfold KHIGH in KHF; clear - KHF F47; lia).
    pose proof (fk_ablk_lits _ _ FH) as FL.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (BSF : SHB + 805376 <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (DPF : FSIP + 24 <= FF \/ FF + 256 <= FSIP) by (clear - FHc LOC LO SPAB SFS; lia).
    assert (SRCAP : SRC + zlen src <= FF \/ FF + 256 <= SRC).
    { destruct (AIS NZ) as [IB|[IM1 IM2]]; [exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 IB ltac:(lia))| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia]. }
    destruct (FFLAG _ _ _ _ _ 2 FF 256 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
    pose proof (fk_ablk_lits _ _ LBK) as LL. pose proof (LAP _ ltac:(left; reflexivity)) as LFF. cbn [ab_addr ab_size] in LFF.
    assert (G_lo : ATOP + 4096 <= lo /\ lo <= FSPA SPV - 4320 /\ SPV - 176 <= FSPA SPV <= SPV - 160 /\ FSPA SPV mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0).
    { unfold KEND in SPK. clear - BOT LO SPAB SPA32 SPK SP16. repeat split; lia. }
    assert (G_fsip : (17594333495296 <= FSIP /\ FSIP + 32 <= 2^47) /\ SPV <= FSIP) by (split; [exact PL| exact SFS]).
    assert (G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP)) by (split; [exact SBK| split; [exact SSR| exact SFSR]]).
    assert (G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ Z.shiftr FF 3 + SHB = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                   /\ (FSIP + 24 <= FF \/ FF + 256 <= FSIP) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC)).
    { split; [exact FH|]. split; [exact F256|]. split; [exact FC|]. split; [unfold shad, ASHOFF; lia|]. split; [exact FFA1|]. split; [exact FFA2|].
      split; [clear - DPF; lia| exact SRCAP]. }
    assert (G_flg : fflag L 2 FF = fflag L 2 FF /\ ablk (fflag L 2 FF) (fflag L 2 FF + 1) /\ fflag L 2 FF + 1 <= ATOP /\ (al_fake L <= fflag L 2 FF /\ fflag L 2 FF + 1 <= al_fake L + FAKESZ)
                    /\ (forall b, In b (FB2 FF :: LB) -> fflag L 2 FF + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L 2 FF)
                    /\ (FSIP + 24 <= fflag L 2 FF \/ fflag L 2 FF + 1 <= FSIP)).
    { split; [reflexivity|]. split; [exact LBK|]. split; [exact LTOP|]. split; [exact LFA|]. split; [exact LAP|].
      clear - LTOP LOC LO SPAB SFS. lia. }
    assert (R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src))) by (split; [exact RS1| exact RS2]).
    assert (R_fsip : rng RNG FSIP 24 /\ rng RNG (shad FSIP) (shspan FSIP 24)) by (split; [exact RP1| exact RP2]).
    assert (R_ff : rng RNG FF 256 /\ rng RNG (Z.shiftr FF 3 + SHB) 32 /\ rng RNG (fflag L 2 FF) 1).
    { split; [exact RFF|]. split; [replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia); exact RSFF| exact RL]. }
    (* [comment removed for export] *)
    assert (FFR02 : ffr_pres [] LB m m2).
    { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2. }
    assert (FFR03 : ffr_pres [(FSIP, FSIP + 24)] LB m m3).
    { apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m m2 m3 2 FF 256 (Z.shiftr FF 3 + SHB) 32 [] [(FSIP, FSIP + 24); (FSPA SPV + 48, FSPA SPV + 56); (FF, FF + 24)]);
        [ exact AH2 | exact LBH | exact FH | clear - F256; Z.div_mod_to_equations; lia | unfold shad, ASHOFF; lia | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia| left; clear - PL SFS BOT LO SPAB; lia]|];
          constructor; [cbn [fst snd]; split; [clear; lia| left; unfold KEND in SPK; clear - BOT LO SPAB SPK; lia]|];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact FH | clear; lia]]] | constructor]
        | constructor
        | exact FFR02
        | cbn [app]; eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WM3 ]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU03 : munch ([(FSIP, FSIP + 24); (SPV - 4672, SPV)] ++ fake_area L) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx SPAB LO; cbn [outside app fake_area] in *; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx SPAB LO; cbn [outside app fake_area] in *; unfold SMK_STACK in *; lia|].
      eapply munch_weaken; [| exact MU3]; intros x Hx; clear - Hx FFA1 FFA2 SPAB LO BOT F256 FHb FA8;
        cbn [outside app fake_area] in *; rewrite ?shad_div in *; rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold FAKESZ, ASHOFF in *;
        Z.div_mod_to_equations; lia. }
    assert (WM03 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn [fst snd]; left; left; cbn; unfold KEND in SPK; clear - BOT LO SPAB SPK LY3 SPT; lia|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd] | constructor].
      replace (Z.shiftr FF 3 + SHB + 32 - (Z.shiftr FF 3 + SHB)) with 32 by (clear; lia). replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F256; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (BI3 : AZ_findfsi_a.BINV AI L RNG st LB m SPV FSIP FF m3).
    { split; [exact AH3|]. split; [exact FFR03|]. split; [exact MU03|]. split; [exact WM03| exact MI3]. }
    (* [comment removed for export] *)
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 160, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [clear - HX Hn LO; lia| exact I]. }
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 160, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
      clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
    assert (D3 : forall X n, (X + n <= lo \/ SPV <= X) -> (X + n <= FF \/ FF + 256 <= X) -> ((6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP)) -> 0 <= n ->
                 disjoint_from [(FSPA SPV + 48, FSPA SPV + 56); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] X n).
    { intros X nn HX HF HB Hn. cbn [disjoint_from]. split; [clear - HX Hn SPAB LO; lia|]. split; [clear - HF Hn; lia|]. split; [clear - HB BSF ATR Hn; lia| exact I]. }
    assert (DS3 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) ->
                 disjoint_from [(FSPA SPV + 48, FSPA SPV + 56); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF in *.
      split; [left; clear - X0 Hn Hb ATR BOT LO SPAB; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb HF F256; Z.div_mod_to_equations; lia| exact I]. }
    assert (INLB : forall b, In b LB -> In b (FB2 FF :: LB)) by (intros b Hb; right; exact Hb).
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [exact SAV2| exact MU3| exact WM3| unfold FSAVED; cbn; unfold KHIGH in KHI; clear - SPAB LO BOT FHc BSF KHI; lia]. }
    assert (STG3 : stk bsegs m3 (FSPA SPV + 56) (SPV + -104)).
    { eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn; unfold KHIGH in KHI; clear - SPAB LO BOT FHc BSF KHI; lia]. }
    assert (XL3 : rw_cells bsegs m3 (fflag L 2 FF) [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_transport; [exact XL2| exact MU3| exact WM3| cbn; clear - LFF LL LTOP LOC LO SPAB BSF ATR; lia]. }
    destruct (rw_cells_forget _ _ _ _ FC0) as [j24 FC0']. rewrite FSZ in FC0'.
    assert (FC3 : rw_cells bsegs m3 FSIP [CB 24 j24]).
    { eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; clear - SFS SPAB DPF PL BSF; lia].
      eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2); [| left; left; cbn; clear - SFS SPAB PL; lia].
      eapply rw_cells_transport; [exact FC0'| exact MU1| exact WM1| apply D1; [right; exact SFS| clear; lia]]. }
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src)).
    { eapply bytes_at_transport; [| exact MU3| rewrite length_map; apply D3; [exact SSR| exact SRCAP| exact SL| clear; lia]].
      destruct (AIS NZ) as [IB|[IM1 IM2]]; [| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      eapply (fk_bytes_pres AI); [exact HPR2| rewrite length_map; exact IB|].
      eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply D1; [exact SSR| clear; lia]]. }
    assert (US3 : unpoisoned m3 SRC (SRC + zlen src)).
    { eapply unpoisoned_munch; [| exact MU3| apply DS3; [clear - SL; lia| clear - NZ; lia| clear - SL ATR; lia| exact SRCAP]].
      destruct (AIS NZ) as [IB|[IM1 IM2]]; [| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IB| clear - NZ; lia|].
      eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR NZ; lia]. }
    assert (UP3 : unpoisoned m3 FSIP (FSIP + 24)).
    { eapply unpoisoned_munch; [| exact MU3| apply DS3; [clear - PL; lia| clear; lia| clear - PL; lia| exact DPF]].
      eapply unpoisoned_munch; [| exact MUF2|].
      - eapply unpoisoned_munch; [exact UP0| exact MU1| apply DS1; clear - PL; lia].
      - destruct LY5 as (_ & _ & FA1 & FA2). cbn [disjoint_from fake_area app]. rewrite !shad_div. unfold AIMG_HI, SMK_STACK, FAKESZ, ASHOFF in *.
        unfold KHIGH in KHI. clear - PL SFS FA1 FA2 FABL SPAB LO BOT KHI ATR. repeat split; Z.div_mod_to_equations; lia. }
    assert (ARO3 : aro_client RNG m3).
    { eapply aro_client_transport_gen; [exact WM03 | exact ARO | exact MU03 |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). destruct LY5 as (_ & _ & FA1 & FA2).
      cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, FAKESZ in *.
      clear - B1 B2 B3 PL FA1 FA2 FABL ATR BOT LO. repeat split; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    pose proof (AZ_findfsi_a.p_fin_sk AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (FSPA SPV) FSIP SRC src off size lo
                  FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) G_lo G_fsip G_src G_ff G_flg RSTK RI R_src R_fsip R_ff LBH) as PFSK.
    pose proof (AZ_findfsi_a.p_fin AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (FSPA SPV) FSIP SRC src off size lo
                  FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) G_lo G_fsip G_src G_ff G_flg RSTK RI R_src R_fsip R_ff LBH) as PFIN.
    pose proof (AZ_findfsi_e.p_lset AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (FSPA SPV) FSIP SRC src off size lo
                  FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) OK OFF0 N5 N40 OFS F8 G_lo G_fsip G_src G_ff G_flg RSTK RI R_src R_fsip R_ff LBH GETCB KHI PFIN) as PLOOP.
    pose proof (AZ_findfsi_c.p_gen AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (FSPA SPV) FSIP SRC src off size lo
                  FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) OK OFF0 N5 OFS F8 G_lo G_fsip G_src G_ff G_flg RSTK RI R_src R_fsip R_ff LBH
                  rng_fs GETFH FHL FFLAG ASH RFS KHI SPT RSTKT TP AIS PFIN PLOOP) as PGEN.
    eapply (AZ_findfsi_b.p_top AI fflag FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (FSPA SPV) FSIP SRC src off size lo
              FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF) OK OFF0 N5 N40 OFS SRCE F8 G_lo G_fsip G_src G_ff G_flg R_src R_fsip LBH PFSK PGEN m3).
    split; [exact BI3|]. split; [exact SAV3|]. split; [exists jA'; exact FRA3|]. split; [exact STL3|]. split; [exact STG3|].
    split; [exists junk; exact FFC3|]. split; [exact XL3|]. split; [exact SHF3|]. split; [exact SB3|]. split; [exact US3|]. split; [exact UP3|].
    split; [exists j24; exact FC3| exact ARO3].
  Qed.
End Thm.
End CANSEC1.
