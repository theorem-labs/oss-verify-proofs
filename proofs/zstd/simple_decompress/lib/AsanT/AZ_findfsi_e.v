(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c AZ_findfsi_d.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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
Section FS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA FSIP SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis N40 : size < 1099511627776.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  Hypothesis F8 : FSIP mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4320 /\ SPV - 176 <= SPA <= SPV - 160 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis G_fsip : (17594333495296 <= FSIP /\ FSIP + 32 <= 2^47) /\ SPV <= FSIP.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                    /\ (FSIP + 24 <= FF \/ FF + 256 <= FSIP) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC).
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (FSIP + 24 <= FLG \/ FLG + 1 <= FSIP).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_fsip : rng RNG FSIP 24 /\ rng RNG (shad FSIP) (shspan FSIP 24).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.
  (* [comment removed for export] *)
  Hypothesis GETCB : zd_getcblock_stmtA.
  Hypothesis KLO : KHIGH <= lo.

  Notation WR := [(FSIP, FSIP + 24)].
  Notation POST := (zd_findfsi_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV FSIP src off size lo m0).
  Notation RES := (find_frame_size_info src off size).

  Notation BINV := (AZ_findfsi_a.BINV AI L RNG st LB m0 SPV FSIP FF).
  Notation LINV := (AZ_findfsi_c.LINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA FSIP SRC src lo FF SHF FLG).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation FRL5 j1 j2 := [CB 16 j1; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FSIP); CB 16 j2; C8 (Z_to_bv 64 FF)].

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Hypothesis PFIN : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84414 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).

  Ltac gf_unhold := unfold fk_held in *.
  Ltac fsip_sh UP RP2 k :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm FSIP 24 (FSIP + k) UP ltac:(clear; lia) ltac:(gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_fsip; lia) ltac:(gf_unhold; clear - G_fsip; lia)) as RDz;
    assert (RTz : rng RNG ((FSIP + k) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RP2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
    end.
  Ltac fsip_sh0 UP RP2 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm FSIP 24 FSIP UP ltac:(clear; lia) ltac:(gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_fsip; lia) ltac:(gf_unhold; clear - G_fsip; lia)) as RDz;
    assert (RTz : rng RNG (FSIP ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RP2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
    end.
  Ltac fsip_up UP MUL :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (UPc : unpoisoned mm FSIP (FSIP + 24))
        by (eapply unpoisoned_munch; [exact UP | exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
              gf_unhold; clear - G_fsip; Z.div_mod_to_equations; lia])
    end.
  (* [comment removed for export] *)
  Ltac fsip_up2 UP MUL :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (UPc : unpoisoned mm FSIP (FSIP + 24))
        by (eapply unpoisoned_munch; [exact UP | exact MUL | cbn [disjoint_from]; rewrite !shad_div;
              match goal with E : SHF = SHB + FF / 8 |- _ => rewrite E end; unfold ASHOFF;
              match goal with F7 : fk_held (FSIP + 24 <= FF \/ _), F2 : FF mod 256 = 0, PL : (17594333495296 <= FSIP /\ _), ATR : (_ <= ATOP <= _) |- _ =>
                clear - F7 F2 F8 PL ATR end;
              unfold fk_held in *; Z.div_mod_to_equations; lia])
    end.
  (* [comment removed for export] *)
  Ltac fs_geom :=
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6); pose proof G_fsip as (P1 & P2); pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8');
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5); pose proof R_fsip as (RP1 & RP2); pose proof G_src as (S1 & S2 & S3); pose proof R_src as (RS1 & RS2);
    pose proof R_ff as (RF1 & RF2 & RF3);
    let ATR := fresh "ATR" in pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    let PL := fresh "PL" in let FL := fresh "FL" in let SL := fresh "SL" in let LL := fresh "LL" in
    pose proof (proj1 G_fsip) as PL; pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as FL;
    pose proof (fk_ablk_lits _ _ (proj1 G_src)) as SL; pose proof (fk_ablk_lits _ _ (proj1 (proj2 G_flg))) as LL;
    let ESHF := fresh "ESHF" in let GS := fresh "GS" in
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite (proj1 (proj2 (proj2 (proj2 G_ff)))), shad_div; reflexivity);
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (clear - FL GS ATR; lia);
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (clear - LL GS ATR; lia);
    assert (PSH : FSIP + 24 <= SHF \/ SHF + 32 <= FSIP) by (clear - PL GS ATR; lia);
    assert (SSH : SRC + zlen src <= SHF \/ SHF + 32 <= SRC) by (clear - SL GS ATR; lia);
    let FLA := fresh "FLA" in pose proof ((proj1 (proj2 (proj2 (proj2 (proj2 G_flg))))) _ ltac:(left; reflexivity)) as FLA; cbn [ab_addr ab_size] in FLA.
  Ltac fs_hold_geom :=
    fk_hold G_lo; fk_hold G_fsip; fk_hold G_src; fk_hold G_ff; fk_hold G_flg; fk_hold R_src; fk_hold R_fsip; fk_hold R_ff; fk_hold LBH.

  (* [comment removed for export] *)
  Ltac pose_berr :=
    pose proof (AZ_findfsi_d.p_berr AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA FSIP SRC src off size lo FF SHF FLG
                  F8 G_lo G_fsip G_src G_ff G_flg RSTK R_src R_fsip R_ff LBH KLO PFIN) as PBERR;
    pose proof (AZ_findfsi_d.p_berr72 AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA FSIP SRC src off size lo FF SHF FLG
                  F8 G_lo G_fsip G_src G_ff G_flg RSTK R_src R_fsip R_ff LBH KLO PFIN) as PBERR72.
  Ltac pose_done :=
    pose proof (AZ_findfsi_d.p_done AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA FSIP SRC src off size lo FF SHF FLG
                  OK OFF0 N40 OFS F8 G_lo G_fsip G_src G_ff G_flg RSTK R_src R_fsip R_ff LBH PFIN) as PDONE.

  (* [comment removed for export] *)
  Definition LOOPAT (n : nat) : Prop :=
    forall m1 h ip rem nb cbs bp j1 j2 w0 j24 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rem <= Z.of_nat n ->
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 112) (bp_cells bp) ->
    rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHB -> bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> unpoisoned m1 SRC (SRC + zlen src) ->
    unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    get_frame_header src off size = FH_ok h -> RES = fsi_fin off h (fsi_blocks src ip rem nb) ->
    get_cblock_size src ip rem = Some (cbs, bp) -> zd_is_error cbs = false ->
    off <= ip -> 0 <= rem -> ip + rem <= off + size -> 0 <= nb -> 3 * nb <= ip - off ->
    evtF bsegs RNG POST (STpc 0x84550 m1 x1 x5 x6 x7 (Z_to_bv 64 cbs) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (nb + 1)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (SRC + off))
                              (Z_to_bv 64 (SRC + ip)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rem) (Z_to_bv 64 (FF + 112)) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_lcall : forall (n : nat), LOOPAT n ->
    forall m1 h ip2 rem2 nb' cs12 j1 j2 w0 j24 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rem2 <= Z.of_nat n ->
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 112) cs12 -> cells_size cs12 = 12%nat ->
    rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHB -> bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> unpoisoned m1 SRC (SRC + zlen src) ->
    unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    get_frame_header src off size = FH_ok h -> RES = fsi_fin off h (fsi_blocks src ip2 rem2 nb') ->
    off <= ip2 -> 0 <= rem2 -> ip2 + rem2 <= off + size -> 1 <= nb' -> 3 * nb' <= ip2 - off ->
    evtF bsegs RNG POST (STpc 0x8457c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nb') (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (SRC + off))
                              (Z_to_bv 64 (SRC + ip2)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rem2) (Z_to_bv 64 (FF + 112)) x28 x29 x30 x31).
  Proof.
    intros n IH m1 h ip2 rem2 nb' cs12 j1 j2 w0 j24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           RN BI SAV FRA STL STG XM ZC XB XBS XP XL XS SB US UP FC GFH ER B1 B2 B3 B4 B5.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
    assert (ART : art m1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (UB : unpoisoned m1 (FF + 112) (FF + 112 + 12)).
    { apply (fshb_unp m1 FF); [rewrite <- F4; exact XS | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia | clear - FL ATR; lia]. }
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold STG. fk_hold XM. fk_hold ZC. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold UP. fk_hold FC. fk_hold ER. fs_hold_geom.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    fk_hold L4. fk_hold L3. fk_hold LL. fk_hold FLA. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold P2. fk_hold FFSH. fk_hold PSH. fk_hold PL.
    zstep. zstep. zstep. zstep.
    unfold zd_getcblock_stmtA, APZD_GETCBLOCK in GETCB.
    eapply evtF_cut.
    { eapply (GETCB RNG) with (lo := lo) (SRC := SRC) (BP := FF + 112) (src := src) (ip := ip2) (size := rem2);
      first [ exact SB | exact OK | exact XB | exact XBS | exact STL | exact MI | exact ART | reflexivity
            | clear - B1 OFF0; lia
            | clear - B2; lia
            | clear - B3 OFS; lia
            | clear - SL; lia
            | clear - G2; lia
            | clear - G3 G5; lia
            | clear - F3 G1; lia
            | clear - S2 G3; lia
            | intros _; split; [exact S1| split; [exact US| split; [exact RS1| exact RS2]]]
            | intros _; split; [eapply ablk_sub; [exact F1|clear; lia|clear; lia] | split; [exact UB| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
            | split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]
            | clear - FL; lia                                            (* [comment removed for export] *)
            | clear - F2; Z.div_mod_to_equations; lia                   (* [comment removed for export] *)
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & cs & -> & MU5 & WM5 & MI5 & ST5 & XB5 & XBS5 & XBOK).
    rd_retlit.
    gf_unhold.
    assert (DW : forall X k, (FF + 124 <= X \/ X + k <= FF + 112) -> SPA <= X -> 0 <= k -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] X k).
    { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk. repeat split; lia. }
    assert (DW' : forall X k, (FF + 124 <= X \/ X + k <= FF + 112) -> (X + k <= lo \/ SPV <= X) -> 0 <= k -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] X k).
    { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk G2 G3. repeat split; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DW; unfold FSAVED; cbn; clear - G3 F3 G1 G2; lia)) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DW; cbn; clear - G3 F3 G1 G2; lia)) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DW; clear - G3 F3 G1 G2; lia)) as STG5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XM MU5 WM5 ltac:(apply DW'; cbn; clear - F3 G1; lia)) as XM5.
    pose proof (rw_cells_transport _ _ _ _ _ _ ZC MU5 WM5 ltac:(apply DW'; unfold zfh_cells; cbn; clear - F3 G1; lia)) as ZC5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XP MU5 WM5 ltac:(apply DW'; cbn; clear - F3 G1; lia)) as XP5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XL MU5 WM5 ltac:(apply DW'; cbn; clear - FLA L2 G1; lia)) as XL5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XS MU5 WM5 ltac:(apply DW'; unfold FSHB; cbn; [clear - FFSH; lia| clear - GS KLO; unfold KHIGH in KLO; lia| clear; lia])) as XS5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FC MU5 WM5 ltac:(apply DW'; cbn; [clear - F7; lia| right; exact P2| clear; lia])) as FC5.
    pose proof (bytes_at_transport _ _ _ _ _ _ SB MU5 ltac:(rewrite length_map; apply DW'; [clear - F8'; lia| exact S2| clear - DB; lia])) as SB5.
    assert (DS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [left; clear - X0 Hn Hb ATR G1 G2 G3; Z.div_mod_to_equations; lia| exact I]. }
    pose proof (unpoisoned_munch _ _ _ _ _ US MU5 ltac:(apply DS; clear - SL ATR DB; lia)) as US5.
    pose proof (unpoisoned_munch _ _ _ _ _ UP MU5 ltac:(apply DS; clear - PL ATR; lia)) as UP5.
    assert (AH5 : AHEAP AI L RNG st (FB2 FF :: LB) m5).
    { eapply (AI_frame AI); [exact AH1 | exact MU5 | exact WM5 |].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] |].
      constructor; [cbn [fst snd] | constructor]. left; left. cbn. clear - G1 G2 G3 G5. lia. }
    assert (FFR05 : ffr_pres WR LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 m5 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24); (FF + 112, FF + 112 + 12); (SPA - 16, SPA)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] |];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] |];
          constructor; [cbn [fst snd]; split; [clear; lia | left; clear - G1 G2 G3 G5; lia] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WM5 ]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU05 : munch ([(FSIP, FSIP + 24); (SPV - 4672, SPV)] ++ fake_area L) m0 m5).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU5]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      unfold FAKESZ in *. clear - Hx F5 F6 G2 G3. lia. }
    assert (BI5 : BINV m5) by (split; [exact AH5| split; [exact FFR05| split; [exact MU05| split; [exact (wmono_trans _ _ _ _ WM1 WM5)| exact MI5]]]]).
    pose proof (cblock_ret_range src ip2 rem2 OK) as RRET.
    clear SAV FRA STG XM ZC XP XL XS FC SB US UP UB ART STL MI DW DW' DS.
    fk_hold BI5. fk_hold SAV5. fk_hold FRA5. fk_hold STG5. fk_hold XM5. fk_hold ZC5. fk_hold XP5. fk_hold XL5. fk_hold XS5. fk_hold FC5. fk_hold SB5. fk_hold US5. fk_hold UP5.
    fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold XBOK. fk_hold ST5. fk_hold XB5.
    zstep.                                                      (* [comment removed for export] *)
                                                                (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-119)) with (Z_to_bv 64 18446744073709551497) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      destruct (get_cblock_size src ip2 rem2) as [[v2 bp2]|] eqn:GC; cbn [cblock_ret] in *;
        [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; clear - KE; lia].
      gf_unhold. rewrite (XBOK v2 bp2 eq_refl) in XB5.
      eapply (IH m5 h ip2 rem2 nb' v2 bp2); try eassumption; try (clear - B1 B2 B3 B4 B5; lia).
      apply zd_is_error_false_iff. clear - KE. lia.
    - (* [comment removed for export] *)
      zstep.
      gf_unhold. pose_berr. eapply PBERR; try eassumption.
      rewrite ER. rewrite (fsi_blocks_err src ip2 rem2 nb' OK); [reflexivity|].
      apply zd_is_error_true_iff. clear - KE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_loop : forall n, LOOPAT n.
  Proof.
    induction n as [|n IH]; unfold LOOPAT; intros m1 h ip rem nb cbs bp j1 j2 w0 j24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           RN BI SAV FRA STL STG XM ZC XB XP XL XS SB US UP FC GFH ER G E B1 B2 B3 B4 B5.
    - (* [comment removed for export] *)
      exfalso. unfold get_cblock_size, ZD_blockHeaderSize in G. replace (rem <? 3) with true in G by (symmetry; apply Z.ltb_lt; clear - RN B2; lia). discriminate G.
    - pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
      pose proof (get_cblock_size_ok src OK ip rem cbs bp G) as (R3 & _ & RT & RL & RO & RC). specialize (RC E).
      destruct RC as (_ & RCBS & _). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in *.
      pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
      rewrite (fsi_blocks_eq src OK), G, E in ER. unfold ZD_blockHeaderSize in ER.
      unfold bp_cells in XB. unfold FSHB in XS.
      pose proof (munch_refl [(SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
      fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold STG. fk_hold STL. fk_hold XM. fk_hold ZC. fk_hold XP. fk_hold XL. fk_hold UP. fk_hold FC. fk_hold ER. fk_hold SB. fk_hold US. fs_hold_geom.
      fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
      fk_hold L4. fk_hold L3. fk_hold LL. fk_hold FLA. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold P2. fk_hold FFSH. fk_hold PSH. fk_hold PL. fk_hold SL. fk_hold S2.
      zstep.                                                    (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        gf_unhold. pose_berr. eapply PBERR72; try eassumption.
        rewrite ER. replace (rem <? 3 + cbs) with true by (symmetry; apply Z.ltb_lt; clear - K; lia). reflexivity.
      + replace (rem <? 3 + cbs) with false in ER by (unfold fk_held; symmetry; apply Z.ltb_ge; clear - K; lia).
        (* [comment removed for export] *)
        zstep. rewrite sx32w_small by (clear - RL; lia).   (* [comment removed for export] *)
        zstep. replace (SRC + ip + (cbs + 3)) with (SRC + (ip + (3 + cbs))) by (clear; lia).
        zstep.                                                 (* [comment removed for export] *)
                                                           (* [comment removed for export] *)
        replace (rem - (cbs + 3)) with (rem - (3 + cbs)) by (clear; lia).
                                                                                                                   (* [comment removed for export] *)
        zstep. zstep.                                      (* [comment removed for export] *)
        zstep. if_cases KL; zify_cond KL.
        * (* [comment removed for export] *)
          change (rw_cells bsegs m2 SHF FSHZ) in XS. gf_unhold.
          assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
          assert (BI2 : BINV m2).
          { split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
            - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
              constructor; [cbn [fst snd] | constructor].
              rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
              eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia].
            - eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
              eapply (fk_ffr_fin AI L RNG st LB m1 m1 m2 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24)]);
                [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
                | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] | constructor]
                | constructor
                | apply ffr_pres_refl
                | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
                | exact WML ].
            - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
              destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia. }
          replace (bp_last bp =? 0) with false in ER by (symmetry; apply Z.eqb_neq; clear - KL; lia).
          pose_done.
          (* [comment removed for export] *)
          eapply (PDONE m2 h (ip + (3 + cbs)) (rem - (3 + cbs)) (nb + 1));
            [ exact BI2
            | eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - FFSH; lia]
            | eapply rw_cells_transport; [exact ZC | exact MUL | exact WML | unfold zfh_cells; cbn; clear - FFSH; lia]
            | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - FFSH; lia]
            | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia]
            | exact XS
            | eapply unpoisoned_munch; [exact UP | exact MUL |]; cbn [disjoint_from]; rewrite !shad_div; rewrite ESHF; unfold ASHOFF; clear - F7 F2 PL; split; [| exact I]; Z.div_mod_to_equations; lia
            | eapply rw_cells_transport; [exact FC | exact MUL | exact WML | cbn; clear - PSH; lia]
            | exact GFH
            | change (RES = fsi_fin off h (FL_done (ip + (3 + cbs)) (rem - (3 + cbs)) (nb + 1))) in ER; exact ER
            | clear - B1 RCBS; lia
            | clear - K; lia
            | clear - B3; lia
            | clear - B4; lia
            | clear - B5 RCBS; lia ].
        * (* [comment removed for export] *)
          replace (bp_last bp =? 0) with true in ER by (unfold fk_held; symmetry; apply Z.eqb_eq; clear - KL; lia).
          zstep. zstep. zstep.                          (* [comment removed for export] *)
          lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          change (rw_cells bsegs m3 SHF FSHB) in XS. gf_unhold.
          assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
          assert (BI3 : BINV m3).
          { split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
            - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
              constructor; [cbn [fst snd] | constructor].
              rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
              eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia].
            - eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
              eapply (fk_ffr_fin AI L RNG st LB m1 m1 m3 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24)]);
                [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
                | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] | constructor]
                | constructor
                | apply ffr_pres_refl
                | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
                | exact WML ].
            - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
              destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia. }
          assert (NZ : 0 < zlen src) by (clear - OFS N5 OFF0; lia).
          eapply (p_lcall n IH m3 h (ip + (3 + cbs)) (rem - (3 + cbs)) (nb + 1) (bp_cells bp));
            [ clear - RN K RCBS; lia
            | exact BI3
            | eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]
            | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - FFSH; lia]
            | eapply rw_cells_transport; [exact ZC | exact MUL | exact WML | unfold zfh_cells; cbn; clear - FFSH; lia]
            | unfold bp_cells; exact XB
            | reflexivity
            | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - FFSH; lia]
            | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia]
            | exact XS
            | eapply bytes_at_transport; [exact SB | exact MUL | rewrite length_map; cbn; clear - SSH; lia]
            | eapply unpoisoned_munch; [exact US | exact MUL |]; cbn [disjoint_from]; rewrite !shad_div; rewrite ESHF; unfold ASHOFF; clear - F8' F2 SL NZ; split; [| exact I]; Z.div_mod_to_equations; lia
            | eapply unpoisoned_munch; [exact UP | exact MUL |]; cbn [disjoint_from]; rewrite !shad_div; rewrite ESHF; unfold ASHOFF; clear - F7 F2 PL; split; [| exact I]; Z.div_mod_to_equations; lia
            | eapply rw_cells_transport; [exact FC | exact MUL | exact WML | cbn; clear - PSH; lia]
            | exact GFH
            | change (RES = fsi_fin off h (fsi_blocks src (ip + (3 + cbs)) (rem - (3 + cbs)) (nb + 1))) in ER; exact ER
            | clear - B1 RCBS; lia
            | clear - K; lia
            | clear - B3; lia
            | clear - B4; lia
            | clear - B5 RCBS; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma p_lcall0 : forall m1 h j1 j2 w0 cs12 j24 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 112) cs12 -> cells_size cs12 = 12%nat ->
    rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHB -> bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> unpoisoned m1 SRC (SRC + zlen src) ->
    unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    get_frame_header src off size = FH_ok h -> RES = fsi_fin off h (fsi_blocks src (off + fh_hsize h) (size - fh_hsize h) 0) ->
    fh_hsize h <= size -> 5 <= fh_hsize h <= 18 ->
    evtF bsegs RNG POST (STpc 0x84530 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (SRC + (off + fh_hsize h)))
                              (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (size - fh_hsize h)) (Z_to_bv 64 (FF + 112)) x28 x29 x30 x31).
  Proof.
    intros m1 h j1 j2 w0 cs12 j24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           BI SAV FRA STL STG XM ZC XB XBS XP XL XS SB US UP FC GFH ER RHS RHS0.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
    assert (ART : art m1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (UB : unpoisoned m1 (FF + 112) (FF + 112 + 12)).
    { apply (fshb_unp m1 FF); [rewrite <- F4; exact XS | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia | clear - FL ATR; lia]. }
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold STG. fk_hold XM. fk_hold ZC. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold UP. fk_hold FC. fk_hold ER. fs_hold_geom.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    fk_hold L4. fk_hold L3. fk_hold LL. fk_hold FLA. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold P2. fk_hold FFSH. fk_hold PSH. fk_hold PL.
    zstep. zstep. zstep. zstep.
    unfold zd_getcblock_stmtA, APZD_GETCBLOCK in GETCB.
    eapply evtF_cut.
    { eapply (GETCB RNG) with (lo := lo) (SRC := SRC) (BP := FF + 112) (src := src) (ip := off + fh_hsize h) (size := size - fh_hsize h);
      first [ exact SB | exact OK | exact XB | exact XBS | exact STL | exact MI | exact ART | reflexivity
            | clear - OFF0 RHS0; lia
            | clear - RHS; lia
            | clear - OFS RHS0; lia
            | clear - SL; lia
            | clear - G2; lia
            | clear - G3 G5; lia
            | clear - F3 G1; lia
            | clear - S2 G3; lia
            | intros _; split; [exact S1| split; [exact US| split; [exact RS1| exact RS2]]]
            | intros _; split; [eapply ablk_sub; [exact F1|clear; lia|clear; lia] | split; [exact UB| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
            | split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]
            | clear - FL; lia                                            (* [comment removed for export] *)
            | clear - F2; Z.div_mod_to_equations; lia                   (* [comment removed for export] *)
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & cs & -> & MU5 & WM5 & MI5 & ST5 & XB5 & XBS5 & XBOK).
    rd_retlit.
    gf_unhold.
    assert (DW : forall X k, (FF + 124 <= X \/ X + k <= FF + 112) -> SPA <= X -> 0 <= k -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] X k).
    { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk. repeat split; lia. }
    assert (DW' : forall X k, (FF + 124 <= X \/ X + k <= FF + 112) -> (X + k <= lo \/ SPV <= X) -> 0 <= k -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] X k).
    { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk G2 G3. repeat split; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DW; unfold FSAVED; cbn; clear - G3 F3 G1 G2; lia)) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DW; cbn; clear - G3 F3 G1 G2; lia)) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DW; clear - G3 F3 G1 G2; lia)) as STG5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XM MU5 WM5 ltac:(apply DW'; cbn; clear - F3 G1; lia)) as XM5.
    pose proof (rw_cells_transport _ _ _ _ _ _ ZC MU5 WM5 ltac:(apply DW'; unfold zfh_cells; cbn; clear - F3 G1; lia)) as ZC5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XP MU5 WM5 ltac:(apply DW'; cbn; clear - F3 G1; lia)) as XP5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XL MU5 WM5 ltac:(apply DW'; cbn; clear - FLA L2 G1; lia)) as XL5.
    pose proof (rw_cells_transport _ _ _ _ _ _ XS MU5 WM5 ltac:(apply DW'; unfold FSHB; cbn; [clear - FFSH; lia| clear - GS KLO; unfold KHIGH in KLO; lia| clear; lia])) as XS5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FC MU5 WM5 ltac:(apply DW'; cbn; [clear - F7; lia| right; exact P2| clear; lia])) as FC5.
    pose proof (bytes_at_transport _ _ _ _ _ _ SB MU5 ltac:(rewrite length_map; apply DW'; [clear - F8'; lia| exact S2| clear - DB; lia])) as SB5.
    assert (DS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(FF + 112, FF + 112 + 12); (SPA - 16, SPA)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [left; clear - X0 Hn Hb ATR G1 G2 G3; Z.div_mod_to_equations; lia| exact I]. }
    pose proof (unpoisoned_munch _ _ _ _ _ US MU5 ltac:(apply DS; clear - SL ATR DB; lia)) as US5.
    pose proof (unpoisoned_munch _ _ _ _ _ UP MU5 ltac:(apply DS; clear - PL ATR; lia)) as UP5.
    assert (AH5 : AHEAP AI L RNG st (FB2 FF :: LB) m5).
    { eapply (AI_frame AI); [exact AH1 | exact MU5 | exact WM5 |].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] |].
      constructor; [cbn [fst snd] | constructor]. left; left. cbn. clear - G1 G2 G3 G5. lia. }
    assert (FFR05 : ffr_pres WR LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 m5 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24); (FF + 112, FF + 112 + 12); (SPA - 16, SPA)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] |];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact F1 | clear; lia]]] |];
          constructor; [cbn [fst snd]; split; [clear; lia | left; clear - G1 G2 G3 G5; lia] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WM5 ]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU05 : munch ([(FSIP, FSIP + 24); (SPV - 4672, SPV)] ++ fake_area L) m0 m5).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU5]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      unfold FAKESZ in *. clear - Hx F5 F6 G2 G3. lia. }
    assert (BI5 : BINV m5) by (split; [exact AH5| split; [exact FFR05| split; [exact MU05| split; [exact (wmono_trans _ _ _ _ WM1 WM5)| exact MI5]]]]).
    pose proof (cblock_ret_range src (off + fh_hsize h) (size - fh_hsize h) OK) as RRET.
    clear SAV FRA STG XM ZC XP XL XS FC SB US UP UB ART STL MI DW DW' DS.
    fk_hold BI5. fk_hold SAV5. fk_hold FRA5. fk_hold STG5. fk_hold XM5. fk_hold ZC5. fk_hold XP5. fk_hold XL5. fk_hold XS5. fk_hold FC5. fk_hold SB5. fk_hold US5. fk_hold UP5.
    fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold XBOK. fk_hold ST5. fk_hold XB5.
    zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 18446744073709551496) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      gf_unhold. pose_berr.
      eapply PBERR; [exact BI5 | exact SAV5 | exact FRA5 | exact ST5 | exact STG5 | exact XM5 | exact XP5 | exact XL5 | exact XS5 | exact UP5 | exact FC5 |].
      rewrite ER. rewrite (fsi_blocks_err src (off + fh_hsize h) (size - fh_hsize h) 0 OK); [reflexivity|].
      apply zd_is_error_true_iff. clear - KE. lia.
    - (* [comment removed for export] *)
      destruct (get_cblock_size src (off + fh_hsize h) (size - fh_hsize h)) as [[v2 bp2]|] eqn:GC; cbn [cblock_ret] in *;
        [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; clear - KE; lia].
      zstep.                                                 (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      change (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)).
      gf_unhold. rewrite (XBOK v2 bp2 eq_refl) in XB5.
      eapply (p_loop (Z.to_nat (size - fh_hsize h)) m5 h (off + fh_hsize h) (size - fh_hsize h) 0 v2 bp2);
        [ clear - RHS; lia
        | exact BI5 | exact SAV5 | exact FRA5 | exact ST5 | exact STG5 | exact XM5 | exact ZC5 | exact XB5 | exact XP5 | exact XL5 | exact XS5
        | exact SB5 | exact US5 | exact UP5 | exact FC5 | exact GFH | exact ER | exact GC
        | apply zd_is_error_false_iff; clear - KE; lia
        | clear - RHS0; lia | clear - RHS; lia | clear; lia | clear; lia | clear - RHS0; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma p_lset : forall m1 h (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word),
    LINV m1 h -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
    get_frame_header src off size = FH_ok h ->
    evtF bsegs RNG POST (STpc 0x8450c m1 x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size)
                              (Z_to_bv 64 (FF + 32)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 h x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 LI SK GFH.
    destruct LI as (BI & SAV & [jA FRA] & STL & STG & [jH XH] & ZC & [jT XT] & XL & XS & SB & US & UP & [j24 FC] & ARO).
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
    pose proof (get_frame_header_ok src OK off size h GFH) as (TY & _ & RHS & _ & _ & _ & _ & _ & HT0 & HT1).
    assert (RHS0 : 5 <= fh_hsize h <= 18).
    { destruct TY as [T|T].
      - destruct (HT0 T) as (_ & _ & RR & _). unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RR. clear - RR. lia.
      - destruct (HT1 T) as (_ & RR & _). unfold ZD_SKIPPABLEHEADERSIZE in RR. clear - RR. lia. }
    clear TY HT0 HT1.
    pose proof (ffsi_main src off size h SK GFH) as ER.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (NZ : 0 < zlen src) by (clear - OFS N5 OFF0; lia).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 48 jA [C8 (Z_to_bv 64 FF)] [16; 8; 8; 16]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XH)) as XM. clear XH.
    apply (rw_cells_split_CB bsegs _ _ [] 168 jT [C8 (Z_to_bv 64 FLG)] [32; 12; 124]%nat) in XT; [| reflexivity]. cbn [mk_CB_cells app] in XT.
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 32 (firstn 32 jT)] _) XT)) as XT2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XT2.
    pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [CB 12 (firstn 12 (skipn 32 jT))] _) XT2)) as XB.
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 12 (firstn 12 (skipn 32 jT)); CB 124 (firstn 124 (skipn 12 (skipn 32 jT)))] _) XT2)) as XP.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XB, XP. clear XT XT2.
    match type of XB with rw_cells _ _ ?a _ => replace a with (FF + 112) in XB by (clear; lia) end.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 248) in XP by (clear; lia) end.
    unfold zfh_cells in ZC. unfold FSHZ in XS.
    pose proof (munch_refl [(SPA + 16, SPA + 32); (SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold BI. fk_hold SAV. fk_hold STG. fk_hold STL. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold UP. fk_hold FC. fk_hold ER. fk_hold SB. fk_hold US. fk_hold XB. fk_hold ARO. fs_hold_geom.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    fk_hold L4. fk_hold L3. fk_hold LL. fk_hold FLA. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold P2. fk_hold FFSH. fk_hold PSH. fk_hold PL. fk_hold SL. fk_hold S2.
    zstep. zstep.                                                  (* [comment removed for export] *)
    zstep. rewrite zx32w_small by (clear - RHS RHS0; lia).         (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold fk_held in SL.
    zstep. zstep. zstep. zstep.
    fk_hold SL. try clear KXE KXA KXRD KXK KXMI.
    let w := getreg 21 in replace w with (Z_to_bv 64 (SRC + (off + fh_hsize h))) by (first [f_equal; clear; lia | apply Z_to_bv_eqm; clear; lia]).
                                                                   (* [comment removed for export] *)
    zstep. zstep.                                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    change (rw_cells bsegs m3 SHF FSHB) in XS. gf_unhold.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (BI3 : BINV m3).
    { split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
      - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
        constructor; [cbn [fst snd]; left; left; cbn; clear - G1 G2 G3 G5; lia |].
        constructor; [cbn [fst snd] | constructor].
        rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
        eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia].
      - eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
        eapply (fk_ffr_fin AI L RNG st LB m1 m1 m3 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24); (SPA + 16, SPA + 32)]);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] |];
            constructor; [cbn [fst snd]; split; [clear; lia | left; clear - G1 G2 G3 G5; lia] | constructor]
          | constructor
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WML ].
      - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2 G3. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (STL3 : stk bsegs m3 lo SPA) by (eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (STG3 : stk bsegs m3 (SPA + 56) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (XM3 : rw_cells bsegs m3 FF [C8 (Z_to_bv 64 0x41b58ab3)]) by (eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - FFSH F3 G1 G2; lia]).
    assert (XB3 : rw_cells bsegs m3 (FF + 112) [CB 12 (firstn 12 (skipn 32 jT))]) by (eapply rw_cells_transport; [exact XB | exact MUL | exact WML | cbn; clear - FFSH F3 G1 G2; lia]).
    assert (XP3 : rw_cells bsegs m3 (FF + 248) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - FFSH F3 G1 G2; lia]).
    assert (XL3 : rw_cells bsegs m3 FLG [C1 (Z_to_bv 8 1)]) by (eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH L2 G1 G2; lia]).
    assert (FC3 : rw_cells bsegs m3 FSIP [CB 24 j24]) by (eapply rw_cells_transport; [exact FC | exact MUL | exact WML | cbn; clear - PSH P2 G2 G3; lia]).
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src)) by (eapply bytes_at_transport; [exact SB | exact MUL | rewrite length_map; cbn; clear - SSH S2 G2 G3; lia]).
    assert (US3 : unpoisoned m3 SRC (SRC + zlen src)).
    { eapply unpoisoned_munch; [exact US | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - F8' F2 SL NZ ATR G1 G2 G3. split; [Z.div_mod_to_equations; lia|]. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (UP3 : unpoisoned m3 FSIP (FSIP + 24)).
    { eapply unpoisoned_munch; [exact UP | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - F7 F2 PL ATR G1 G2 G3. split; [Z.div_mod_to_equations; lia|]. split; [| exact I]. Z.div_mod_to_equations. lia. }
    clear SAV STL STG XM XB XP XL FC SB US UP ARO.
    eapply (p_lcall0 m3 h); [exact BI3 | exact SAV3 | exact FRA | exact STL3 | exact STG3 | exact XM3 | exact ZC | exact XB3 | reflexivity | exact XP3 | exact XL3 | exact XS
                            | exact SB3 | exact US3 | exact UP3 | exact FC3 | exact GFH | exact ER | exact RHS | exact RHS0 ].
  Qed.
End FS.
End CANSEC1.
