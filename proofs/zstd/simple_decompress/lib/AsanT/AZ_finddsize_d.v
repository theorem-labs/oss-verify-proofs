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
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c AZ_finddsize_a AZ_finddsize_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation SHB := 2147450880.
Notation KM8 := 18446744073709551608.
Notation K9 := 4294967287.
Notation KSK := (Z_to_bv 64 25481893).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dd_cblock_ret_range : forall src ip rem, all_bytes src ->
  0 <= cblock_ret (get_cblock_size src ip rem) < 18446744073709551616.
Proof.
  intros src ip rem OK. unfold get_cblock_size.
  destruct (rem <? ZD_blockHeaderSize); cbn [cblock_ret].
  - unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
  - pose proof (cblock_props_range (le24 src ip) (le24_range src OK ip)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
    unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected. change (2^64) with 18446744073709551616.
    destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia.
Qed.

Lemma dd_fsi_blocks_fuel_err_range : forall src, all_bytes src -> forall f ip rem nb v,
  fsi_blocks_fuel f src ip rem nb = FL_err v -> 0 <= v < 18446744073709551616.
Proof.
  intros src OK. induction f as [|f IH]; intros ip rem nb v E; cbn [fsi_blocks_fuel] in E.
  - injection E as <-. unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
  - pose proof (dd_cblock_ret_range src ip rem OK) as RC.
    destruct (get_cblock_size src ip rem) as [[cbs bp]|]; cbn [cblock_ret] in RC.
    + destruct (zd_is_error cbs); [injection E as <-; exact RC|].
      destruct (rem <? ZD_blockHeaderSize + cbs); [injection E as <-; unfold ZERR, ZE_srcSize_wrong; change (2^64) with 18446744073709551616; lia|].
      destruct (bp_last bp =? 0); [eapply IH; exact E| discriminate E].
    + injection E as <-. exact RC.
Qed.

Lemma dd_fsi_csize_range : forall src off sz, all_bytes src -> 0 <= off -> 5 <= sz < 18446744073709551616 ->
  0 <= find_frame_compressed_size src off sz < 18446744073709551616.
Proof.
  intros src off sz OK OFF RSZ. unfold find_frame_compressed_size, find_frame_size_info.
  destruct ((ZD_SKIPPABLEHEADERSIZE <=? sz) && is_skippable_magic (le32 src off)); cbn [fsi_csize].
  - unfold read_skippable_frame_size. pose proof (le32_range src OK (off + 4)) as R4. change (2^32) with 4294967296 in R4.
    unfold ZERR, ZE_srcSize_wrong, ZE_frameParameter_unsupported, ZD_SKIPPABLEHEADERSIZE. change (2^64) with 18446744073709551616.
    destruct (sz <? 8); [lia|]. cbv zeta. destruct (_ <? le32 src (off + 4)); [lia|]. destruct (sz <? _); lia.
  - destruct (get_frame_header src off sz) as [h|v] eqn:G.
    + pose proof (get_frame_header_ok src OK off sz h G) as (TY & _ & RHS & _ & _ & _ & _ & _ & HT0 & HT1).
      assert (RHS0 : 5 <= fh_hsize h).
      { destruct TY as [T|T].
        - destruct (HT0 T) as (_ & _ & RR & _). unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RR. lia.
        - destruct (HT1 T) as (_ & RR & _). unfold ZD_SKIPPABLEHEADERSIZE in RR. lia. }
      destruct (fsi_blocks src (off + fh_hsize h) (sz - fh_hsize h) 0) as [v|ip rem nb] eqn:B.
      * cbn [fsi_csize]. eapply dd_fsi_blocks_fuel_err_range; [exact OK| exact B].
      * apply (fsi_blocks_done src OK) in B. destruct B as (B1 & B2 & B3 & _). unfold ZD_blockHeaderSize in B1.
        destruct (negb (fh_checksum h =? 0) && (rem <? 4)) eqn:C; cbv zeta; cbn [fsi_csize].
        -- unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
        -- destruct (fh_checksum h =? 0); cbn [negb andb] in C; [lia|]. apply Z.ltb_ge in C. lia.
    + pose proof (gfh_ret_pos src off sz v ltac:(lia) G) as RV.
      destruct (zd_is_error v); cbn [fsi_csize]; [lia|]. unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
Qed.


Section FD.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA SRC : Z) (src : list Z) (size0 lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size0.
  Hypothesis N40 : size0 < 1099511627776.
  Hypothesis NLEN : size0 <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4672 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC).
  Hypothesis G_ff : ablk FF (FF + 128) /\ FF mod 128 = 0 /\ FF + 128 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 128 <= al_fake L + FAKESZ
                    /\ (SRC + zlen src <= FF \/ FF + 128 <= SRC).
  Hypothesis G_flg : FLG = fflag L 1 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB1 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_ff : rng RNG FF 128 /\ rng RNG SHF 16 /\ rng RNG FLG 1.
  Hypothesis R_fsi : rng RNG (shad (SPA + 64)) (shspan (SPA + 64) 24).
  Hypothesis LBH : ablkLB LB.
  (* [comment removed for export] *)
  Variable SZB : Z.

  Notation POST := (zd_finddsize_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV src size0 lo m0).
  Notation RES := (find_decompressed_size src size0).
  Notation BINV := (AZ_finddsize_a.BINV AI L RNG st LB m0 SPV FF).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 KM8) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation XINVg := (AZ_finddsize_b.XINVg AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA SRC src lo FF SHF FLG).
  Notation XINV := (XINVg DSH0).


  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FINDFSI : zd_findfsi_stmtA AI rng_fs.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis ASH : ashort LB 3.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis RSTKT : rng RNG lo (al_top L - lo).
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis INS : 0 < zlen src -> ainimg LB SRC (zlen src).

  (* [comment removed for export] *)
  Hypothesis PXEXIT : forall sh m1 r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31 : word),
    XINVg sh m1 -> cells_size sh = 16%nat -> Z_to_bv 64 r = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (STpc 0x83dac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 r) x27 x28 x29 x30 x31).
  Hypothesis PADV : forall m1 off sz step total (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 8 <= step <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src (off + step) (sz - step) total -> 0 <= total < 18446744073709551616 -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83e30 m1 x1 x5 x6 x7 (Z_to_bv 64 step) x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).

  Ltac gf_unhold := unfold fk_held in *.
  Ltac fd_geom :=
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6); pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7);
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4); pose proof G_src as (S1 & S2); pose proof R_src as (RS1 & RS2); pose proof R_ff as (RF1 & RF2 & RF3);
    let ATR := fresh "ATR" in pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    let FL := fresh "FL" in let SL := fresh "SL" in let LL := fresh "LL" in
    pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as FL; pose proof (fk_ablk_lits _ _ (proj1 G_src)) as SL; pose proof (fk_ablk_lits _ _ (proj1 (proj2 G_flg))) as LL;
    let ESHF := fresh "ESHF" in let GS := fresh "GS" in
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite (proj1 (proj2 (proj2 (proj2 G_ff)))), shad_div; reflexivity);
    assert (GS : SHB + 805376 <= SHF /\ SHF + 16 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
    assert (FFSH : FF + 128 <= SHF \/ SHF + 16 <= FF) by (clear - FL GS ATR; lia);
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 16 <= FLG) by (clear - LL GS ATR; lia);
    assert (SSH : SRC + zlen src <= SHF \/ SHF + 16 <= SRC) by (clear - SL GS ATR; lia);
    let FLA := fresh "FLA" in pose proof ((proj2 (proj2 (proj2 (proj2 G_flg)))) _ ltac:(left; reflexivity)) as FLA; cbn [ab_addr ab_size] in FLA.

  (* [comment removed for export] *)
  Lemma p_fsi : forall m1 off sz total v (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 -> 0 <= total < 18446744073709551616 ->
    RES = (if zd_is_error (find_frame_compressed_size src off sz) then ZD_CONTENTSIZE_ERROR
           else find_dsize src (off + find_frame_compressed_size src off sz) (sz - find_frame_compressed_size src off sz) total) ->
    Z_to_bv 64 v = Z_to_bv 64 ZD_CONTENTSIZE_ERROR -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83f94 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              (Z_to_bv 64 v) (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XI R5 ROFF RSZ RT ER EV RB.
    pose proof XI as (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO).
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    fd_geom.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (NZ : 0 < zlen src) by (clear - RSZ R5 ROFF NLEN; lia).
    assert (OFS : off + sz <= zlen src) by (clear - RSZ NLEN; lia).
    assert (SZ40 : sz < 1099511627776) by (clear - RSZ N40 ROFF; lia).
    destruct (FHL _ _ _ _ _ AH1) as [FAB FABD]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (LBH' : ablkLB (FB1 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB1 FF :: LB) 2) by (apply ashort_push; [exact ASH| clear; lia]).
    assert (ART1 : art m1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP : afpre AI rng_fs L RNG st (FB1 FF :: LB) m1 lo SPA 2).
    { unfold afpre, astk. split; [exact AH1|]. split; [exact ASH'|]. split; [exact ART1|].
      split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    assert (SRCAP : ainblk (FB1 FF :: LB) SRC (zlen src)).
    { destruct (INS NZ) as [(b & Hb & Hb1 & Hb2)|[IM1 IM2]]; [| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      exists b. split; [right; exact Hb| split; [exact Hb1| exact Hb2]]. }
    assert (AROF : aro RNG m1 (SPA + 64) 24).
    { split; [eapply unpoisoned_sub; [exact UP| clear; lia| clear; lia]|]. split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact R_fsi]. }
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold XI. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold SAV. fk_hold FRA. fk_hold FRB. fk_hold FRC. fk_hold STL. fk_hold STG. fk_hold XH. fk_hold XL. fk_hold XS. fk_hold SB1. fk_hold US. fk_hold UP. fk_hold ARO.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold S2. fk_hold F7. fk_hold ER. fk_hold EV.
    fk_hold FFSH. fk_hold FLSH. fk_hold SSH. fk_hold AFP. fk_hold SRCAP. fk_hold AROF. fk_hold ART1. fk_hold LBH'. fk_hold ASH'.
    zstep. zstep. zstep. zstep.                            (* [comment removed for export] *)
    zstep. unfold zd_findfsi_stmtA, APZD_FINDFSI in FINDFSI. gf_unhold.
    eapply evtF_cut.
    { eapply (FINDFSI L RNG st (FB1 FF :: LB)) with (lo := lo) (FSIP := SPA + 64) (SRC := SRC) (src := src) (off := off) (size := sz);
      first [ exact SB1 | exact OK | exact ROFF | exact R5 | exact SZ40 | exact OFS | exact SRCE | exact FRC | exact STL | exact AFP | exact ARO | exact AROF | exact MI | exact TP | reflexivity
            | clear - G2; lia
            | clear - SL; lia
            | clear; lia
            | clear - KLO G2; unfold KHIGH in *; lia
            | clear - G3 G5; lia
            | clear - S2 G3; lia
            | clear - S2 G2 G3; lia
            | clear - G4; Z.div_mod_to_equations; lia
            | intros _; split; [exact S1| split; [exact US| split; [exact RS1| exact RS2]]]
            | intros _; left; exact SRCAP
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & j0 & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & FC5).
    rd_retlit.
    (* [comment removed for export] *)
    set (W5 := [(SPA + 64, SPA + 64 + 24); (SPA - 4672, SPA)]) in MU5.
    assert (AW5 : aappW W5).
    { subst W5. unfold aappW. unfold KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - KLO G2 G3 G5; lia|]. apply Forall_cons; [cbn [fst snd]; clear - KLO G2; lia|]. apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> (X + k <= SPA + 64 \/ SPA + 88 <= X) -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k H1 H2 Hk. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - H1 H2 Hk FABL G1 G2 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    assert (DAPP : forall X k, (X + k <= lo \/ SPV <= X) -> ((6443008 <= X /\ X + k <= 2147446784) \/ (17594333495296 <= X /\ X + k <= ATOP)) -> 0 <= k ->
                   disjoint_from (W5 ++ fake_area L) X k -> True) by (intros; exact I).
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DSTK; [clear - G3; lia| clear - G3; lia| clear; lia])) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DSTK; [clear; lia| cbn; clear; lia| clear; lia])) as FRA5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU5 WM5 ltac:(apply DSTK; [clear; lia| cbn; clear; lia| clear; lia])) as FRB5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DSTK; [clear; lia| clear; lia| clear - G3; lia])) as STG5.
    (* [comment removed for export] *)
    assert (PFF : forall a, FF <= a < FF + 128 ->
              (in_fake (FB1 FF :: LB) a /\ outside [(SPA + 64, SPA + 64 + 24)] a) \/ (exists a', in_fake (FB1 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. left. split; [exists 1, FF, 128; split; [left; reflexivity| exact Ha]|]. cbn [outside]. clear - Ha F3 G1 G2. split; [lia| exact I]. }
    assert (PSF : forall a, SHF <= a < SHF + 16 -> (in_fake (FB1 FF :: LB) a /\ outside [(SPA + 64, SPA + 64 + 24)] a) \/ (exists a', in_fake (FB1 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 1, FF, 128; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XH ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XH5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XS ltac:(unfold DSH0; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    (* [comment removed for export] *)
    assert (XL5 : rw_cells bsegs m5 FLG [C1 (Z_to_bv 8 1)]).
    { rewrite L0. destruct (FFLAG _ _ _ _ _ 1 FF 128 AH5 ltac:(left; reflexivity)) as (X & _). exact X. }
    (* [comment removed for export] *)
    assert (FFR5' : ffr_pres W5 (FB1 FF :: LB) m1 m5).
    { eapply magree_mono; [exact FFR5|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      subst W5; cbn [outside app] in HO |- *. destruct HO as (O1 & _). exact (conj O1 I). }
    assert (DFSR : disjoint_from W5 SRC (zlen src)) by (subst W5; cbn [disjoint_from]; clear - S2 G2 G3 NZ; repeat split; lia).
    assert (UP5 : unpoisoned m5 (SPA + 64) (SPA + 88)).
    { eapply unpoisoned_munch; [exact UP | exact MU5 |]. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - FABL G1 G2 G3 G5 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ _ SRC (map (Z_to_bv 8) src) AH1 ltac:(rewrite length_map; exact SRCAP) ltac:(rewrite length_map; exact DFSR) MU5 FFR5' SB1) as SB5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH1 SRCAP NZ ltac:(unfold KEND; clear - SL ATR; lia) AW5 MU5 FFR5' US) as US5.
    assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO| exact MU5| exact WM5| exact AW5| exact FAB]).
    (* [comment removed for export] *)
    assert (FFR05 : ffr_pres [] LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR1|].
      eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
      - left. split; [exists c, A, k; split; [right; exact Hb| exact Ha]|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH1 (or_intror Hb)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        cbn [outside]. clear - B3 Ha G1 G2. split; [lia| exact I].
      - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU05 : munch ((SPV - 5024, SPV) :: fake_area L) m0 m5).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. unfold FAKESZ in *.
      clear - Hx F5 F6 G3. lia. }
    assert (WM05 : wmono bsegs m0 m5) by (exact (wmono_trans _ _ _ _ WM1 WM5)).
    assert (BI5 : BINV m5) by (split; [exact AH5| split; [exact FFR05| split; [exact MU05| split; [exact WM05| exact MI5]]]]).
    change (fsi_csize (find_frame_size_info src off sz)) with (find_frame_compressed_size src off sz) in FC5.
    set (fsz := find_frame_compressed_size src off sz) in *.
    pose proof (dd_fsi_csize_range src off sz OK ROFF ltac:(clear - R5 SZ40; lia)) as RFSZ. fold fsz in RFSZ.
    (* [comment removed for export] *)
    assert (XI5 : forall cs, rw_cells bsegs m5 (SPA + 64) cs -> cells_size cs = 24%nat -> XINV m5).
    { intros cs C SZ. destruct (rw_cells_forget _ _ _ _ C) as [jz C']. rewrite SZ in C'.
      split; [exact BI5|]. split; [exact SAV5|]. split; [exists jA; exact FRA5|]. split; [exists jB; exact FRB5|]. split; [exists jz; exact C'|].
      split; [exact ST5|]. split; [exact STG5|]. split; [exists jH; exact XH5|]. split; [exact XL5|]. split; [exact XS5|].
      split; [exact SB5|]. split; [exact US5|]. split; [exact UP5| exact ARO5]. }
    clear MU5 WM5 FFR5 FFR5' PFF PSF DSTK DAPP AW5 DFSR SAV FRA FRB FRC STL STG XH XS XL SB1 US UP ARO AFP ART1 MI AH1 FFR1 MU1 WM1 XI.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold S2. fk_hold F7.
    fk_hold FFSH. fk_hold FLSH. fk_hold SSH. fk_hold SRCAP. fk_hold LBH'. fk_hold ASH'. fk_hold AROF.
    fk_hold SAV5. fk_hold FRA5. fk_hold FRB5. fk_hold STG5. fk_hold ST5. fk_hold XH5. fk_hold XS5. fk_hold XL5. fk_hold SB5. fk_hold US5. fk_hold UP5. fk_hold ARO5.
    fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold WM05. fk_hold BI5. fk_hold XI5. fk_hold ER. fk_hold EV.
    unfold fk_held in G_lo.
    zstep.                                                 (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 18446744073709551496) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases KE; zify_cond KE.                      (* [comment removed for export] *)
    - (* [comment removed for export] *)
      gf_unhold.
      assert (NE : zd_is_error fsz = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - KE RFSZ; lia).
      rewrite NE in ER.
      pose proof (find_frame_compressed_size_ok src OK off sz ltac:(change (2^64) with 18446744073709551616; clear - SZ40; lia) NE) as RF.
      unfold ZD_SKIPPABLEHEADERSIZE in RF. fold fsz in RF.
      (* [comment removed for export] *)
      fk_hold XS5. fk_hold SAV5. fk_hold FC5.
      try clear KXE KXA KXRD KXK KXMI. unfold fk_held in FC5, XS5, SAV5.
      eapply (PADV m5 off sz fsz total); [exact (XI5 _ FC5 eq_refl) | exact RF | exact ROFF | exact RSZ | exact ER | exact RT | exact RB].
    - zstep. gf_unhold. rewrite EV. eapply PXEXIT; [exact (XI5 _ FC5 eq_refl) | reflexivity |].
      rewrite ER. replace (zd_is_error fsz) with true by (symmetry; apply zd_is_error_true_iff; change (2^64) with 18446744073709551616; clear - KE RFSZ; lia).
      reflexivity.
  Qed.
End FD.
End CANSEC1.
