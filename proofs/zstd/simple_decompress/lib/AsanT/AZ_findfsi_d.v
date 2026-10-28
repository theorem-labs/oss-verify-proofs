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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c.
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

(* [comment removed for export] *)
Definition FSHB : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 B00; C1 (Z_to_bv 8 4);
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].

Lemma fshb_unp : forall (m : amem) FF, rw_cells bsegs m (shad FF) FSHB -> FF mod 8 = 0 -> 0 <= FF -> FF + 256 <= 2^47 ->
  unpoisoned m (FF + 112) (FF + 112 + 12).
Proof.
  intros m FF H F8 F0 FH. unfold FSHB in H. rewrite shad_div in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 BF2] _)) in H.
  destruct H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 B00] _)) in H. destruct H as [H14 H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 (Z_to_bv 8 4)] _)) in H. destruct H as [H15 _].
  pose proof (fk_byte_of_c1 m _ _ H14 ltac:(unfold ASHOFF; lia)) as R14. pose proof (fk_byte_of_c1 m _ _ H15 ltac:(unfold ASHOFF; lia)) as R15.
  split; [lia|]. split; [lia|]. intros G HG H1 H2.
  assert (E : G = FF / 8 + 14 \/ G = FF / 8 + 15) by (Z.div_mod_to_equations; lia).
  destruct E as [-> | ->].
  - exists (Z_to_bv 8 0). split; [| left; reflexivity]. rewrite <- R14. f_equal. f_equal. unfold ASHOFF. lia.
  - exists (Z_to_bv 8 4). split; [rewrite <- R15; f_equal; f_equal; unfold ASHOFF; lia|].
    right. change (sval (Z_to_bv 8 4)) with 4. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fsi_blocks_err : forall src ip rem nb, all_bytes src ->
  zd_is_error (cblock_ret (get_cblock_size src ip rem)) = true ->
  fsi_blocks src ip rem nb = FL_err (cblock_ret (get_cblock_size src ip rem)).
Proof.
  intros src ip rem nb OK E. rewrite (fsi_blocks_eq src OK).
  destruct (get_cblock_size src ip rem) as [[cbs bp]|]; cbn [cblock_ret] in *; [rewrite E|]; reflexivity.
Qed.
Lemma cblock_ret_range : forall src ip rem, all_bytes src ->
  0 <= cblock_ret (get_cblock_size src ip rem) < 18446744073709551616.
Proof.
  intros src ip rem OK. unfold get_cblock_size.
  destruct (rem <? ZD_blockHeaderSize); cbn [cblock_ret].
  - unfold ZERR, ZE_srcSize_wrong. lia.
  - pose proof (cblock_props_range (le24 src ip) (le24_range src OK ip)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
    unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected.
    destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia.
Qed.

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
  Lemma p_berr : forall m1 v j1 j2 w0 j24 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHB -> unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    RES = FSI_err v ->
    evtF bsegs RNG POST (STpc 0x845d0 m1 x1 x5 x6 x7 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC + off)) x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 v j1 j2 w0 j24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM XP XL XS UP FC ER.
    fs_geom.
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FC; [| reflexivity]. cbn [mk_CB_cells app] in FC.
    unfold FSHB in XS.
    pose proof (munch_refl [(FSIP, FSIP + 24); (SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fs_hold_geom. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL.
    fk_hold L4. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FLA. fk_hold S2. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold ER. fk_hold F7.
    zstep.                                                   (* [comment removed for export] *)
    zstep. fsip_up2 UP MUL. fsip_sh UPc RP2 8. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
    zstep.                                                   (* [comment removed for export] *)
    zstep. fsip_up2 UP MUL. fsip_sh UPc RP2 16. zstep. zstep. zstep. clear RDz RTz UPc.
    zstep.                                                   (* [comment removed for export] *)
    zstep. if_false.
    zstep. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
    zstep.                                                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep.                                       (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    gf_unhold.
    apply (rw_cells_merge bsegs _ SPA [] (FRL5 j1 j2) []) in FRA. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FRA.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']. cbn [cells_size csize Nat.add length] in FRA'.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add length] in XS'.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    eapply (PFIN m6 jfr _ shb _);
      [
      | eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - P2 G2 G3 GS KLO; unfold KHIGH in KLO; lia]
      | exact FRA'
      | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - P2 G2 G3 GS KLO; unfold KHIGH in KLO; lia]
      | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - P2 G2 G3 GS KLO; unfold KHIGH in KLO; lia]
      | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - F7 FFSH; lia]
      | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - F7 FFSH; lia]
      | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - L5 FLSH; lia]
      | exact XS'
      | rewrite ER; cbn [fsi_csize fsi_bound]; exact FC ].
    split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
    - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd]; left; left; clear - PL P2 G1 G2 G3; lia |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia].
    - eapply ffr_pres_trans; [exact FFR1|].
      apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 m6 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; exact MUL
        | exact WML ].
    - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_berr72 : forall m1 j1 j2 w0 j24 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHB -> unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    RES = FSI_err (ZERR ZE_srcSize_wrong) ->
    evtF bsegs RNG POST (STpc 0x845cc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC + off)) x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 j1 j2 w0 j24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31
           BI SAV FRA STL STG XM XP XL XS UP FC ER.
    fk_hold BI. fk_hold SAV. fk_hold FRA. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold UP. fk_hold FC. fs_hold_geom.
    zstep. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
    gf_unhold. eapply p_berr; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma p_dst : forall m1 h ipf bound nb' j1 j2 w0 j24 (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHZ -> unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    RES = FSI nb' (ipf - off) bound -> off <= ipf <= off + size -> 0 <= nb' < 2^40 -> 0 <= bound < 2^64 ->
    evtF bsegs RNG POST (STpc 0x84688 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 bound) x12 (Z_to_bv 64 FSIP) x14 x15 x16 x17 (Z_to_bv 64 nb') x19 (Z_to_bv 64 (SRC + off))
                              (Z_to_bv 64 (SRC + ipf)) (Z_to_bv 64 (FF + 32)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 h ipf bound nb' j1 j2 w0 j24 x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31
           (AH1 & FFR1 & MU1 & WM1 & MI) SAV FRA STL STG XM ZC XP XL XS UP FC ER BI BN BB.
    fs_geom.
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FC; [| reflexivity]. cbn [mk_CB_cells app] in FC.
    pose proof (munch_refl [(FSIP, FSIP + 24)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fs_hold_geom. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold ZC. fk_hold XS.
    fk_hold L4. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FLA. fk_hold S2. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold ER. fk_hold F7. fk_hold FFSH.
    zstep. fsip_up UP MUL. fsip_sh0 UPc RP2. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
    zstep.                                                   (* [comment removed for export] *)
    zstep. fsip_up UP MUL. fsip_sh UPc RP2 8. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
    zstep.                                                   (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    zstep. fsip_up UP MUL. fsip_sh UPc RP2 16. zstep. zstep. clear RDz RTz UPc.
    zstep.                                                   (* [comment removed for export] *)
    zstep. if_true.
    zstep.                                                   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    gf_unhold.
    apply (rw_cells_merge bsegs _ SPA [] (FRL5 j1 j2) []) in FRA. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FRA.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']. cbn [cells_size csize Nat.add length app] in FRA'.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. unfold FSHZ in XS'. cbn [cells_size csize Nat.add length] in XS'.
    apply (rw_cells_merge bsegs _ FSIP [] [C8 (Z_to_bv 64 nb')] _) in FC. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC.
    replace ((SRC + ipf) mod 18446744073709551616 - (SRC + off) mod 18446744073709551616) with (ipf - off) in FC
      by (rewrite !Z.mod_small; clear - BI SL SRCE OFS OFF0; unfold fk_held in *; lia).
    eapply (PFIN m6 jfr _ shb _);
      [
      | eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - P2 G2 G3; lia]
      | exact FRA'
      | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
      | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
      | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - F7; lia]
      | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - F7; lia]
      | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - L5; lia]
      | eapply rw_cells_transport; [exact XS' | exact MUL | exact WML | cbn; clear - PSH; lia]
      | rewrite ER; cbn [fsi_csize fsi_bound]; exact FC ].
    split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
    - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd]; left; left; clear - PL P2 G1 G2 G3; lia | constructor].
    - eapply ffr_pres_trans; [exact FFR1|].
      apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 m6 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WML ].
    - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_dfcs : forall m1 h ipf nb' j1 j2 w0 j24 (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHZ -> unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    get_frame_header src off size = FH_ok h ->
    RES = FSI nb' (ipf - off) (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb' * fh_bsmax h else fh_fcs h) ->
    off <= ipf <= off + size -> 0 <= nb' < 2^40 ->
    evtF bsegs RNG POST (STpc 0x84674 m1 x1 x5 x6 x7 x10 x11 x12 (Z_to_bv 64 FSIP) x14 x15 x16 x17 (Z_to_bv 64 nb') x19 (Z_to_bv 64 (SRC + off))
                              (Z_to_bv 64 (SRC + ipf)) (Z_to_bv 64 (FF + 32)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 h ipf nb' j1 j2 w0 j24 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31
           BI SAV FRA STL STG XM ZC XP XL XS UP FC GFH ER BIP BN.
    pose proof (get_frame_header_ok src OK off size h GFH) as (_ & _ & _ & RFCS & _ & RBSM & _ & RCK & _).
    change (2^64) with 18446744073709551616 in RFCS. unfold ZD_BLOCKSIZE_MAX in RBSM.
    unfold zfh_cells in ZC. pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
    fk_hold BI. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold UP. fk_hold FC. fk_hold ER. fs_hold_geom.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    (* [comment removed for export] *)
    fk_hold L4. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FLA. fk_hold S2. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold FFSH. fk_hold PSH.
    zstep.                                                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
                                                             (* [comment removed for export] *)
    fk_hold FRA.
    zstep. if_cases KU; zify_cond KU.
    - (* [comment removed for export] *)
      gf_unhold. eapply (p_dst m1 h ipf (fh_fcs h) nb'); try eassumption.
      rewrite ER. replace (fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN) with false
        by (symmetry; apply Z.eqb_neq; unfold ZD_CONTENTSIZE_UNKNOWN; change (2^64) with 18446744073709551616; clear - KU RFCS; lia). reflexivity.
    - (* [comment removed for export] *)
      zstep. rewrite zx32w_small by (clear - RBSM; lia).
      zstep.
      replace ((nb' * fh_bsmax h) mod 18446744073709551616) with (nb' * fh_bsmax h) by (rewrite Z.mod_small by (clear - BN RBSM; nia); reflexivity).
      gf_unhold. eapply (p_dst m1 h ipf (nb' * fh_bsmax h) nb'); try eassumption; [| clear - BN RBSM; nia].
      rewrite ER. replace (fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN) with true
        by (symmetry; apply Z.eqb_eq; unfold ZD_CONTENTSIZE_UNKNOWN; change (2^64) with 18446744073709551616; clear - KU RFCS; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_done : forall m1 h ip' rem' nb' j1 j2 w0 j24 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA (FRL5 j1 j2) -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) (zfh_cells h) -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF FSHZ -> unpoisoned m1 FSIP (FSIP + 24) -> rw_cells bsegs m1 FSIP [CB 24 j24] ->
    get_frame_header src off size = FH_ok h ->
    RES = fsi_fin off h (FL_done ip' rem' nb') ->
    off <= ip' -> 0 <= rem' -> ip' + rem' <= off + size -> 0 <= nb' -> 3 * nb' <= ip' - off ->
    evtF bsegs RNG POST (STpc 0x8461c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nb') x19 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (SRC + ip'))
                              (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 rem') x24 x28 x29 x30 x31).
  Proof.
    intros m1 h ip' rem' nb' j1 j2 w0 j24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x28 x29 x30 x31
           BI SAV FRA STL STG XM ZC XP XL XS UP FC GFH ER B1 B2 B3 B4 B5.
    pose proof (get_frame_header_ok src OK off size h GFH) as (_ & _ & _ & RFCS & _ & RBSM & _ & RCK & _).
    change (2^64) with 18446744073709551616 in RFCS. unfold ZD_BLOCKSIZE_MAX in RBSM.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI). fs_geom.
    assert (BN : 0 <= nb' < 2^40) by (clear - B1 B2 B3 B4 B5 N40 OFF0; lia).
    unfold zfh_cells in ZC.
    fk_hold BI. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XM. fk_hold XP. fk_hold XL. fk_hold XS. fk_hold ER. fs_hold_geom.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1.
    fk_hold L4. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FLA. fk_hold S2. fk_hold S3. fk_hold F8'. fk_hold L5. fk_hold FLSH. fk_hold SSH. fk_hold F7. fk_hold FFSH. fk_hold PSH.
    zstep. rewrite sx32w_small by (clear - RCK; lia).       (* [comment removed for export] *)
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zstep. zstep. gf_unhold. eapply (p_dfcs m1 h ip' nb'); try eassumption; [| clear - B1 B2 B3; lia].
      rewrite ER. unfold fsi_fin. rewrite KC. cbn [Z.eqb negb andb]. reflexivity.
    - zstep.                                                 (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        zstep. replace (SRC + ip' + 4) with (SRC + (ip' + 4)) by (clear; lia).
        gf_unhold. eapply (p_dfcs m1 h (ip' + 4) nb'); try eassumption; [| clear - B1 B2 B3 K3; lia].
        rewrite ER. unfold fsi_fin. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KC; lia).
        replace (rem' <? 4) with false by (symmetry; apply Z.ltb_ge; clear - K3; lia). reflexivity.
      + (* [comment removed for export] *)
        assert (ER' : RES = FSI_err (ZERR ZE_srcSize_wrong)).
        { unfold fk_held in ER. rewrite ER. unfold fsi_fin. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KC; lia).
          replace (rem' <? 4) with true by (symmetry; apply Z.ltb_lt; clear - K3; lia). reflexivity. }
        clear ER. unfold fk_held in FC, UP.
        apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FC; [| reflexivity]. cbn [mk_CB_cells app] in FC.
        pose proof (munch_refl [(FSIP, FSIP + 24)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
        fk_hold ZC.
                                                             (* [comment removed for export] *)
        zstep. fsip_up UP MUL. fsip_sh UPc RP2 8. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
        zstep. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        zstep.                                               (* [comment removed for export] *)
        zstep. fsip_up UP MUL. fsip_sh UPc RP2 16. zstep. zstep. zstep. clear RDz RTz UPc.
        zstep.                                               (* [comment removed for export] *)
        zstep. if_true.
        zstep. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
        zstep.                                               (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        gf_unhold.
        apply (rw_cells_merge bsegs _ SPA [] (FRL5 j1 j2) []) in FRA. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FRA.
        destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']. cbn [cells_size csize Nat.add length app] in FRA'.
        destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. unfold FSHZ in XS'. cbn [cells_size csize Nat.add length] in XS'.
        eapply (PFIN m6 jfr _ shb _);
          [
          | eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - P2 G2 G3; lia]
          | exact FRA'
          | eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
          | eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
          | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - F7; lia]
          | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - F7; lia]
          | eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - L5; lia]
          | eapply rw_cells_transport; [exact XS' | exact MUL | exact WML | cbn; clear - PSH; lia]
          | rewrite ER'; cbn [fsi_csize fsi_bound]; exact FC ].
        split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
        * eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
          constructor; [cbn [fst snd]; left; left; clear - PL P2 G1 G2 G3; lia | constructor].
        * eapply ffr_pres_trans; [exact FFR1|].
          apply ffr_pres_mono_nil1.
          eapply (fk_ffr_fin AI L RNG st LB m1 m1 m6 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24)]);
            [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
            | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - PL P2 G1 G2 G3; lia] | constructor]
            | constructor
            | apply ffr_pres_refl
            | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
            | exact WML ].
        * eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia.
  Qed.
End FS.
End CANSEC1.
