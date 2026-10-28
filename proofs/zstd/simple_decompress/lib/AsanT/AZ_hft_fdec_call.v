(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdHufFse.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface FsKit
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_fserd_iface AZ_fserd_err AZ_hft_bdt AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_hft_rstats_a AZ_hft_fdec_defs AZ_hft_fdec_epi AZ_hft_fdec_pro AZ_hft_fdec_close AZ_hft_fdec_mid AZ_hft_fdec_open.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac bcase K := if_cases K; zify_cond K.

Section CANSEC1. Context {rc : runConstT}.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Lemma land_m4h63 : forall x, 0 <= x < 4096 -> Z.land x 9223372036854775804 = 4 * (x / 4).
Proof.
  assert (B : forallb (fun x => Z.land x 9223372036854775804 =? 4 * (x / 4)) (map Z.of_nat (seq 0 4096)) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.
(* [comment removed for export] *)
Lemma land_m4h : forall x, 0 <= x < 4096 -> Z.land x 18446744073709551612 = 4 * (x / 4).
Proof.
  assert (B : forallb (fun x => Z.land x 18446744073709551612 =? 4 * (x / 4)) (map Z.of_nat (seq 0 4096)) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma read_ncount_err_codeA : forall nc0 maxSV buf e, all_bytes buf -> 0 <= maxSV -> maxSV + 1 <= FseNCount.Zlength nc0 ->
  read_ncount nc0 maxSV buf = Err e -> e = 20 \/ e = 44.
Proof.
  intros nc0 maxSV buf e HB HM HL E. unfold read_ncount in E. cbv zeta in E.
  destruct (Z.ltb_spec (FseNCount.Zlength buf) 8) as [S|S].
  - set (buf8 := buf ++ repeat 0 (Z.to_nat (8 - FseNCount.Zlength buf))) in *.
    assert (HB8 : all_bytes buf8).
    { subst buf8. apply Forall_all_bytes. apply Forall_app. split; [apply all_bytes_Forall; exact HB|].
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    assert (HL8 : Z.of_nat (length buf8) = 8) by (subst buf8; unfold FseNCount.Zlength in *; rewrite length_app, repeat_length; lia).
    destruct (read_ncount_body8 buf8 (maxSV + 1) nc0) as [[[[nc msv] tl] cs]|e'| |] eqn:B8; cbn [bind] in E; try discriminate E.
    + destruct (FseNCount.Zlength buf <? cs); [injection E as <-; left; reflexivity | discriminate E].
    + injection E as <-. destruct (read_body8_err_invA buf8 (maxSV + 1) nc0 e' ltac:(lia) HB8 ltac:(unfold FseNCount.Zlength in *; lia) B8) as [(_ & ->)|(_ & -> & _)]; [right|left]; reflexivity.
  - destruct (read_body8_err_invA buf (maxSV + 1) nc0 e ltac:(unfold FseNCount.Zlength in *; lia) HB ltac:(unfold FseNCount.Zlength in *; lia) E) as [(_ & ->)|(_ & -> & _)]; [right|left]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fdsh_unp : forall m FF, rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) FDSH -> FF mod 64 = 0 -> 0 <= FF -> FF + 64 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 32 + 4) /\ unpoisoned m (FF + 48) (FF + 48 + 4).
Proof.
  intros m FF H F64 F0 FH. unfold FDSH in H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
                                            C1 (Z_to_bv 8 18446744073709551601)] _) H) as [_ H4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H4.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 4)] _) H4) as [H4a H5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H5.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 18446744073709551602)] _) H5) as [_ H6]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H6.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 4)] _) H6) as [H6a _].
  assert (R4 : m (wa (FF / 8 + 2147450880 + 4)) = Some (Z_to_bv 8 4)) by (apply (rw_C1_high m _ _ H4a); lia).
  assert (R6 : m (wa (FF / 8 + 2147450880 + 4 + 1 + 1)) = Some (Z_to_bv 8 4)) by (apply (rw_C1_high m _ _ H6a); lia).
  split; (split; [lia|]; split; [lia|]; intros G HG H1 H2; exists (Z_to_bv 8 4); split;
    [ unfold ASHOFF | right; change (sval (Z_to_bv 8 4)) with 4; lia ]).
  - replace G with (FF / 8 + 4) by (Z.div_mod_to_equations; lia). replace (2147450880 + (FF / 8 + 4)) with (FF / 8 + 2147450880 + 4) by lia. exact R4.
  - replace G with (FF / 8 + 6) by (Z.div_mod_to_equations; lia). replace (2147450880 + (FF / 8 + 6)) with (FF / 8 + 2147450880 + 4 + 1 + 1) by lia. exact R6.
Qed.

(* [comment removed for export] *)
Lemma fd_ahull_sub : forall RNG (m : amem) A n A' n', ahull RNG m A n -> A <= A' -> A' + n' <= A + n -> ahull RNG m A' n'.
Proof.
  intros RNG m A n A' n' (RLO & RHI & H1 & H2 & REST) L1 L2. exists RLO, RHI. split; [lia|]. split; [lia|]. exact REST.
Qed.

(* [comment removed for export] *)
Lemma fd_ffr_frame_cells : forall W FF LB (m m' : amem) A cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m A cs -> FF <= A -> A + Z.of_nat (cells_size cs) <= FF + 64 ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells bsegs m' A cs.
Proof.
  intros W FF LB m m' A cs FP RC H1 H2 HO. eapply rw_cells_magree; [exact FP| exact RC|].
  intros a Ha. left. split; [| exact (HO a Ha)]. exists 0, FF, 64. split; [left; reflexivity| lia].
Qed.
Lemma fd_ffr_fshadow_cells : forall W FF LB (m m' : amem) cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) cs -> FF mod 8 = 0 -> 0 <= FF ->
  Z.of_nat (cells_size cs) <= 8 -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) cs.
Proof.
  intros W FF LB m m' cs FP RC F8 F0 SZ. eapply rw_cells_magree; [exact FP| exact RC|].
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  intros a Ha. right. exists (FF + 8 * (a - (FF / 8 + 2147450880))). split.
  - exists 0, FF, 64. split; [left; reflexivity|]. clear - Ha F8 SZ. Z.div_mod_to_equations. lia.
  - rewrite shad_div. unfold ASHOFF. clear - F8. Z.div_mod_to_equations. lia.
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis FHL : fake_heap_law AI.
Hypothesis READ : fse_read_any_stmtA AI rng_fs.

Section K.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Variables (SPV DST cap SRC n ml WK wksz lo FF : Z) (src : list byte).
  (* [comment removed for export] *)
  Hypotheses (ASH : ashort LB 3) (LBH : ablkLB LB) (RI : rng_aimg RNG) (RSTK2 : rng RNG lo (al_top L - lo)) (RFS : rng_fs L RNG)
             (BOT : ATOP + 4096 <= lo) (LO0 : 4096 <= lo) (LOS : lo <= SPV - 4992) (SPR : SPV + 16 < 2^47) (SPT : SPV + 16 < al_top L) (SP16 : SPV mod 16 = 0)
             (TP : tp = Z_to_bv 64 ATP) (KLO : KHIGH <= lo) (RSTK : rng RNG lo (SPV - lo))
             (AZS : azstk RNG m lo SPV) (AROC : aro_client RNG m).
  (* [comment removed for export] *)
  Hypotheses (INDST : ainblk LB DST cap) (INWK : ainblk LB WK wksz) (INSRC : ainimg LB SRC n)
             (RDST : 0 < cap -> rng RNG DST cap) (RSDST : 0 < cap -> rng RNG (shad DST) (shspan DST cap))
             (ABW : ablk WK (WK + wksz)) (RWK : rng RNG WK wksz) (RSWK : rng RNG (shad WK) (shspan WK wksz)) (HULLW : ahull RNG m WK wksz)
             (ABS : ablk SRC (SRC + n)) (RSRC : rng RNG SRC n) (RSSRC : rng RNG (shad SRC) (shspan SRC n)) (HULLS : ahull RNG m SRC n)
             (CAPR : 0 <= cap <= 65536) (DSTL : 4096 <= DST) (DSTH : DST + cap < 2^47)
             (NR : 0 <= n <= 65536) (SRCL : 4096 <= SRC) (SRCH : SRC + n < 2^47) (LSB : zlen src = n)
             (MLR : 0 <= ml <= 9) (WKL : 4096 <= WK) (WR : 0 <= wksz < 2^32) (WKH : WK + wksz < 2^47) (WKA : WK mod 4 = 0)
             (OFFDST : DST + cap <= lo \/ SPV <= DST) (OFFWK : WK + wksz <= lo \/ SPV <= WK) (OFFSRC : SRC + n <= lo \/ SPV <= SRC)
             (DSTWK : DST + cap <= WK \/ WK + wksz <= DST) (DSTSRC : DST + cap <= SRC \/ SRC + n <= DST) (WKSRC : WK + wksz <= SRC \/ SRC + n <= WK).
  (* [comment removed for export] *)
  Hypotheses (F64 : FF mod 64 = 0) (FH : ablk FF (FF + 64)) (FC : FF + 64 <= ATOP) (RFF : rng RNG FF 64) (RSFF : rng RNG (shad FF) 8)
             (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
             (FFA1 : al_fake L <= FF) (FFA2 : FF + 64 <= al_fake L + FAKESZ).
  (* [comment removed for export] *)
  Hypothesis FASTG : forall (mA : amem) (hs tl fast : Z) (tb : list Z),
    fdA_hyps RNG SPV (FSPB SPV) lo DST cap SRC n WK wksz (WK + 512) hs tl FF -> fdA_an RNG mA SPV (FSPB SPV) lo DST cap SRC n WK wksz (WK + 512) hs tl fast FF tb src -> fast = 1 ->
    fd_entK RNG (fd_qexit gp tp F fc mA SPV (FSPB SPV) lo DST cap FF) gp tp F fc mA SPV (FSPB SPV) lo DST cap SRC n hs WK wksz (WK + 512) FF 0xac0c4.
  Hypothesis NONFG : forall (mA : amem) (hs tl fast : Z) (tb : list Z),
    fdA_hyps RNG SPV (FSPB SPV) lo DST cap SRC n WK wksz (WK + 512) hs tl FF -> fdA_an RNG mA SPV (FSPB SPV) lo DST cap SRC n WK wksz (WK + 512) hs tl fast FF tb src -> fast = 0 ->
    fd_entK RNG (fd_qexit gp tp F fc mA SPV (FSPB SPV) lo DST cap FF) gp tp F fc mA SPV (FSPB SPV) lo DST cap SRC n hs WK wksz (WK + 512) FF 0xac2bc.
  Notation SPB := (FSPB SPV).
  Notation POST := (fse_dec_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation MUNCH := ([(DST, DST + cap); (WK, WK + wksz); (SPV - 4992, SPV)] ++ fake_area L).
  Notation WL := [(DST, DST + cap); (WK, WK + wksz)].

  (* [comment removed for export] *)
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

  (* [comment removed for export] *)
  Ltac fd_exit_side FFLAG FREL LBH INDST INWK FFD FH RFF RSFF RSTK RI :=
    lazymatch goal with
    | |- fake_flag_law _ _ => exact FFLAG
    | |- fake_release_law _ _ => exact FREL
    | |- ablkLB _ => exact LBH
    | |- ainblk _ _ cap => exact INDST
    | |- ainblk _ _ _ => exact INWK
    | |- forall b, In b _ -> _ => exact FFD
    | |- ablk _ _ => exact FH
    | |- rng _ (shad _) _ => exact RSFF
    | |- rng _ lo _ => exact RSTK
    | |- rng _ _ _ => exact RFF
    | |- rng_aimg _ => exact RI
    | |- _ \/ _ => idtac
    | |- mem_inv _ _ => assumption
    | |- rw_cells _ _ _ _ => eassumption
    | |- stk _ _ _ _ => assumption
    | |- munch _ _ _ => assumption
    | |- wmono _ _ _ => assumption
    | |- ffr_pres _ _ _ _ => assumption
    | |- AHEAP _ _ _ _ _ _ => assumption
    | |- _ => first [assumption | lia | unfold KHIGH; lia | lazymatch goal with |- ?G => idtac "EXIT-LEFT:" G end]
    end.

  (* [comment removed for export] *)
  Lemma fd_kcall : forall (m3 : amem) (jA' : list byte) (j32 j48 j64 j80 j24 : list byte) (tlw : word) (j36 j52 : list byte)
      (y5 y6 y7 y16 y28 y29 y30 y31 : word),
    AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
    munch ([(SPV - 4992, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
    rw_cells bsegs m3 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m3 SPB (FDFRAME jA' (Z_to_bv 64 DST) (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) j32 FF j48 j64 j80) ->
    rw_cells bsegs m3 FF (FDHDR FF (fflag L 0 FF) j24 tlw j36 j52) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) FDSH ->
    stk bsegs m3 lo SPB -> stk bsegs m3 (SPB + 120) (SPV + -104) ->
    stk bsegs m3 DST (DST + cap) -> (0 < cap -> unpoisoned m3 DST (DST + cap)) ->
    stk bsegs m3 WK (WK + wksz) -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
    bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
    512 <= wksz ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0xac008) (Z_to_bv 64 SPB) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
               (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 0) y16 (Z_to_bv 64 FF)
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 cap) (Z_to_bv 64 ml) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
               (Z_to_bv 64 WK) (Z_to_bv 64 wksz) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
          F (Z_to_bv 64 0xaaac0) fc None m3 (seg_rom bsegs)).
  Proof.
    intros until y31. intros AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3 SD3 UD3 SW3 UW3 SB3 US3 WGE.
    pose proof atop_range as ATR.
    pose proof (fspb_props SPV SP16) as (SPAB & SPA32).
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
    destruct (FHL _ _ _ _ _ AH3) as [FAB FABD].
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ WK (WK + 512) (WK + wksz) SW3 ltac:(lia)) as [WKN WKR].
    destruct (stk_open bsegs _ WK (WK + 512) WK 512%nat WKN ltac:(lia) ltac:(lia)) as (jn & NCC & _ & _).
    assert (LJN : length jn = 512%nat) by (destruct NCC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in NCC.
    destruct (u16s_of_bytes 256 jn LJN) as (rt0 & LRT0 & _ & ERT0). rewrite ERT0 in NCC. clear WKN ERT0 LJN.
    assert (LNC : 2 * zlen rt0 = 512) by (rewrite LRT0; reflexivity).
    pose proof SB3 as SRCZ. rewrite <- (bytes_of_unsigned src) in SRCZ.
    remember (map bv_unsigned src) as buf eqn:EBUF.
    assert (BUFL : zlen buf = n) by (subst buf; rewrite length_map; exact LSB).
    assert (BUFB : Forall (fun c => 0 <= c < 256) buf) by (subst buf; apply bytes_unsigned_range).
    clear EBUF.
    (* [comment removed for export] *)
    destruct (fdsh_unp m3 FF SHF3 F64 ltac:(lia) ltac:(lia)) as [UTL UMSV].
    pose proof FFC3 as FX. unfold FDHDR in FX.
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d982); C8 (Z_to_bv 64 0xabea0); CB 8 j24] _) FX) as [FH0 FX1].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FX1. clear FX.
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [C4 tlw] _) FX1) as [FTL FX2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FX2. clear FX1.
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [CB 12 j36] _) FX2) as [FJ36 FX3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FX3. clear FX2.
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [C4 (Z_to_bv 64 255)] _) FX3) as [FMSV FX4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FX4. clear FX3.
    lazymatch type of FTL with rw_cells _ _ ?a _ => replace a with (FF + 32) in FTL by (cbn; lia) end.
    lazymatch type of FJ36 with rw_cells _ _ ?a _ => replace a with (FF + 36) in FJ36 by (cbn; lia) end.
    lazymatch type of FMSV with rw_cells _ _ ?a _ => replace a with (FF + 48) in FMSV by (cbn; lia) end.
    lazymatch type of FX4 with rw_cells _ _ ?a _ => replace a with (FF + 52) in FX4 by (cbn; lia) end.
    (* [comment removed for export] *)
    assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact FH| exact LBH]).
    assert (ASH' : ashort (FB0 FF :: LB) 2) by (apply ashort_push; [exact ASH| lia]).
    assert (ART3 : art m3) by (exact (art_of_aheap AI _ _ _ _ _ AH3)).
    assert (AFP3 : afpre AI rng_fs L RNG st (FB0 FF :: LB) m3 lo SPB 2).
    { unfold afpre, astk. split; [exact AH3|]. split; [exact ASH'|]. split; [exact ART3|].
      split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact BOT|]. split; [lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [exact RSTK2| exact LBH']. }
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ WK wksz AH3 INWK ltac:(lia)) as DFW.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DST cap AH3 INDST ltac:(lia)) as DFD.
    assert (DFS : FF + 64 <= SRC \/ SRC + n <= FF).
    { destruct INSRC as [IB|[IM1 IM2]]; [| unfold AIMG_HI in IM2; lia].
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC n AH3 IB ltac:(lia)). lia. }
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (b & Hb & H1 & H2); exists b; split; [right; exact Hb| split; [exact H1| exact H2]]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (READ L RNG st (FB0 FF :: LB)) with (lo := lo) (rt0 := rt0) (buf := buf) (msv0 := 255) (tl0 := tlw) (NC := WK) (MSVP := FF + 48) (TLP := FF + 32) (BUF := SRC);
        rewrite ?LNC, ?BUFL.
      all: lazymatch goal with
           | |- afpre _ _ _ _ _ _ _ _ _ _ => exact AFP3
           | |- tp = _ => exact TP
           | |- mem_inv _ _ => exact MI3
           | |- u8arr _ _ _ _ => exact NCC
           | |- rw_cells _ _ (FF + 48) _ => exact FMSV
           | |- rw_cells _ _ (FF + 32) _ => exact FTL
           | |- bytes_at _ _ _ _ => exact SRCZ
           | |- Forall _ _ => exact BUFB
           | |- stk _ _ lo _ => exact STL3
           | |- areg _ _ WK _ => intros _; split; [eapply ablk_sub; [exact ABW| lia| lia]|]; split; [eapply unpoisoned_sub; [exact (UW3 ltac:(lia))| lia| lia]|];
                                 split; [eapply rng_sub; [exact RWK| lia| lia]|];
                                 destruct (shspan_sub WK wksz WK 512 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2]; eapply rng_sub; [exact RSWK| exact S1| exact S2]
           | |- areg _ _ (FF + 48) _ => intros _; split; [eapply ablk_sub; [exact FH| lia| lia]|]; split; [exact UMSV|]; split; [eapply rng_sub; [exact RFF| lia| lia]|];
                                       eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]
           | |- areg _ _ (FF + 32) _ => intros _; split; [eapply ablk_sub; [exact FH| lia| lia]|]; split; [exact UTL|]; split; [eapply rng_sub; [exact RFF| lia| lia]|];
                                       eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]
           | |- ainblk _ WK _ => apply INCONS; eapply ainblk_sub; [exact INWK| lia| lia]
           | |- ainblk _ _ _ => exists (FB0 FF); split; [left; reflexivity| cbn; lia]
           | |- ahull _ _ WK _ => eapply fd_ahull_sub; [eapply fk_ahull_pres; [exact WM03| exact HULLW]| lia| lia]
           | |- ahull _ _ SRC _ => eapply fk_ahull_pres; [exact WM03| exact HULLS]
           | |- aregU _ _ SRC _ => split; [exact ABS|]; split; [destruct (Z.eq_dec n 0) as [E0|NZ]; [rewrite E0, Z.add_0_r; split; [lia| split; [lia| intros G HG; lia]]| exact (US3 ltac:(lia))]|];
                                  split; [exact RSRC| exact RSSRC]
           | |- 0 < _ -> ainimg _ _ _ => intros _; destruct INSRC as [IB|IMG]; [left; apply INCONS; exact IB| right; exact IMG]
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
           | |- forall ms', _ => idtac
           | |- _ => first [lia | clear - WKA; Z.div_mod_to_equations; lia | clear - F64 FHa FHb FHc; Z.div_mod_to_equations; lia | lazymatch goal with |- ?G => idtac "LEFT:" G end]
           end. }
    cbv beta. intros ms' PO.
    destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & r & rt' & msvw & tlw' & -> & MU4 & WM4 & MI4 & ST4 & FFR4 & AH4 & NCC4 & LRT & FMSV4 & FTL4 & RR & RES).
    rd_retlit.
    rewrite LNC in MU4, FFR4.
    pose proof (ablk_lin _ _ FAB) as (FA1 & FA2 & FA3 & FA4). unfold AIMG_HI in FA1. unfold FAKESZ in *.
    pose proof (ablk_disj_band _ _ ABW) as DBW. pose proof (ablk_disj_band _ _ FH) as DBF. pose proof (ablk_disj_band _ _ ABS) as DBS. unfold KLS in DBW, DBF, DBS.
    pose proof (ablk_lin _ _ ABW) as (WB1 & _ & _ & _). unfold AIMG_HI in WB1.
    unfold KHIGH in KLO.
    (* [comment removed for export] *)
    assert (SHF4 : rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) FDSH)
      by (eapply (fd_ffr_fshadow_cells _ FF LB m3 m4); [exact FFR4| exact SHF3| clear - F64; Z.div_mod_to_equations; lia| lia| cbn; lia]).
    assert (OUTW : forall a, (FF <= a < FF + 32 \/ FF + 36 <= a < FF + 48 \/ FF + 52 <= a < FF + 64) ->
                   outside [(WK, WK + 512); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4)] a).
    { intros a Ha. cbn [outside]. clear - Ha DFW WGE. repeat split; lia. }
    assert (FH04 : rw_cells bsegs m4 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d982); C8 (Z_to_bv 64 0xabea0); CB 8 j24])
      by (eapply (fd_ffr_frame_cells _ FF LB m3 m4); [exact FFR4| exact FH0| lia| cbn; lia| intros a Ha; apply OUTW; cbn in Ha; lia]).
    assert (FX44 : rw_cells bsegs m4 (FF + 52) [CB 4 j52; C8 (Z_to_bv 64 (fflag L 0 FF))])
      by (eapply (fd_ffr_frame_cells _ FF LB m3 m4); [exact FFR4| exact FX4| lia| cbn; lia| intros a Ha; apply OUTW; cbn in Ha; lia]).
    assert (DSTK : forall A k, SPB <= A -> 0 <= k -> A + k <= SPV ->
                   disjoint_from ([(WK, WK + 512); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (SPB - 4672, SPB)] ++ fake_area L) A k).
    { intros A k H1 H2 H3. cbn [disjoint_from fake_area app]. unfold FAKESZ. rewrite !shad_div. unfold ASHOFF. clear - H1 H2 H3 OFFWK WGE FHc BOT LOS SPAB FA3 FA2 KLO.
      repeat split; first [lia | Z.div_mod_to_equations; lia]. }
    assert (FRB4 : rw_cells bsegs m4 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact FRB3| exact MU4| exact WM4| apply DSTK; cbn; lia]).
    assert (FRA4 : rw_cells bsegs m4 SPB (FDFRAME jA' (Z_to_bv 64 DST) (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) j32 FF j48 j64 j80))
      by (eapply rw_cells_transport; [exact FRA3| exact MU4| exact WM4| apply DSTK; cbn; lia]).
    assert (STG4 : stk bsegs m4 (SPB + 120) (SPV + -104))
      by (eapply stk_transport_disjoint; [exact STG3| exact MU4| exact WM4| apply DSTK; lia]).
    assert (FFR4' : ffr_pres [(WK, WK + 512); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (SPB - 4672, SPB)] (FB0 FF :: LB) m3 m4).
    { eapply ffr_pres_monoW; [exact FFR4|]. intros iv Hiv. cbn in Hiv |- *. clear - Hiv. tauto. }
    assert (SD4 : stk bsegs m4 DST (DST + cap)).
    { eapply (fd_fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; replace (DST + cap - DST) with cap by lia; exact INDST| | exact MU4| exact WM4| exact FFR4'| exact SD3].
      cbn [disjoint_from]. clear - DSTWK DFD OFFDST SPAB LOS CAPR WGE. repeat split; lia. }
    assert (WKR4 : stk bsegs m4 (WK + 512) (WK + wksz)).
    { eapply (fd_fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; eapply ainblk_sub; [exact INWK| lia| lia]| | exact MU4| exact WM4| exact FFR4'| exact WKR].
      cbn [disjoint_from]. clear - DFW OFFWK SPAB LOS WGE. repeat split; lia. }
    assert (AW4 : aappW [(WK, WK + 512); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (SPB - 4672, SPB)]).
    { unfold aappW. unfold KLOW, KHIGH. clear - DBW DBF KLO SPAB LOS WGE WR.
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (UD4 : 0 < cap -> unpoisoned m4 DST (DST + cap)).
    { intros CP. eapply (fd_fcall_unp_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; exact INDST| exact CP| unfold KEND; lia| exact AW4| exact MU4| exact FFR4'| exact (UD3 CP)]. }
    assert (UW4 : unpoisoned m4 WK (WK + wksz)).
    { eapply (fd_fcall_unp_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; exact INWK| lia| unfold KEND; lia| exact AW4| exact MU4| exact FFR4'| exact (UW3 ltac:(lia))]. }
    assert (HB4 : bytes_at bsegs m4 SRC src /\ (0 < n -> unpoisoned m4 SRC (SRC + n))).
    { destruct (Z.eq_dec n 0) as [E0|NZ].
      { rewrite E0 in *. destruct src; [| cbn [length] in LSB; lia]. split; [exact (fd_bytes_at_nil1 _ _ _ SB3)| intros; lia]. }
      destruct INSRC as [IBB | [IB1 IB2]].
      - split.
        + eapply (fd_fcall_bytes_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; rewrite LSB; exact IBB| | exact MU4| exact FFR4'| exact SB3].
          rewrite LSB. cbn [disjoint_from]. clear - WKSRC DFS OFFSRC SPAB LOS NZ NR WGE. repeat split; lia.
        + intros NP. eapply (fd_fcall_unp_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m4); [exact AH3| apply INCONS; exact IBB| exact NP| unfold KEND; lia| exact AW4| exact MU4| exact FFR4'| exact (US3 NP)].
      - unfold AIMG_HI in IB2. split.
        + eapply bytes_at_transport; [exact SB3| exact MU4|]. rewrite LSB. cbn [disjoint_from fake_area app]. unfold FAKESZ. rewrite !shad_div. unfold ASHOFF.
          clear - IB1 IB2 NZ NR FA1 FHa WB1 KLO SPAB LOS. repeat split; first [lia | Z.div_mod_to_equations; lia].
        + intros NP. eapply unpoisoned_munch; [exact (US3 NP)| exact MU4|]. cbn [disjoint_from fake_area app]. unfold FAKESZ. rewrite !shad_div. unfold ASHOFF.
          pose proof (ablk_disj_band _ _ FAB) as FABB. unfold KLS in FABB. clear - IB1 IB2 NZ NR FA1 FA2 FA3 FHa FHb WB1 DBW DBF FABB KLO SPAB LOS ATR BOT WGE. repeat split; Z.div_mod_to_equations; lia. }
    destruct HB4 as [SB4 US4].
    assert (AZS3 : azstk RNG m3 lo SPV).
    { eapply azstk_transport_F; [exact AZS| exact MU03| exact WM03| | exact FAB| unfold al_fake; clear; Z.div_mod_to_equations; lia| unfold FAKESZ; clear - FA3 BOT; lia| clear - LOS; lia].
      unfold aappW. apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; lia| apply Forall_nil]. }
    assert (AZS4 : azstk RNG m4 lo SPV).
    { eapply azstk_transport_F; [exact AZS3| exact MU4| exact WM4| exact AW4| exact FAB| unfold al_fake; clear; Z.div_mod_to_equations; lia| unfold FAKESZ; clear - FA3 BOT; lia| clear - LOS; lia]. }
    assert (AROC4 : aro_client RNG m4).
    { eapply aro_client_transport_F; [| exact MU4| exact WM4| exact AW4| exact FAB].
      eapply aro_client_transport_F; [exact AROC| exact MU03| exact WM03| | exact FAB].
      unfold aappW. apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; lia| apply Forall_nil]. }
    assert (MU04 : munch MUNCH m m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
      eapply munch_weaken; [| exact MU4]. intros x Hx. cbn [outside app fake_area] in *. unfold FAKESZ in *. clear - Hx FFA1 FFA2 SPAB WR WGE. lia. }
    assert (WM04 : wmono bsegs m m4) by (eapply wmono_trans; [exact WM03| exact WM4]).
    assert (FFR04 : ffr_pres WL LB m m4).
    { eapply ffr_pres_trans; [apply fd_ffr_pres_mono_nil; exact FFR03|].
      intros a Ha HP. apply (FFR4 a Ha). destruct HP as [[(c & A & k & Hin & Hr) HO]|(a' & (c & A & k & Hin & Hr) & E)].
      - left. split; [exists c, A, k; split; [right; exact Hin| exact Hr]|].
        pose proof (FFD _ Hin) as AP. cbn [ab_addr ab_size] in AP. cbn [outside] in HO |- *. clear - HO AP Hr WGE. repeat split; lia.
      - right. exists a'. split; [exists c, A, k; split; [right; exact Hin| exact Hr]| exact E]. }
    clear MU03 WM03 FFR03 FRB3 FRA3 STG3 SD3 UD3 SW3 UW3 SB3 US3 STL3 WKR NCC FH0 FTL FJ36 FMSV FX4 UTL UMSV ART3 AFP3 AZS3 SHF3 FFC3 MI3 OUTW DSTK.
    (* [comment removed for export] *)
    unfold FDFRAME in FRA4.
    pose proof (proj1 (rd_rw_cells_appA bsegs m4 FF [C8 (Z_to_bv 64 0x41b58ab3)] _) FH04) as [FF04 _].
    pose proof (proj1 (rd_rw_cells_appA bsegs m4 (FF + 52) [CB 4 j52] _) FX44) as [_ FF564]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FF564.
    lazymatch type of FF564 with rw_cells _ _ ?a _ => replace a with (FF + 56) in FF564 by (cbn; lia) end.
    assert (STA4 : stk bsegs m4 lo (SPV + -104)).
    { pose proof FRA4 as X. apply stk_of_rw_cells in X. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X.
      lazymatch type of X with stk _ _ _ ?e => replace e with (SPB + 120) in X by (cbn; lia) end.
      apply (stk_merge bsegs m4 lo SPB (SPV + -104) ST4); [| clear - SPAB LOS LO0; lia].
      apply (stk_merge bsegs m4 SPB (SPB + 120) (SPV + -104) X); [exact STG4| clear - SPAB; lia]. }
    assert (WKS4 : stk bsegs m4 WK (WK + wksz)).
    { pose proof NCC4 as X. apply rw_cells_of_u8arr in X. apply stk_of_rw_cells in X. cbn [cells_size csize] in X.
      rewrite u16s_length, length_map, LRT, LRT0 in X.
      lazymatch type of X with stk _ _ _ ?e => replace e with (WK + 512) in X by (cbn; lia) end.
      apply (stk_merge bsegs m4 WK (WK + 512) (WK + wksz) X WKR4). lia. }
    hide_all_disj.   (* [comment removed for export] *)
    pose proof (read_ncount_total rt0 255 buf (Forall_all_bytes _ BUFB) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia)) as TOT.
    (* [comment removed for export] *)
    assert (FA24of : forall mx,
              rw_cells bsegs mx SPB [CB 8 jA'; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 FF); CB 8 j32; C8 (Z_to_bv 64 FF); CB 16 j48; CB 16 j64; CB 40 j80] ->
              rw_cells bsegs mx (SPB + 24) [C8 (Z_to_bv 64 FF)]).
    { intros mx X.
      pose proof (proj1 (rd_rw_cells_appA bsegs mx SPB [CB 8 jA'; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] _) X) as [_ X1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X1.
      pose proof (proj1 (rd_rw_cells_appA bsegs mx _ [C8 (Z_to_bv 64 FF)] _) X1) as [X2 _].
      lazymatch type of X2 with rw_cells _ _ ?a _ => replace a with (SPB + 24) in X2 by (clear; lia) end. exact X2. }
    destruct RES as [(rt & msv & tl & hn & RN & -> & -> & -> & ->) | (e & RN & ->)].
    2:{ (* [comment removed for export] *)
        pose proof (read_ncount_err_codeA rt0 255 buf e (Forall_all_bytes _ BUFB) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) RN) as HE.
        zstep. zstep. bcase K1; [| exfalso; clear - K1 HE; lia].     (* [comment removed for export] *)
        eapply fd_exit_gen3c.
        all: try (lazymatch goal with |- rw_cells _ _ (SPB + 24) _ => eapply FA24of; exact FRA4 end).
        all: fd_exit_side FFLAG FREL LBH INDST INWK FFD FH RFF RSFF RSTK RI.
        left. unfold zd_is_error, ZE_maxCode. apply Z.ltb_lt. clear - K1. lia. }
    destruct TOT as [(rt' & msv' & tl' & n' & RN' & LRT' & MSVR & TLR & HNR & _ & _ & WS) | (e' & RN')]; [| rewrite RN in RN'; discriminate RN'].
    rewrite RN in RN'. injection RN' as <- <- <- <-.
    unfold FseNCount.Zlength in *.
    zstep. zstep. bcase K1; [exfalso; clear - K1 HNR BUFL NR; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    clear MU4 FFR4 FFR4'.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DSTT : DST + cap <= ATOP).
    { destruct (fk_inblk_ablk LB DST cap LBH INDST ltac:(clear - CAPR; lia)) as (A1 & N1 & AB1 & L1 & H1). pose proof (ablk_lin _ _ AB1) as (_ & _ & X3 & _). clear - H1 X3. lia. }
    (* [comment removed for export] *)
    zstep. rewrite (sx32w_small tl) by lia.   (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    zstep.
    zstep. bcase K2.                          (* [comment removed for export] *)
    1:{ replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply Z_to_bv_eqm; reflexivity).
        eapply fd_exit_gen.
        all: fd_exit_side FFLAG FREL LBH INDST INWK FFD FH RFF RSFF RSTK RI.
        left. reflexivity. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    zstep. rewrite (sx32w_small msv) by lia.  (* [comment removed for export] *)
    zstep. rewrite (sllw_pow2 tl) by lia.     (* [comment removed for export] *)
    assert (P2 : 32 <= 2^tl <= 512) by (split; [change 32 with (2^5); apply Z.pow_le_mono_r; lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep.                                    (* [comment removed for export] *)
    first [ progress replace ((2 ^ tl mod 18446744073709551616) ≪ 2) with (4 * 2^tl) by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia)
          | progress replace (2 ^ tl ≪ 2) with (4 * 2 ^ tl) by (rewrite Z.shiftl_mul_pow2 by lia; lia) ].
    zstep.                                    (* [comment removed for export] *)
    replace (1 ≪ (tl mod 64)) with (2^tl) by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.                                    (* [comment removed for export] *)
    zstep. zstep.                             (* [comment removed for export] *)
    replace ((msv + 1) ≪ 32) with ((msv + 1) * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep.                                    (* [comment removed for export] *)
    replace (((msv + 1) * 4294967296) ≫ 31) with (2 * (msv + 1)) by (rewrite Z.shiftr_div_pow2 by lia; change 4294967296 with (2 * 2^31); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    zstep.                                    (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    lazymatch goal with |- context [Z.land ?x ?msk] => replace (Z.land x msk) with (4 * (x / 4)) by (symmetry; first [apply land_m4h | apply land_m4h63]; clear - P2 MSVR; lia) end.
    set (need0 := 4 * ((4 * 2 ^ tl + 2 ^ tl + 2 * (msv + 1) + 19) / 4)).
    assert (NEED : 5 * 2^tl + 2 * (msv + 1) + 16 <= need0 <= 5 * 2^tl + 2 * (msv + 1) + 19) by (unfold need0; Z.div_mod_to_equations; lia).
    clearbody need0.
    zstep. zstep. bcase K3.                   (* [comment removed for export] *)
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply Z_to_bv_eqm; reflexivity).
      eapply fd_exit_gen. all: fd_exit_side FFLAG FREL LBH INDST INWK FFD FH RFF RSFF RSTK RI.
      left. reflexivity. }
    zstep.                                    (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 6 zstep.                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (WK + 512 + (4 * 2 ^ tl + 4)) with (WK + 516 + 4 * 2 ^ tl) by lia. replace (wksz - (4 * 2 ^ tl + 4) + -512) with (wksz - 516 - 4 * 2 ^ tl) by lia.
    zstep.                                    (* [comment removed for export] *)
    assert (LRT2 : zlen rt = 256) by (rewrite LRT, LRT0; reflexivity).
    destruct (stk_split bsegs _ (WK + 512) (WK + 516 + 4 * 2^tl) (WK + wksz) WKR4 ltac:(lia)) as [DTS WS2].
    pose proof NCC4 as NCB. destruct NCB as [NCB _].
    specialize (WS ltac:(lia)). destruct WS as (NGE & NSUM).
    assert (ART4 : art m4) by (exact (art_of_aheap AI _ _ _ _ _ AH4)).
    eapply evtF_cut.
    { eapply (fse_bdt_proofA RNG) with (lo := lo) (norm := rt); rewrite ?LRT2.
      all: lazymatch goal with
           | |- areg _ _ (WK + 512) _ => intros _; split; [eapply ablk_sub; [exact ABW| lia| lia]|]; split; [eapply unpoisoned_sub; [exact UW4| lia| lia]|];
                                         split; [eapply rng_sub; [exact RWK| lia| lia]|];
                                         destruct (shspan_sub WK wksz (WK + 512) (4 + 4 * 2^tl) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2]; eapply rng_sub; [exact RSWK| exact S1| exact S2]
           | |- areg _ _ _ _ => intros WP; split; [eapply ablk_sub; [exact ABW| lia| lia]|]; split; [eapply unpoisoned_sub; [exact UW4| lia| lia]|];
                                split; [eapply rng_sub; [exact RWK| lia| lia]|];
                                destruct (shspan_sub WK wksz (WK + 516 + 4 * 2^tl) (wksz - 516 - 4 * 2^tl) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2]; eapply rng_sub; [exact RSWK| exact S1| exact S2]
           | |- aro _ _ WK _ => split; [eapply unpoisoned_sub; [exact UW4| lia| lia]|]; split; [eapply rng_sub; [exact RWK| lia| lia]|];
                                destruct (shspan_sub WK wksz WK 512 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2]; eapply rng_sub; [exact RSWK| exact S1| exact S2]
           | |- art _ => exact ART4
           | |- astk _ _ _ => split; [unfold KHIGH; exact KLO| split; [eapply rng_sub'; [exact RSTK| lia]| exact RI]]
           | |- mem_inv _ _ => exact MI4
           | |- stk _ _ lo _ => exact ST4
           | |- stk _ _ (WK + 512) _ => replace (WK + 512 + 4 + 4 * 2 ^ tl) with (WK + 516 + 4 * 2^tl) by lia; exact DTS
           | |- stk _ _ _ _ => replace (WK + 516 + 4 * 2 ^ tl + (wksz - 516 - 4 * 2 ^ tl)) with (WK + wksz) by lia; exact WS2
           | |- bytes_at _ _ _ _ => exact NCB
           | |- forall i, _ -> _ => exact NGE
           | |- wsum _ = _ => exact NSUM
           | |- forall ms', _ => idtac
           | |- _ => first [lia | clear - WKA; Z.div_mod_to_equations; lia | unhide; clear - OFFWK SPAB P2 K3 NEED WGE WR MSVR; lia]
           end. }
    cbv beta. intros ms' PO. unfold fse_bdt_postA in PO.
    destruct PO as (v0 & v1 & v2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & m5 & rb & -> & MU5 & WM5 & MI5 & ST5 & WS5 & RBR & POSTB).
    rd_retlit.
    (* [comment removed for export] *)
    set (Wb := [(WK + 512, WK + 512 + 4 + 4 * 2 ^ tl); (WK + 516 + 4 * 2 ^ tl, WK + 516 + 4 * 2 ^ tl + (wksz - 516 - 4 * 2 ^ tl)); (SPB - 192, SPB)]) in MU5.
    assert (DJA : forall A k, (A + k <= WK + 512 \/ WK + wksz <= A) -> (A + k <= SPB - 192 \/ SPB <= A) -> 0 <= k -> disjoint_from Wb A k).
    { intros A k H1 H2 H3. subst Wb. cbn [disjoint_from]. clear - H1 H2 H3 P2 NEED K3 MSVR. repeat split; lia. }
    assert (DJS : forall X k, 0 <= X -> 0 <= k -> X + k <= ATOP -> disjoint_from Wb (shad X) (shad (X + k - 1) + 1 - shad X)).
    { intros X k H1 H2 H3. subst Wb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. unhide. clear - H1 H2 H3 P2 NEED K3 MSVR DBW WB1 SPAB KLO LOS ATR. repeat split; Z.div_mod_to_equations; lia. }
    unhide.
    assert (SHF5 : rw_cells bsegs m5 (Z.shiftr FF 3 + 2147450880) FDSH).
    { eapply rw_cells_transport; [exact SHF4| exact MU5| exact WM5|]. subst Wb. unfold FDSH. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      clear - BSF DBW WB1 P2 NEED K3 MSVR SPAB KLO LOS. repeat split; lia. }
    assert (FF05 : rw_cells bsegs m5 FF [C8 (Z_to_bv 64 0x41b58ab3)]) by (eapply rw_cells_transport; [exact FF04| exact MU5| exact WM5| apply DJA; cbn; clear - DFW FHc BOT LOS SPAB WGE; lia]).
    assert (FF565 : rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]) by (eapply rw_cells_transport; [exact FF564| exact MU5| exact WM5| apply DJA; cbn; clear - DFW FHc BOT LOS SPAB WGE; lia]).
    assert (FRB5 : rw_cells bsegs m5 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact FRB4| exact MU5| exact WM5| apply DJA; cbn; clear - OFFWK SPAB LOS WGE; lia]).
    assert (FRA5 : rw_cells bsegs m5 SPB [CB 8 jA'; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 FF); CB 8 j32; C8 (Z_to_bv 64 FF); CB 16 j48; CB 16 j64; CB 40 j80])
      by (eapply rw_cells_transport; [exact FRA4| exact MU5| exact WM5| apply DJA; cbn; clear - OFFWK SPAB LOS WGE; lia]).
    assert (STG5 : stk bsegs m5 (SPB + 120) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG4| exact MU5| exact WM5| apply DJA; clear - OFFWK SPAB LOS WGE; lia]).
    assert (SD5 : stk bsegs m5 DST (DST + cap)) by (eapply stk_transport_disjoint; [exact SD4| exact MU5| exact WM5| apply DJA; clear - DSTWK OFFDST SPAB LOS CAPR WGE; lia]).
    assert (NCC5 : u8arr bsegs m5 WK (u16s (map (Z_to_bv 64) rt))).
    { eapply u8arr_transport; [exact NCC4| exact MU5| exact WM5|]. rewrite u16s_length, length_map. apply DJA; clear - OFFWK SPAB LOS WGE LRT LRT0 LRT2; lia. }
    assert (SB5 : bytes_at bsegs m5 SRC src).
    { destruct (Z.eq_dec n 0) as [E0|NZ]; [rewrite E0 in *; destruct src; [exact (fd_bytes_at_nil1 _ _ _ SB4)| cbn [length] in LSB; lia]|].
      eapply bytes_at_transport; [exact SB4| exact MU5|]. rewrite LSB. apply DJA; clear - WKSRC OFFSRC SPAB LOS NR NZ WGE; lia. }
    assert (UD5 : 0 < cap -> unpoisoned m5 DST (DST + cap)) by (intros CP; eapply unpoisoned_munch; [exact (UD4 CP)| exact MU5| apply DJS; clear - DSTL CAPR DSTT; lia]).
    assert (UW5 : unpoisoned m5 WK (WK + wksz)) by (eapply unpoisoned_munch; [exact UW4| exact MU5| apply DJS; pose proof (ablk_lin _ _ ABW) as (_ & _ & WB3 & _); clear - WKL WR WB3; lia]).
    assert (US5 : 0 < n -> unpoisoned m5 SRC (SRC + n)) by (intros NP; eapply unpoisoned_munch; [exact (US4 NP)| exact MU5| apply DJS; pose proof (ablk_lin _ _ ABS) as (_ & _ & SB3' & _); clear - SRCL NR SB3'; lia]).
    assert (AWB : aappW Wb).
    { subst Wb. unfold aappW, KLOW, KHIGH. clear - DBW KLO SPAB LOS WGE WR P2 NEED K3 MSVR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (AZS5 : azstk RNG m5 lo SPV) by (eapply azstk_transport; [exact AZS4| exact MU5| exact WM5| exact AWB| clear - LOS; lia]).
    assert (AROC5 : aro_client RNG m5) by (eapply aro_client_transport; [exact AROC4| exact MU5| exact WM5| exact AWB]).
    assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|]. subst Wb.
      constructor; [cbn [fst snd]; apply (fk_acr_inblk AI); apply INCONS; eapply ainblk_sub; [exact INWK| clear; lia| clear - P2 NEED K3 MSVR; lia]|].
      constructor; [cbn [fst snd]; apply (fk_acr_inblk AI); apply INCONS; eapply ainblk_sub; [exact INWK| clear - P2; lia| clear - P2 NEED K3 MSVR; lia]|].
      constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LOS SPAB SPR; lia| constructor]. }
    assert (MU05 : munch MUNCH m m5).
    { eapply munch_trans; [exact MU04|]. eapply munch_weaken; [| exact MU5]. subst Wb. intros x Hx. cbn [outside app fake_area] in *. clear - Hx SPAB P2 NEED K3 MSVR WGE. lia. }
    assert (WM05 : wmono bsegs m m5) by (eapply wmono_trans; [exact WM04| exact WM5]).
    assert (FFR05 : ffr_pres WL LB m m5).
    { eapply ffr_pres_trans; [exact FFR04|]. unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU5| exact WM5]|]. subst Wb.
      intros a [((c & A & k & Hin & Ha) & OUT)|(a' & (c & A & k & Hin & Ha') & ->)].
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH4 ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        cbn [outside] in OUT |- *. clear - OUT Ha B3 BOT LOS SPAB P2 NEED K3 MSVR WGE. repeat split; lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH4 ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        cbn [outside]. rewrite shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha' B1 B3 DBW WB1 KLO LOS SPAB ATR P2 NEED K3 MSVR. repeat split; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    hide_all_disj.
    zstep. zstep. bcase K4.                   (* [comment removed for export] *)
    { (* [comment removed for export] *)
      unhide. destruct POSTB as [(RB0 & _) | (RBE & DTS5)]; [exfalso; clear - K4 RB0; lia|].
      assert (WKS5 : stk bsegs m5 WK (WK + wksz)).
      { pose proof NCC5 as X. apply rw_cells_of_u8arr in X. apply stk_of_rw_cells in X. cbn [cells_size csize] in X.
        rewrite u16s_length, length_map, LRT, LRT0 in X.
        lazymatch type of X with stk _ _ _ ?e => replace e with (WK + 512) in X by (cbn; lia) end.
        apply (stk_merge bsegs m5 WK (WK + 512) (WK + wksz) X); [| lia].
        apply (stk_merge bsegs m5 (WK + 512) (WK + 512 + 4 + 4 * 2^tl) (WK + wksz) DTS5); [| clear - P2 NEED K3 MSVR; lia].
        lazymatch type of WS5 with stk _ _ ?b ?e => replace (WK + 512 + 4 + 4 * 2^tl) with b by (clear; lia); replace (WK + wksz) with e by (clear; lia) end. exact WS5. }
      assert (STA5 : stk bsegs m5 lo (SPV + -104)).
      { pose proof FRA5 as X. apply stk_of_rw_cells in X. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X.
        lazymatch type of X with stk _ _ _ ?e => replace e with (SPB + 120) in X by (cbn; lia) end.
        apply (stk_merge bsegs m5 lo SPB (SPV + -104) ST5); [| clear - SPAB LOS LO0; lia].
        apply (stk_merge bsegs m5 SPB (SPB + 120) (SPV + -104) X); [exact STG5| clear - SPAB; lia]. }
      eapply fd_exit_gen3c.
      all: try (lazymatch goal with |- rw_cells _ _ (SPB + 24) _ => eapply FA24of; exact FRA5 end).
      all: fd_exit_side FFLAG FREL LBH INDST INWK FFD FH RFF RSFF RSTK RI.
      left. exact RBE. }
    (* [comment removed for export] *)
    unhide. destruct POSTB as [(RB0 & fast & tb & DTBL) | (RBE & _)]; [| exfalso; unfold zd_is_error, ZE_maxCode in RBE; apply Z.ltb_lt in RBE; clear - K4 RBE; lia].
    destruct DTBL as (HDR & CELU & TBLEN & FASTR & TBBY & TBOK).
    (* [comment removed for export] *)
    assert (ABD3 : AIMG_HI <= DST /\ DST + cap <= ATOP /\ (DST + cap <= KLS \/ KHIGH <= DST)).
    { destruct (fk_inblk_ablk LB DST cap LBH INDST ltac:(clear - CAPR; lia)) as (A1 & N1 & AB1 & L1 & H1).
      pose proof (ablk_lin _ _ AB1) as (X1 & X2 & X3 & X4). pose proof (ablk_disj_band _ _ AB1) as XD. clear - L1 H1 X1 X3 XD. unfold KLS, KHIGH in *. lia. }
    assert (RSSPB : rng RNG (shad SPB) 20).
    { pose proof AZS as AZS'. unfold azstk in AZS'. destruct AZS' as (RLO & RHI & _ & (R1 & R2 & R3 & R4 & R5 & R6) & _ & _ & R8).
      eapply rng_sub; [exact R8| |]; rewrite ?shad_div; unfold ASHOFF; clear - R1 R2 R3 R5 SPAB SPA32 LOS LO0; Z.div_mod_to_equations; lia. }
    assert (HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz (WK + 512) hn tl FF).
    { unfold fdA_hyps. repeat (simple apply conj).
      all: first [ exact RSSPB | exact ABD3 | exact RDST | exact RSDST | exact ABS | exact RSRC | exact RSSRC | exact ABW | exact RWK | exact RSWK | exact RI | exact RSTK
                 | exact FH | exact RFF | exact RSFF | exact F64 | reflexivity | unfold KHIGH; clear - KLO; lia
                 | clear - TLR K2 MLR; lia | clear - HNR BUFL NR; lia | clear - NEED K3 MSVR P2; lia | clear - DFS; lia
                 | lia ]. }
    (* [comment removed for export] *)
    assert (UD5' : unpoisoned m5 DST (DST + cap)).
    { destruct (Z.eq_dec cap 0) as [E0|NZ]; [| exact (UD5 ltac:(clear - NZ CAPR; lia))]. rewrite E0, Z.add_0_r. split; [clear - DSTL; lia|]. split; [clear - DSTH E0; lia|]. intros G HG. clear - HG. lia. }
    assert (US5' : unpoisoned m5 SRC (SRC + n)).
    { destruct (Z.eq_dec n 0) as [E0|NZ]; [| exact (US5 ltac:(clear - NZ NR; lia))]. rewrite E0, Z.add_0_r. split; [clear - SRCL; lia|]. split; [clear - SRCH E0; lia|]. intros G HG. clear - HG. lia. }
    assert (ART5 : art m5) by (exact (art_of_aheap AI _ _ _ _ _ AH5)).
    assert (WKLO5 : stk bsegs m5 WK (WK + 512)).
    { pose proof NCC5 as X. apply rw_cells_of_u8arr in X. apply stk_of_rw_cells in X. cbn [cells_size csize] in X.
      rewrite u16s_length, length_map, LRT, LRT0 in X. lazymatch type of X with stk _ _ _ ?e => replace e with (WK + 512) in X by (cbn; lia) end. exact X. }
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 SPB [CB 8 jA'] _) FRA5) as [FS0 FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 FF)] _) FR1) as [FA5 FR2].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2. clear FR1.
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 8 j32] _) FR2) as [FS64 FR3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR3. clear FR2.
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [C8 (Z_to_bv 64 FF)] _) FR3) as [FB5 FR4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR4. clear FR3.
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 16 j48] _) FR4) as [FJ2 FR5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR5. clear FR4.
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 16 j64] _) FR5) as [FJ1 FJB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FJB. clear FR5.
    lazymatch type of FA5 with rw_cells _ _ ?a _ => replace a with (SPB + 8) in FA5 by (clear; lia) end.
    lazymatch type of FS64 with rw_cells _ _ ?a _ => replace a with (SPB + 32) in FS64 by (clear; lia) end.
    lazymatch type of FB5 with rw_cells _ _ ?a _ => replace a with (SPB + 40) in FB5 by (clear; lia) end.
    lazymatch type of FJ2 with rw_cells _ _ ?a _ => replace a with (SPB + 48) in FJ2 by (clear; lia) end.
    lazymatch type of FJ1 with rw_cells _ _ ?a _ => replace a with (SPB + 64) in FJ1 by (clear; lia) end.
    lazymatch type of FJB with rw_cells _ _ ?a _ => replace a with (SPB + 80) in FJB by (clear; lia) end.
    apply stk_of_rw_cells in FS0. apply stk_of_rw_cells in FS64. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FS0, FS64.
    lazymatch type of FS0 with stk _ _ _ ?e => replace e with (SPB + 8) in FS0 by (clear; lia) end.
    lazymatch type of FS64 with stk _ _ _ ?e => replace e with (SPB + 40) in FS64 by (clear; lia) end.
    assert (AN : fdA_an RNG m5 SPV SPB lo DST cap SRC n WK wksz (WK + 512) hn tl fast FF tb src).
    { unfold fdA_an. split; [exact UD5'|]. split; [exact US5'|]. split; [exact UW5|]. split; [exact AZS5|]. split; [exact ART5|]. split; [exact AROC5|].
      split; [exact HDR|]. split; [exact CELU|]. split; [split; [exact TBLEN| split; [exact FASTR| split; [exact TBBY| exact TBOK]]]|].
      split; [lazymatch type of WS5 with stk _ _ ?b ?e => replace (WK + 512 + 4 + 4 * 2^tl) with b by (clear; lia); replace (WK + wksz) with e by (clear; lia) end; exact WS5|].
      split; [exact WKLO5|]. split; [exact SB5|]. split; [exact LSB|]. split; [exact FA5|]. split; [exact FB5|]. split; [exact FS0|]. split; [exact FS64|]. split; [exact STG5| exact MI5]. }
    assert (FR : fdA_fr AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m5 SPV DST cap WK wksz FF (fflag L 0 FF) (Z_to_bv 64 0x41b58ab3)).
    { unfold fdA_fr. split; [exact SHF5|]. split; [exact FF05|]. split; [exact FF565|]. split; [exact FRB5|]. split; [exact AH5|]. split; [exact MU05|]. split; [exact WM05| exact FFR05]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fd_mid RNG m5 SPV SPB lo DST cap SRC n WK wksz (WK + 512) hn tl fast FF tb src gp tp F fc HY AN
                     (fd_qexit gp tp F fc m5 SPV SPB lo DST cap FF) (FASTG m5 hn tl fast tb HY AN) (NONFG m5 hn tl fast tb HY AN));
        [exact FJ2| exact FJ1| exact FJB| exact SD5| exact ST5]. }
    cbv beta. intros ms' QE.
    eapply fd_close.
    all: lazymatch goal with
         | |- fake_flag_law _ _ => exact FFLAG
         | |- fake_release_law _ _ => exact FREL
         | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
         | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
         | |- fdA_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact FR
         | |- ablkLB _ => exact LBH
         | |- ainblk _ _ cap => exact INDST
         | |- ainblk _ _ _ => exact INWK
         | |- forall b, In b _ -> _ => exact FFD
         | |- fd_qexit _ _ _ _ _ _ _ _ _ _ _ _ => exact QE
         | |- _ => first [eassumption | lia | lazymatch goal with |- ?G => idtac "CLOSE-LEFT:" G end]
         end.
  Qed.
End K.
End Asm.
End CANSEC1.
