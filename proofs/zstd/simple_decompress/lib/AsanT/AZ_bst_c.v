(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem FseRdKit FseRdKit2 ZdWalkKit MemRange SepHide ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require AZ_fserd_err.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_kx AZ_blk_iface AZ_blk_iface2 AZ_fserd_iface AZ_bst_env AZ_bst_a AZ_bst_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kxa_norm ::= unfold shspan in *.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF5 := (Z_to_bv 8 18446744073709551605).

Notation MAGIC := (Z_to_bv 64 0x41b58ab3).
Notation RETIRED := (Z_to_bv 64 0x45e0360e).
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).
Notation B02 := (Z_to_bv 8 2).
Notation B04 := (Z_to_bv 8 4).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition BSHU : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B04; C1 BF2; C1 B04; C1 BF2;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B02;
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00].

(* [comment removed for export] *)
Lemma bshu_rd0 : forall (m : amem) FF k, rw_cells bsegs m (shad FF) BSHU -> 0 <= FF -> 0 <= k < 13 ->
  m (wa (ASHOFF + FF / 8 + 8 + k)) = Some (Z_to_bv 8 0).
Proof.
  intros m FF k H F0 Hk. unfold BSHU in H. rewrite shad_div in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B04; C1 BF2; C1 B04; C1 BF2] _)) in H. destruct H as [_ H].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  assert (STEP : forall a cs, rw_cells bsegs m a (C1 B00 :: cs) -> 0x625000 <= a -> m (wa a) = Some (Z_to_bv 8 0) /\ rw_cells bsegs m (a + 1) cs).
  { intros a cs Hc Ha. apply (proj1 (rw_cells_app bsegs _ _ [C1 B00] cs)) in Hc. destruct Hc as [Hx Hy].
    split; [exact (fk_byte_of_c1 m _ _ Hx Ha)| exact Hy]. }
  destruct (STEP _ _ H ltac:(unfold ASHOFF; lia)) as [R0 H1]. destruct (STEP _ _ H1 ltac:(unfold ASHOFF; lia)) as [R1 H2].
  destruct (STEP _ _ H2 ltac:(unfold ASHOFF; lia)) as [R2 H3]. destruct (STEP _ _ H3 ltac:(unfold ASHOFF; lia)) as [R3 H4].
  destruct (STEP _ _ H4 ltac:(unfold ASHOFF; lia)) as [R4 H5]. destruct (STEP _ _ H5 ltac:(unfold ASHOFF; lia)) as [R5 H6].
  destruct (STEP _ _ H6 ltac:(unfold ASHOFF; lia)) as [R6 H7]. destruct (STEP _ _ H7 ltac:(unfold ASHOFF; lia)) as [R7 H8].
  destruct (STEP _ _ H8 ltac:(unfold ASHOFF; lia)) as [R8 H9]. destruct (STEP _ _ H9 ltac:(unfold ASHOFF; lia)) as [R9 H10].
  destruct (STEP _ _ H10 ltac:(unfold ASHOFF; lia)) as [R10 H11]. destruct (STEP _ _ H11 ltac:(unfold ASHOFF; lia)) as [R11 H12].
  destruct (STEP _ _ H12 ltac:(unfold ASHOFF; lia)) as [R12 _].
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
    [ rewrite <- R0 | rewrite <- R1 | rewrite <- R2 | rewrite <- R3 | rewrite <- R4 | rewrite <- R5 | rewrite <- R6
    | rewrite <- R7 | rewrite <- R8 | rewrite <- R9 | rewrite <- R10 | rewrite <- R11 | rewrite <- R12 ]; f_equal; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma bshu_rd4 : forall (m : amem) FF, rw_cells bsegs m (shad FF) BSHU -> 0 <= FF ->
  m (wa (ASHOFF + FF / 8 + 4)) = Some (Z_to_bv 8 4) /\ m (wa (ASHOFF + FF / 8 + 6)) = Some (Z_to_bv 8 4) /\ m (wa (ASHOFF + FF / 8 + 21)) = Some (Z_to_bv 8 2).
Proof.
  intros m FF H F0. unfold BSHU in H. rewrite shad_div in H.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1] _) H) as [_ H4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H4.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 B04] _) H4) as [H4a H5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H5.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 BF2] _) H5) as [_ H6]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H6.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 B04] _) H6) as [H6a H7]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H7.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 BF2; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00] _) H7) as [_ H21].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H21.
  pose proof (proj1 (rw_cells_app bsegs _ _ [C1 B02] _) H21) as [H21a _].
  split; [| split].
  - replace (ASHOFF + FF / 8 + 4) with (ASHOFF + FF / 8 + Z.of_nat 4) by lia. apply (fk_byte_of_c1 m _ _ H4a). unfold ASHOFF; lia.
  - replace (ASHOFF + FF / 8 + 6) with (ASHOFF + FF / 8 + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1) by lia. apply (fk_byte_of_c1 m _ _ H6a). unfold ASHOFF; lia.
  - replace (ASHOFF + FF / 8 + 21) with (ASHOFF + FF / 8 + Z.of_nat 4 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 14) by lia. apply (fk_byte_of_c1 m _ _ H21a). unfold ASHOFF; lia.
Qed.

(* [comment removed for export] *)
Lemma bshu_unp : forall (m : amem) FF, rw_cells bsegs m (shad FF) BSHU -> FF mod 256 = 0 -> 0 <= FF -> FF + 256 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 32 + 4) /\ unpoisoned m (FF + 48) (FF + 48 + 4) /\ unpoisoned m (FF + 64) (FF + 64 + 106).
Proof.
  intros m FF H F8 F0 FH. destruct (bshu_rd4 m FF H F0) as (R4 & R6 & R21).
  split; [| split]; (split; [lia|]; split; [lia|]; intros G HG H1 H2).
  - exists (Z_to_bv 8 4). split; [| right; change (sval (Z_to_bv 8 4)) with 4; lia].
    replace G with (FF / 8 + 4) by (Z.div_mod_to_equations; lia). rewrite <- R4. f_equal. f_equal. lia.
  - exists (Z_to_bv 8 4). split; [| right; change (sval (Z_to_bv 8 4)) with 4; lia].
    replace G with (FF / 8 + 6) by (Z.div_mod_to_equations; lia). rewrite <- R6. f_equal. f_equal. lia.
  - destruct (Z_lt_le_dec G (FF / 8 + 21)) as [LT|GE].
    + exists (Z_to_bv 8 0). split; [| left; reflexivity].
      replace (ASHOFF + G) with (ASHOFF + FF / 8 + 8 + (G - FF / 8 - 8)) by lia. apply (bshu_rd0 m FF (G - FF / 8 - 8) H F0). Z.div_mod_to_equations; lia.
    + exists (Z_to_bv 8 2). split; [| right; change (sval (Z_to_bv 8 2)) with 2; Z.div_mod_to_equations; lia].
      replace G with (FF / 8 + 21) by (Z.div_mod_to_equations; lia). rewrite <- R21. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma read_ncount_err_val : forall nc0 msv buf e, all_bytes buf -> 0 <= msv -> msv + 1 <= FseNCount.Zlength nc0 ->
  read_ncount nc0 msv buf = Err e -> e = 20 \/ e = 44.
Proof.
  intros nc0 msv buf e HB Hm HL. unfold read_ncount.
  destruct (Z.ltb_spec (FseNCount.Zlength buf) 8) as [Hs|Hl].
  - set (buf8 := buf ++ repeat 0 (Z.to_nat (8 - FseNCount.Zlength buf))).
    assert (HB8 : all_bytes buf8).
    { subst buf8. apply Forall_all_bytes. apply Forall_app. split; [apply all_bytes_Forall; exact HB|].
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    assert (HL8 : FseNCount.Zlength buf8 = 8) by (subst buf8; unfold FseNCount.Zlength in *; rewrite length_app, repeat_length; lia).
    destruct (read_ncount_body8 buf8 (msv + 1) nc0) as [[[[nc m1] tl] n]|e1| |] eqn:E; cbn [bind]; try discriminate.
    + destruct (Z.ltb_spec (FseNCount.Zlength buf) n); intros Q; [injection Q as <-; left; reflexivity | discriminate Q].
    + intros Q. injection Q as <-.
      destruct (AsanW.AZ_fserd_err.read_body8_err_invA buf8 (msv + 1) nc0 e1 ltac:(unfold FseNCount.Zlength in *; lia) HB8 ltac:(unfold FseNCount.Zlength in *; lia) E) as [[_ ->]|[_ [-> _]]]; auto.
  - intros E.
    destruct (AsanW.AZ_fserd_err.read_body8_err_invA buf (msv + 1) nc0 e ltac:(unfold FseNCount.Zlength in *; lia) HB ltac:(unfold FseNCount.Zlength in *; lia) E) as [[_ ->]|[_ [-> _]]]; auto.
Qed.

(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.
Lemma disjoint_from_sub1 : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.
Lemma fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.
Lemma fcall_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
  AHEAP AI L RNG st LB m0 -> ainblk LB X k -> 0 < k -> X + k <= KEND -> aappW W ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros L RNG st LB m0 m m' W X k AH (b & Hb & H1 & H2) Hk XH HW MU FP U.
  pose proof U as (U0 & U1 & _).
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [_ DSF].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & _) & _). pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4).
    eapply unpoisoned_munch; [exact U| exact MU|]. apply disjoint_from_app2.
    + apply aappW_shadow_disjoint; [exact HW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
    + eapply disjoint_from_sub1; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. rewrite !shad_div in Hs. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite !shad_div in Hs. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    destruct (FP s ltac:(rewrite !shad_div in Hs; unfold ASHOFF in Hs; unfold KEND in XH; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| symmetry; exact Ea])) as [E _].
    exact E.
Qed.
End FC.

Section BS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo FF SHF FLG : Z)
            (DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind) (dt0 wb0 : list byte) (srcb : list Z) (frw oldp nbw coldw : word).
  (* [comment removed for export] *)
  Hypothesis LD0 : zlen dt0 = 8 + 8 * 2^(kind_maxLog k).
  Hypothesis LW0 : 626 <= zlen wb0.
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) srcb.
  Hypothesis SLEN : zlen srcb <= 1048576.
  Hypothesis TYR : 0 <= ty <= 3.
  Hypothesis DTP8 : DTP mod 8 = 0.
  Hypothesis DTS4 : DTS mod 4 = 0.      (* [comment removed for export] *)
  Hypothesis WAL2 : W mod 2 = 0.
  Hypothesis BASE4 : BASE mod 4 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 5136 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_dts : ablk DTS (DTS + zlen dt0) /\ (DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS) /\ (FF + 256 <= DTS \/ DTS + zlen dt0 <= FF) /\ 4096 <= DTS /\ DTS + zlen dt0 < 2^47.
  Hypothesis G_dtp : ablk DTP (DTP + 8) /\ (DTP + 8 <= lo \/ SPV + 16 <= DTP) /\ (FF + 256 <= DTP \/ DTP + 8 <= FF) /\ 4096 <= DTP /\ DTP + 8 < 2^47.
  Hypothesis G_w : ablk W (W + zlen wb0) /\ (W + zlen wb0 <= lo \/ SPV + 16 <= W) /\ (FF + 256 <= W \/ W + zlen wb0 <= FF) /\ 4096 <= W /\ W + zlen wb0 < 2^47.
  Hypothesis G_src : ablk SRC (SRC + zlen srcb) /\ (SRC + zlen srcb <= lo \/ SPV <= SRC) /\ (FF + 256 <= SRC \/ SRC + zlen srcb <= FF)
                     /\ 4096 <= SRC /\ SRC + zlen srcb < 2^47.
  Hypothesis G_img : 4096 <= BASE /\ BASE + 212 <= AIMG_HI /\ 4096 <= BITS /\ BITS + 53 <= AIMG_HI.
  Hypothesis G_sep : (DTS + zlen dt0 <= DTP \/ DTP + 8 <= DTS) /\ (DTS + zlen dt0 <= W \/ W + zlen wb0 <= DTS) /\ (DTS + zlen dt0 <= SRC \/ SRC + zlen srcb <= DTS)
                     /\ (DTP + 8 <= W \/ W + zlen wb0 <= DTP) /\ (DTP + 8 <= SRC \/ SRC + zlen srcb <= DTP) /\ (W + zlen wb0 <= SRC \/ SRC + zlen srcb <= W).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ.
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (DTS + zlen dt0 <= FLG \/ FLG + 1 <= DTS) /\ (DTP + 8 <= FLG \/ FLG + 1 <= DTP) /\ (W + zlen wb0 <= FLG \/ FLG + 1 <= W).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV + 16 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_dts : rng RNG DTS (zlen dt0) /\ rng RNG (shad DTS) (shspan DTS (zlen dt0)).
  Hypothesis R_dtp : rng RNG DTP 8 /\ rng RNG (shad DTP) (shspan DTP 8).
  Hypothesis R_w : rng RNG W (zlen wb0) /\ rng RNG (shad W) (shspan W (zlen wb0)).
  Hypothesis R_src : rng RNG SRC (zlen srcb) /\ rng RNG (shad SRC) (shspan SRC (zlen srcb)).
  Hypothesis HSRC : ahull RNG m0 SRC (zlen srcb).
  Hypothesis R_img : aro RNG m0 BASE (4 * zlen (kind_base k)) /\ aro RNG m0 BITS (zlen (kind_bits k)).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.
  Hypothesis G_in : ainblk LB DTS (zlen dt0) /\ ainblk LB DTP 8 /\ ainblk LB W (zlen wb0) /\ (0 < zlen srcb -> ainimg LB SRC (zlen srcb)).
  (* [comment removed for export] *)
  Hypothesis G_af : ashort LB 3 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ KHIGH <= lo.
  Hypothesis TP : tp = Z_to_bv 64 ATP.

  Notation WR := [(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0)].
  Notation POST := (zd_buildseq_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DTS DTP W DFLT k ty (zlen srcb) frw oldp dt0 (length wb0) lo m0).

  Notation BS_EXIT := (AZ_bst_a.bs_exitA AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo FF SHF FLG
                        DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb frw oldp G_lo G_dts G_dtp G_w G_img G_sep G_ff G_flg RSTK RI R_img R_ff LBH).
  Notation BINV := (AZ_bst_a.BINV AI L RNG st LB m0 SPV FF DTS DTP W dt0 wb0).
  Notation BINV_STEP := (AZ_bst_b.binv_step AI fflag L RNG st LB m0 SPV SPA lo FF SHF FLG DTS DTP SRC W BASE BITS dt0 wb0 srcb
                          G_lo G_dts G_dtp G_w G_src G_img G_sep G_ff G_flg R_dts R_dtp R_w R_ff LBH G_in).
  Notation BE := (AZ_bst_b.BE AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo FF SHF FLG DTS DTP SRC W BASE BITS k dt0 wb0 srcb oldp nbw coldw).

  (* [comment removed for export] *)
  Notation STb pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 FF) x21 x22 (Z_to_bv 64 SHF) x24 x25 (Z_to_bv 64 SHB) x27 x28 x29 x30 x31)   (* [comment removed for export] *)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac open_be I := destruct I as (BI & SAV & (jA & jB & FRA) & STL & STG & (j3 & j4 & XF) & XL & XS & DTA & DTPC & WA & SB & BASEB & BITSB
                                      & ARGS & UD & UP & UW & US & UBASE & UBITS).

  Ltac be_geom :=
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6); pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6);
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7); pose proof R_ff as (RF1 & RF2 & RF3);
    pose proof G_dts as (D1 & D2 & D3 & D4 & D5); pose proof G_dtp as (P1 & P2 & P3 & P4 & P5); pose proof G_w as (W1 & W2 & W3 & W4 & W5);
    pose proof R_dts as (RD1 & RD2); pose proof R_dtp as (RP1 & RP2); pose proof R_w as (RW1 & RW2);
    pose proof G_src as (S1 & S2 & S3 & S4 & S5); pose proof G_sep as (DSP1 & DSP2 & DSP3 & DSP4 & DSP5 & DSP6); pose proof G_img as (IB1 & IB2 & IB3 & IB4);
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    hide G_lo; hide G_ff; hide G_flg; hide R_ff; hide G_dts; hide G_dtp; hide G_w; hide R_dts; hide R_dtp; hide R_w; hide G_src; hide G_sep; hide G_img; hide G_in; hide R_img.
  (* [comment removed for export] *)
  Ltac be_lits :=
    lazymatch goal with
    | G2 : lo <= SPV - 5136, G3 : SPV - 208 <= SPA <= SPV - 192, F1 : ablk FF (FF + 256), F3 : FF + 256 <= ATOP, F4 : SHF = shad FF, L1 : ablk FLG (FLG + 1), L2 : FLG + 1 <= ATOP,
      D1 : ablk DTS (DTS + zlen dt0), P1 : ablk DTP (DTP + 8), W1 : ablk W (W + zlen wb0),
      D2 : DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS, P2 : DTP + 8 <= lo \/ SPV + 16 <= DTP, W2 : W + zlen wb0 <= lo \/ SPV + 16 <= W,
      S2 : SRC + zlen srcb <= lo \/ SPV <= SRC, L4 : forall b, In b (FB2 FF :: LB) -> _ |- _ =>
      let FL := fresh "FL" in pose proof (fk_ablk_lits _ _ F1) as FL;
      let LL := fresh "LL" in pose proof (fk_ablk_lits _ _ L1) as LL;
      let DL := fresh "DL" in pose proof (fk_ablk_lits _ _ D1) as DL;
      let PL := fresh "PL" in pose proof (fk_ablk_lits _ _ P1) as PL;
      let WL := fresh "WL" in pose proof (fk_ablk_lits _ _ W1) as WL;
      let ATR := fresh "ATR'" in pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
      assert (F0' : 6443008 <= FF /\ FF + 256 <= ATOP) by (clear - FL F3 ATR; lia);
      assert (L0' : 6443008 <= FLG /\ FLG + 1 <= ATOP) by (clear - LL L2 ATR; lia);
      assert (D0' : 6443008 <= DTS /\ 0 <= zlen dt0) by (clear - DL; lia);
      assert (P0' : 6443008 <= DTP) by (clear - PL; lia);
      assert (W0' : 6443008 <= W /\ 0 <= zlen wb0) by (clear - WL; lia);
      assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity);
      assert (GS : SHB + 788992 <= SHF /\ SHF + 32 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
      assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (clear - FL GS ATR; lia);
      assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (clear - LL GS ATR; lia);
      assert (DSH : DTS + zlen dt0 <= SHF \/ SHF + 32 <= DTS) by (clear - DL GS ATR; lia);
      assert (PSH : DTP + 8 <= SHF \/ SHF + 32 <= DTP) by (clear - PL GS ATR; lia);
      assert (WSH : W + zlen wb0 <= SHF \/ SHF + 32 <= W) by (clear - WL GS ATR; lia);
      assert (D2' : DTS + zlen dt0 <= SPA \/ SPV + 16 <= DTS) by (clear - D2 G2 G3; lia);
      assert (P2' : DTP + 8 <= SPA \/ SPV + 16 <= DTP) by (clear - P2 G2 G3; lia);
      assert (W2' : W + zlen wb0 <= SPA \/ SPV + 16 <= W) by (clear - W2 G2 G3; lia);
      assert (S2' : SRC + zlen srcb <= SPA \/ SPV <= SRC) by (clear - S2 G2 G3; lia);
      let LFF := fresh "LFF" in pose proof (L4 _ ltac:(left; reflexivity)) as LFF; cbn [ab_addr ab_size] in LFF;
      clear FL LL DL PL WL ATR
    end.

  (* [comment removed for export] *)
  Ltac bs_close r :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      unfold fk_held in *; unhide;
      let BI2 := fresh "BI2" in
      assert (BI2 : BINV mx);
      [ lazymatch goal with MUL : munch _ _ mx, WML : wmono _ _ mx, BI : BINV _ |- _ =>
          eapply BINV_STEP; [exact BI| exact MUL| exact WML| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; first [match goal with HL : 16 <= zlen dt0 |- _ => clear - Hx HL end| clear - Hx]; lia] end
      | lazymatch goal with XF : rw_cells _ mx FF (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) |- _ =>
          change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c1] ++ [c2; c3; c4; c5; c6] ++ rest) in XF;
          apply rw_cells_app in XF; destruct XF as [XM XF]; apply rw_cells_app in XF; destruct XF as [_ XP]; cbn [cells_size csize Nat.add length app] in XM, XP;
          replace (FF + Z.of_nat 8 + Z.of_nat 240) with (FF + 248) in XP by (clear; lia);
          lazymatch goal with FRA : rw_cells _ mx SPA _, XS : rw_cells _ mx SHF _, SAV : rw_cells _ mx (SPV + -104) _ |- _ =>
            destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']; destruct (rw_cells_forget _ _ _ _ XS) as [shb XS'];
            fold (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in SAV; cbn [cells_size csize Nat.add length] in FRA', XS';
            eapply (BS_EXIT mx jfr _ shb _ _ _ r);
            [exact BI2| exact SAV| exact FRA'| eassumption| eassumption| exact XM| exact XP| eassumption| exact XS'| eassumption| | eassumption| | eassumption| | ]
          end
        end ]
    end.

  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FSERD : fse_read_any_stmtA AI rng_fs.
  Hypothesis BFSE : zd_buildfse_stmtA.

  (* [comment removed for export] *)
  Lemma bs_compA : forall m1 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word),
    BE m1 -> ty = 2 ->
    evtF bsegs RNG POST (STb 0x88ea4 m1 x1 x5 x6 x7 (Z_to_bv 64 2) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 ty) x21 x22
                              (Z_to_bv 64 SRC) (Z_to_bv 64 (zlen srcb)) x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I TY2. open_be I. be_geom. be_lits. unfold BSAVED in SAV. unfold BSH0 in XS.
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (L16 : 16 <= zlen dt0) by (pose proof (Z.pow_le_mono_r 2 8 (kind_maxLog k) ltac:(clear; lia) ltac:(clear - KM; lia)) as P8; change (2^8) with 256 in P8; clear - P8 LD0; lia).
    assert (LKB : zlen (kind_bits k) = kind_max k + 1 /\ zlen (kind_base k) = kind_max k + 1) by (destruct k; split; reflexivity).
    destruct LKB as [LKB1 LKB2].
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    hide_all_disj.
    fk_hold UD. fk_hold UP. fk_hold UW. fk_hold US. fk_hold UBASE. fk_hold UBITS. fk_hold BI. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold AH1.
    fk_hold SB. fk_hold BASEB. fk_hold BITSB.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (munch_refl [(SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    zstep. zstep. zstep. zstep.                            (* [comment removed for export] *)
    do 15 zstep.                                           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    change (rw_cells bsegs m2 SHF BSHU) in XS.
    (* [comment removed for export] *)
    pose proof (fk_ablk_lits _ _ S1) as SL. assert (S0' : 6443008 <= SRC) by (clear - SL; lia). hide SL.
    unfold fk_held in UD, UP, UW, US, UBASE, UBITS, BI, FFR1, MU1, WM1, AH1.
    assert (BI2 : BINV m2).
    { eapply BINV_STEP; [exact BI| exact MUL| exact WML| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia]. }
    pose proof BI2 as (AH2 & FFR2 & MU02 & WM02 & MI2).
    destruct (bshu_unp m2 FF ltac:(rewrite <- F4; exact XS) ltac:(clear - F2; Z.div_mod_to_equations; lia) ltac:(clear - F0'; lia) ltac:(clear - F0' ATR; lia)) as (UMSV & UTL & UNC).
    assert (DSs : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) -> disjoint_from [(SHF, SHF + 32)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF in *. split; [clear - X0 Hn Hb HF F2; Z.div_mod_to_equations; lia| exact I]. }
    assert (US2 : unpoisoned m2 SRC (SRC + zlen srcb)) by (eapply unpoisoned_munch; [exact US| exact MUL| apply DSs; unfold hidden in S3; clear - S0' S4 S5 DB S3; lia]).
    assert (UD2 : unpoisoned m2 DTS (DTS + zlen dt0)) by (eapply unpoisoned_munch; [exact UD| exact MUL| apply DSs; unfold hidden in D3; clear - D0' D4 D5 D3; lia]).
    assert (UP2 : unpoisoned m2 DTP (DTP + 8)) by (eapply unpoisoned_munch; [exact UP| exact MUL| apply DSs; unfold hidden in P3; clear - P0' P4 P5 P3; lia]).
    assert (UW2 : unpoisoned m2 W (W + zlen wb0)) by (eapply unpoisoned_munch; [exact UW| exact MUL| apply DSs; unfold hidden in W3; clear - W0' W4 W5 W3; lia]).
    assert (UBASE2 : unpoisoned m2 BASE (BASE + 4 * zlen (kind_base k))) by (eapply unpoisoned_munch; [exact UBASE| exact MUL| apply DSs; unfold AIMG_HI in IB2; clear - IB1 IB2 LKB2 KM F0'; lia]).
    assert (UBITS2 : unpoisoned m2 BITS (BITS + zlen (kind_bits k))) by (eapply unpoisoned_munch; [exact UBITS| exact MUL| apply DSs; unfold AIMG_HI in IB4; clear - IB3 IB4 LKB1 KM F0'; lia]).
    unfold fk_held in SB, BASEB, BITSB.
    assert (SB2 : bytes_at bsegs m2 SRC (map (Z_to_bv 8) srcb))
      by (eapply bytes_at_transport; [exact SB| exact MUL| rewrite length_map; cbn [disjoint_from fst snd]; unfold hidden in SL; clear - SL GS; lia]).
    assert (BASEB2 : bytes_at bsegs m2 BASE (u32s (map (Z_to_bv 64) (kind_base k))))
      by (eapply bytes_at_transport; [exact BASEB| exact MUL| rewrite u32s_length, length_map; cbn [disjoint_from fst snd]; unfold AIMG_HI in IB2; clear - IB2 LKB2 KM GS; lia]).
    assert (BITSB2 : bytes_at bsegs m2 BITS (map (Z_to_bv 8) (kind_bits k)))
      by (eapply bytes_at_transport; [exact BITSB| exact MUL| rewrite length_map; cbn [disjoint_from fst snd]; unfold AIMG_HI in IB4; clear - IB4 LKB1 KM GS; lia]).
    clear US UD UP UW UBASE UBITS DSs SB BASEB BITSB.
    (* [comment removed for export] *)
    pose proof G_af as (ASH & RFS & SPT & RSTKT & KLO).
    assert (LJ4 : length j4 = 212%nat) by (pose proof (proj1 (proj1 XF)) as Hwf; cbn in Hwf; clear - Hwf; tauto).
    apply (rw_cells_split_CB bsegs _ _ [C8 MAGIC; C8 (Z_to_bv 64 0x1a046); C8 (Z_to_bv 64 0x88cd8); CB 8 j3; C4 (Z_to_bv 64 (kind_max k))] 212 j4
             [C8 (Z_to_bv 64 FLG)] [12; 4; 12; 106; 78]%nat) in XF; [| reflexivity]. cbn [mk_CB_cells app] in XF.
    set (jb := firstn 12 j4) in XF. set (jt := firstn 4 (skipn 12 j4)) in XF. set (jc := firstn 12 (skipn 4 (skipn 12 j4))) in XF.
    set (jn := firstn 106 (skipn 12 (skipn 4 (skipn 12 j4)))) in XF. set (jr := firstn 78 (skipn 106 (skipn 12 (skipn 4 (skipn 12 j4))))) in XF.
    assert (LT4 : length jt = 4%nat) by (subst jt; rewrite firstn_length, skipn_length; clear - LJ4; lia).
    assert (LN : length jn = 106%nat) by (subst jn; rewrite firstn_length, !skipn_length; clear - LJ4; lia).
    lazymatch type of XF with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
      change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest) with ([c1; c2; c3; c4] ++ [c5] ++ [c6] ++ [c7] ++ [c8] ++ [c9] ++ rest) in XF end.
    apply rw_cells_app in XF. destruct XF as [XA XF]. cbn [cells_size csize Nat.add length] in XF.
    apply rw_cells_app in XF. destruct XF as [XM XF]. cbn [cells_size csize Nat.add length] in XF.
    apply rw_cells_app in XF. destruct XF as [XB XF]. cbn [cells_size csize Nat.add length] in XF.
    apply rw_cells_app in XF. destruct XF as [XT XF]. cbn [cells_size csize Nat.add length] in XF.
    apply rw_cells_app in XF. destruct XF as [XC XF]. cbn [cells_size csize Nat.add length] in XF.
    apply rw_cells_app in XF. destruct XF as [XN XR]. cbn [cells_size csize Nat.add length] in XR.
    match type of XM with rw_cells _ _ ?a _ => replace a with (FF + 32) in XM by (clear; lia) end.
    match type of XB with rw_cells _ _ ?a _ => replace a with (FF + 36) in XB by (clear; lia) end.
    match type of XT with rw_cells _ _ ?a _ => replace a with (FF + 48) in XT by (clear; lia) end.
    match type of XC with rw_cells _ _ ?a _ => replace a with (FF + 52) in XC by (clear; lia) end.
    match type of XN with rw_cells _ _ ?a _ => replace a with (FF + 64) in XN by (clear; lia) end.
    match type of XR with rw_cells _ _ ?a _ => replace a with (FF + 170) in XR by (clear; lia) end.
    rewrite <- (ABytes.le4_of_bytes jt LT4) in XT.
    assert (XT' : rw_cells bsegs m2 (FF + 48) [C4 (le_bytes_to_word jt)]).
    { destruct XT as [[Wf B] R]. split; [split|]; [ split; [exact I | exact (proj2 Wf)] | exact B | exact R ]. }
    clear XT. rename XT' into XT.
    apply u8arr_of_rw_cells in XN. destruct (u16s_of_bytes 53 jn LN) as (rt0 & LRT0 & _ & ERT0). rewrite ERT0 in XN.
    assert (NCL : zlen rt0 = 53) by (clear - LRT0; lia).
    (* [comment removed for export] *)
    assert (LBH' : ablkLB (FB2 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB2 FF :: LB) 2) by (apply ashort_push; [exact ASH| clear; lia]).
    assert (ART2 : art m2).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH2) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP : afpre AI rng_fs L RNG st (FB2 FF :: LB) m2 lo SPA 2).
    { unfold afpre, astk. split; [exact AH2|]. split; [exact ASH'|]. split; [exact ART2|].
      split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|].
      split; [exact RSTKT| exact LBH']. }
    assert (HULF : forall X n, FF <= X -> X + n <= FF + 256 -> ahull RNG m2 X n).
    { intros X nn H1 H2. exists FF, (FF + 256). split; [exact H1|]. split; [exact H2|]. split; [clear - F2; Z.div_mod_to_equations; lia|].
      split; [clear - F2; Z.div_mod_to_equations; lia|]. split; [clear - F0'; lia|]. split; [unfold KEND; clear - F0' ATR; lia|].
      rewrite <- F4. replace (shad (FF + 256) - SHF) with 32 by (rewrite F4, !shad_div; clear - F2; Z.div_mod_to_equations; lia).
      split; [exact (proj2 XS) | exact RF2]. }
    assert (HUS2 : ahull RNG m2 SRC (zlen srcb)) by (eapply fk_ahull_pres; [exact WM02| exact HSRC]).
    assert (INF : forall X n, FF <= X -> X + n <= FF + 256 -> ainblk (FB2 FF :: LB) X n).
    { intros X nn H1 H2. exists (FB2 FF). split; [left; reflexivity| cbn [ab_addr ab_size]; clear - H1 H2; lia]. }
    assert (ARF : forall X n, FF <= X -> X + n <= FF + 256 -> 0 <= n -> unpoisoned m2 X (X + n) -> areg RNG m2 X n).
    { intros X nn H1 H2 Hn U _. split; [eapply ablk_sub; [exact F1| exact H1| exact H2]|]. split; [exact U|].
      split; [eapply rng_sub'; [exact RF1| clear - H1 H2 Hn; lia]|].
      eapply rng_sub'; [exact RF2|]. unfold shspan. rewrite F4, !shad_div. unfold ASHOFF. clear - H1 H2 Hn F2. Z.div_mod_to_equations; lia. }
    pose proof (ARF (FF + 64) 106 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) UNC) as ANC.
    pose proof (ARF (FF + 32) 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) UMSV) as AMSV.
    pose proof (ARF (FF + 48) 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) UTL) as ATL.
    assert (ASRC : aregU RNG m2 SRC (zlen srcb)) by (split; [exact S1| split; [exact US2| exact R_src]]).
    pose proof G_in as (INd & INp & INw & INs). unfold hidden in INs.
    assert (INS' : 0 < zlen srcb -> ainimg (FB2 FF :: LB) SRC (zlen srcb)).
    { intros Hn. destruct (INs Hn) as [(b & Hb & H1 & H2)|IM]; [left; exists b; split; [right; exact Hb| split; [exact H1| exact H2]]| right; exact IM]. }
    (* [comment removed for export] *)
    hide_all_disj.
    fk_hold SAV. fk_hold FRA. fk_hold STG. fk_hold XA. fk_hold XB. fk_hold XC. fk_hold XR. fk_hold XL. fk_hold XS. fk_hold DTA. fk_hold DTPC. fk_hold WA. fk_hold ARGS.
    fk_hold BASEB2. fk_hold BITSB2.
    zstep. zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    unfold fk_held in *.
    eapply evtF_cut.
    { unfold fse_read_any_stmtA, APFSE_READ_BODY in FSERD.
      eapply (FSERD L RNG st (FB2 FF :: LB)) with (lo := lo) (NC := FF + 64) (MSVP := FF + 32) (TLP := FF + 48) (BUF := SRC) (rt0 := rt0) (buf := srcb) (msv0 := kind_max k);
      first [ exact AFP | exact TP | exact ANC | exact AMSV | exact ATL | exact ASRC | exact HUS2 | exact INS' | exact MI2 | exact XN | exact XM | exact XT | exact SB2 | exact FBY | exact STL
            | reflexivity
            | apply HULF; clear; lia
            | apply INF; clear; lia
            | clear - KM NCL SLEN S4 S5 F0' G1 G2 G3 G5 ATR; lia
            | unfold hidden in S2; clear - S2 G3; lia
            | unfold hidden in S3; clear - S3; lia
            | clear - F2; Z.div_mod_to_equations; lia
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
      all: replace (2 * zlen rt0) with 106 by (clear - NCL; lia).
      all: first [exact ANC | apply INF; clear; lia | apply HULF; clear; lia | unfold hidden in S3; clear - S3; lia]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & r & rt' & msvw & tlw
                     & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & ARR5 & LRT5 & MSV5 & TL5 & RR5 & RES5).
    rd_retlit.
    replace (2 * zlen rt0) with 106 in MU5, FFR5 by (clear - NCL; lia).
    (* [comment removed for export] *)
    destruct (FHL _ _ _ _ _ AH1) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL. hide FABL.
    set (Wc := [(FF + 64, FF + 64 + 106); (FF + 32, FF + 32 + 4); (FF + 48, FF + 48 + 4); (SPA - 4672, SPA)]) in MU5.
    assert (AW5 : aappW Wc).
    { subst Wc. unfold aappW. pose proof (ablk_disj_band _ _ F1) as DBF. unfold KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - DBF; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBF; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBF; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - KLO G2 G3; lia|]. apply Forall_nil. }
    assert (DSTK : forall X kk, SPA <= X -> 0 <= kk -> disjoint_from (Wc ++ fake_area L) X kk).
    { intros X kk H1 Hk. subst Wc. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *. unfold hidden in FABL.
      clear - H1 Hk FABL F3 F0' G1 G2 ATR KLO G3. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DSTK; clear; lia)) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as STG5.
    pose proof (rw_cells_transport _ _ _ _ _ _ ARGS MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as ARGS5.
    (* [comment removed for export] *)
    assert (PFF : forall a, FF <= a < FF + 256 -> ~ (FF + 64 <= a < FF + 170) -> ~ (FF + 32 <= a < FF + 36) -> ~ (FF + 48 <= a < FF + 52) ->
              (in_fake (FB2 FF :: LB) a /\ outside [(FF + 64, FF + 64 + 106); (FF + 32, FF + 32 + 4); (FF + 48, FF + 48 + 4)] a) \/ (exists a', in_fake (FB2 FF :: LB) a' /\ a = shad a')).
    { intros a Ha N1 N2 N3. left. split; [exists 2, FF, 256; split; [left; reflexivity| exact Ha]|]. cbn [outside]. clear - Ha N1 N2 N3. repeat split; lia. }
    assert (PSF : forall a, SHF <= a < SHF + 32 ->
              (in_fake (FB2 FF :: LB) a /\ outside [(FF + 64, FF + 64 + 106); (FF + 32, FF + 32 + 4); (FF + 48, FF + 48 + 4)] a) \/ (exists a', in_fake (FB2 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 2, FF, 256; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XA ltac:(cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XA5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XB ltac:(cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XB5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XC ltac:(cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XC5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XR ltac:(cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XR5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XS ltac:(unfold BSHU; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    assert (XL5 : rw_cells bsegs m5 FLG [C1 (Z_to_bv 8 1)]).
    { rewrite L0. destruct (FFLAG _ _ _ _ _ 2 FF 256 AH5 ltac:(left; reflexivity)) as (X & _). exact X. }
    (* [comment removed for export] *)
    assert (FFR5' : ffr_pres Wc (FB2 FF :: LB) m2 m5).
    { eapply AZ_bst_b.ffr_pres_mono; [| exact FFR5]. intros a Ho. subst Wc; cbn [outside app] in Ho |- *. destruct Ho as (O1 & O2 & O3 & _). repeat split; assumption. }
    assert (INL : forall X n, ainblk LB X n -> ainblk (FB2 FF :: LB) X n) by (intros X n (b & Hb & H); exists b; split; [right; exact Hb| exact H]).
    assert (DW5 : forall X n, (FF + 256 <= X \/ X + n <= FF) -> (X + n <= lo \/ SPV + 16 <= X) -> 0 <= n -> disjoint_from Wc X n).
    { intros X nn HF HS Hn. subst Wc. cbn [disjoint_from]. clear - HF HS Hn G2 G3. repeat split; first [exact I| lia]. }
    unfold hidden in D3, P3, W3, D2, P2, W2.
    pose proof (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 (INL _ _ INd) (DW5 _ _ D3 D2 (proj2 D0')) MU5 FFR5' (proj1 DTA)) as DTB5.
    assert (DTA5 : u8arr bsegs m5 DTS dt0) by (split; [exact DTB5| eapply wr_at_transport; [exact (proj2 DTA)| exact WM5]]). clear DTB5.
    pose proof (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 (INL _ _ INw) (DW5 _ _ W3 W2 (proj2 W0')) MU5 FFR5' (proj1 WA)) as WB5.
    assert (WA5 : u8arr bsegs m5 W wb0) by (split; [exact WB5| eapply wr_at_transport; [exact (proj2 WA)| exact WM5]]). clear WB5.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ _ [C8 oldp] AH2 (INL _ _ INp) (DW5 _ _ P3 P2 ltac:(clear; lia)) MU5 WM5 FFR5' DTPC) as DTPC5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 (INL _ _ INd) ltac:(clear - L16; lia) ltac:(unfold KEND; clear - D5; lia) AW5 MU5 FFR5' UD2) as UD5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 (INL _ _ INp) ltac:(clear; lia) ltac:(unfold KEND; clear - P5; lia) AW5 MU5 FFR5' UP2) as UP5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 (INL _ _ INw) ltac:(clear - LW0; lia) ltac:(unfold KEND; clear - W5; lia) AW5 MU5 FFR5' UW2) as UW5.
    hide D3. hide P3. hide W3. hide D2. hide P2. hide W2.
    assert (DIMG : forall X n, 0 <= X -> X + n <= 6443008 -> 0 <= n -> disjoint_from (Wc ++ fake_area L) X n /\ disjoint_from (Wc ++ fake_area L) (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 XH Hn. subst Wc. unfold hidden in FABL. pose proof (fk_ablk_lits _ _ F1) as FL. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - X0 XH Hn FABL FL G1 G2 ATR KLO G3. unfold KHIGH in KLO. split; repeat split; try exact I; Z.div_mod_to_equations; lia. }
    unfold AIMG_HI in IB2, IB4.
    destruct (DIMG BASE (4 * zlen (kind_base k)) ltac:(clear - IB1; lia) ltac:(clear - IB2 LKB2 KM; lia) ltac:(clear - LKB2 KM; lia)) as [DB1 DB2].
    destruct (DIMG BITS (zlen (kind_bits k)) ltac:(clear - IB3; lia) ltac:(clear - IB4 LKB1 KM; lia) ltac:(clear - LKB1 KM; lia)) as [DI1 DI2].
    assert (BASEB5 : bytes_at bsegs m5 BASE (u32s (map (Z_to_bv 64) (kind_base k))))
      by (eapply bytes_at_transport; [exact BASEB2| exact MU5| rewrite u32s_length, length_map; replace (Z.of_nat (4 * length (kind_base k))) with (4 * zlen (kind_base k)) by (clear; lia); exact DB1]).
    assert (BITSB5 : bytes_at bsegs m5 BITS (map (Z_to_bv 8) (kind_bits k))) by (eapply bytes_at_transport; [exact BITSB2| exact MU5| rewrite length_map; exact DI1]).
    pose proof (unpoisoned_munch _ _ _ _ _ UBASE2 MU5 DB2) as UBASE5.
    pose proof (unpoisoned_munch _ _ _ _ _ UBITS2 MU5 DI2) as UBITS5.
    (* [comment removed for export] *)
    assert (FFR25 : ffr_pres WR LB m2 m5).
    { eapply magree_mono; [exact FFR5|]. intros a [[HF HO]|(a' & HF & Ha')].
      - left. destruct HF as (c & A & n & Hb & Ha). pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2 _ Hb) as AP. cbn [ab_addr ab_size] in AP.
        split; [exists c, A, n; split; [right; exact Hb| exact Ha]|]. cbn [outside]. clear - AP Ha. repeat split; try exact I; lia.
      - right. exists a'. split; [| exact Ha']. destruct HF as (c & A & n & Hb & Ha). exists c, A, n; split; [right; exact Hb| exact Ha]. }
    assert (BI5 : BINV m5).
    { split; [exact AH5|]. split; [eapply ffr_pres_trans; [exact FFR2| exact FFR25]|]. split; [| split; [exact (wmono_trans _ _ _ _ WM02 WM5)| exact MI5]].
      eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU5]. unfold sub_fp; subst Wc; unfold fake_area; cbn [outside app]; intros x Hx.
      clear - Hx F5 F6 G3. unfold FAKESZ in *. lia. }
    clear FFR25 PFF PSF DSTK DIMG DB1 DB2 DI1 DI2 AW5 DW5 FFR5' FFR5 INL.
    clear SAV FRA STG XA XB XC XR XL XS DTA DTPC WA ARGS XM XT XN BASEB2 BITSB2 UD2 UP2 UW2 UBASE2 UBITS2 UMSV UTL UNC US2 SB2 HUS2 ASRC ANC AMSV ATL ARF HULF INF AFP ART2 MI2 AH2 MU02 WM02 FFR2 BI2 BI MUL WML MU5 WM5.
    pose proof (Forall_all_bytes _ FBY) as ABY.
    assert (P2K : 2^9 >= 2^(kind_maxLog k)) by (apply Z.ge_le_iff, Z.pow_le_mono_r; clear - KM; lia). change (2^9) with 512 in P2K.
    (* [comment removed for export] *)
    assert (ERRK : forall xa1 xa5 : word,
      evtF bsegs RNG POST (STb 0x88f6c m5 (Z_to_bv 64 0x88f08) z5 z6 z7 (Z_to_bv 64 (2^64 - 20)) xa1 z12 z13 z14 xa5 z16 z17
                           (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 64)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 r) (Z_to_bv 64 (zlen srcb)) x27 z28 z29 z30 z31)).   (* [comment removed for export] *)
    { intros xa1 xa5. hide_all_disj.
      pose proof (munch_refl [(SHF, SHF + 32); (FF, FF + 8)] m5) as MUL. pose proof (wmono_refl bsegs m5) as WML.
      unfold BSHU in XS5. fk_hold BI5. fk_hold UD5. fk_hold UP5. fk_hold UW5. fk_hold UBASE5. fk_hold UBITS5. clear ARR5 MSV5 TL5 RES5.
      zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      do 15 zstep.
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      zstep. bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
      unfold fk_held in *. unhide.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      assert (BIB : BINV mB).
      { eapply BINV_STEP; [exact BI5| exact MUL| exact WML| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia]. }
      lazymatch type of XA5 with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in XA5 end.
      apply rw_cells_app in XA5. destruct XA5 as [XMAG _].
      lazymatch type of XR5 with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in XR5 end.
      apply rw_cells_app in XR5. destruct XR5 as [_ XP]. cbn [cells_size csize Nat.add length app] in XP.
      replace (FF + 170 + Z.of_nat 78) with (FF + 248) in XP by (clear; lia).
      destruct (rw_cells_forget _ _ _ _ FRA5) as [jfr FRA']. destruct (rw_cells_forget _ _ _ _ XS5) as [shb XS'].
      fold (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in SAV5. cbn [cells_size csize Nat.add length] in FRA', XS'.
      eapply (BS_EXIT mB jfr _ shb _ _ _ (2^64 - 20));
        [exact BIB| exact SAV5| exact FRA'| eassumption| eassumption| exact XMAG| exact XP| eassumption| exact XS'| eassumption| reflexivity| eassumption| reflexivity| eassumption| clear; lia| left; reflexivity]. }
    (* [comment removed for export] *)
    hide_all_disj.
    zstep. zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 (2^64 - 120)) by (apply Z_to_bv_eqm; reflexivity).
    zstep. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
    destruct RES5 as [(rt & msv & tl & n & RN & -> & -> & -> & ->) | (e & RN & ->)].
    2: { (* [comment removed for export] *)
      pose proof (read_ncount_err_val rt0 (kind_max k) srcb e ABY ltac:(clear - KM; lia) ltac:(unfold FseNCount.Zlength; clear - NCL KM; lia) RN) as EV.
      zstep. bcase KE; [| exfalso; rewrite ?unsigned_lit in KE by (clear - EV; lia); clear - KE EV; lia].
      apply ERRK. }
    destruct (read_ncount_total rt0 (kind_max k) srcb ABY ltac:(clear - KM; lia) ltac:(unfold FseNCount.Zlength; clear - NCL KM; lia))
      as [(rt2 & msv2 & tl2 & n2 & RN2 & LRT & MSVR & TLR & NR & ZER & KEEP & SUMS) | (e & RN2)]; rewrite RN in RN2; [| discriminate RN2].
    injection RN2 as En Etl Emsv Ert. subst rt2 msv2 tl2 n2.
    unfold FseNCount.Zlength in NR.
    zstep. bcase KE; [exfalso; rewrite ?unsigned_lit in KE by (clear - NR SLEN; lia); clear - KE NR SLEN; lia|].
    (* [comment removed for export] *)
    zstep. rewrite (sx32w_small tl) by (clear - TLR; lia).
    zstep.
    zstep. bcase K2; [rewrite ?unsigned_lit in K2 by (clear - TLR KM; lia); apply ERRK|].
    assert (TLK : tl <= kind_maxLog k) by (rewrite ?unsigned_lit in K2 by (clear - TLR KM; lia); clear - K2 TLR KM; lia). clear K2 KE ERRK.
    (* [comment removed for export] *)
    assert (PT2 : 2^tl <= 2^(kind_maxLog k)) by (apply Z.pow_le_mono_r; clear - TLK TLR; lia).
    assert (PT5 : 32 <= 2^tl) by (change 32 with (2^5); apply Z.pow_le_mono_r; clear - TLR; lia).
    assert (FFSPA : FF + 256 <= SPA - 16) by (clear - F3 G1 G2 G3; lia).
    assert (SHFSPA : SHF + 32 <= SPA - 16) by (unfold KHIGH in KLO; clear - GS KLO G2 G3; lia).
    assert (FLGSPA : FLG + 1 <= SPA - 16) by (clear - L2 G1 G2 G3; lia).
    try clear K2 KE ERRK.
    assert (D2s : DTS + zlen dt0 <= SPA - 16 \/ SPV + 16 <= DTS) by (try unfold hidden in D2; clear - D2 G2 G3; lia).
    assert (P2s : DTP + 8 <= SPA - 16 \/ SPV + 16 <= DTP) by (try unfold hidden in P2; clear - P2 G2 G3; lia).
    assert (W2s : W + zlen wb0 <= SPA - 16 \/ SPV + 16 <= W) by (try unfold hidden in W2; clear - W2 G2 G3; lia).
    hide_all_disj.
    zstep.                                                 (* [comment removed for export] *)
    zstep. rewrite (sx32w_small msv) by (clear - MSVR KM; lia).   (* [comment removed for export] *)
    pose proof (munch_refl [(SPA - 16, SPA)] m5) as MUL. pose proof (wmono_refl bsegs m5) as WML.
    fk_hold BASEB5. fk_hold BITSB5. fk_hold XS5. fk_hold BI5. fk_hold UD5. fk_hold UP5. fk_hold UW5. fk_hold UBASE5. fk_hold UBITS5.
    zstep.                                                 (* [comment removed for export] *)
    carve_frame 16%nat ST5.
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    unfold fk_held in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    (* [comment removed for export] *)
    assert (DSH6 : forall X nn, 0 <= X -> 0 <= nn -> X + nn <= 2^47 -> disjoint_from [(SPA + -16, SPA)] (shad X) (shad (X + nn - 1) + 1 - shad X)).
    { intros X nn H1 H2 H3. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. unfold KHIGH in KLO. split; [clear - H1 H2 H3 KLO G2 G3; Z.div_mod_to_equations; lia| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ XS5 MUL WML ltac:(unfold BSHU; cbn [disjoint_from cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SHFSPA; lia)) as XS6.
    pose proof (bytes_at_transport _ _ _ _ _ _ BASEB5 MUL ltac:(rewrite u32s_length, length_map; cbn [disjoint_from]; clear - IB2 LKB2 KM G1 G2 KLO G3; unfold KHIGH in KLO; lia)) as BASEB6.
    pose proof (bytes_at_transport _ _ _ _ _ _ BITSB5 MUL ltac:(rewrite length_map; cbn [disjoint_from]; clear - IB4 LKB1 KM G1 G2 KLO G3; unfold KHIGH in KLO; lia)) as BITSB6.
    pose proof (unpoisoned_munch _ _ _ _ _ UD5 MUL ltac:(apply DSH6; [clear - D0'; lia| clear - D0'; lia| clear - D5; lia])) as UD6.
    pose proof (unpoisoned_munch _ _ _ _ _ UP5 MUL ltac:(apply DSH6; [clear - P0'; lia| clear; lia| clear - P5; lia])) as UP6.
    pose proof (unpoisoned_munch _ _ _ _ _ UW5 MUL ltac:(apply DSH6; [clear - W0'; lia| clear - W0'; lia| clear - W5; lia])) as UW6.
    pose proof (unpoisoned_munch _ _ _ _ _ UBASE5 MUL ltac:(apply DSH6; [clear - IB1; lia| clear - LKB2 KM; lia| clear - IB2 LKB2 KM; lia])) as UBASE6.
    pose proof (unpoisoned_munch _ _ _ _ _ UBITS5 MUL ltac:(apply DSH6; [clear - IB3; lia| clear - LKB1 KM; lia| clear - IB4 LKB1 KM; lia])) as UBITS6.
    assert (BI6 : BINV m6).
    { eapply BINV_STEP; [exact BI5| exact MUL| exact WML| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx G3; lia]. }
    pose proof BI6 as (AH6 & FFR6 & MU06 & WM06 & MI6).
    clear XS5 BASEB5 BITSB5 UD5 UP5 UW5 UBASE5 UBITS5 BI5 AH5 DSH6.
    destruct (bshu_unp m6 FF ltac:(rewrite <- F4; exact XS6) ltac:(clear - F2; Z.div_mod_to_equations; lia) ltac:(clear - F0'; lia) ltac:(clear - F0' ATR; lia)) as (UMSV6 & UTL6 & UNC6).
    assert (ART6 : art m6).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH6) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (ARD : areg RNG m6 DTS (8 + 8 * 2^tl)).
    { intros _. split; [eapply ablk_sub; [exact D1| clear; lia| clear - PT2 LD0; lia]|]. split; [eapply unpoisoned_sub; [exact UD6| clear; lia| clear - PT2 LD0; lia]|].
      split; [eapply rng_sub'; [exact RD1| clear - PT2 LD0 PT5; lia]|].
      eapply rng_sub'; [exact RD2|]. pose proof (shspan_sub DTS (zlen dt0) DTS (8 + 8 * 2^tl) ltac:(clear; lia) ltac:(clear - PT5; lia) ltac:(clear - PT2 LD0; lia)) as [SH1 SH2]. clear - SH1 SH2; lia. }
    assert (ARW : areg RNG m6 W (zlen wb0)).
    { intros _. split; [exact W1|]. split; [exact UW6|]. split; [exact RW1| exact RW2]. }
    assert (ARNC : areg RNG m6 (FF + 64) 106).
    { intros _. split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia]|]. split; [exact UNC6|].
      split; [eapply rng_sub'; [exact RF1| clear; lia]|].
      eapply rng_sub'; [exact RF2|]. unfold shspan. rewrite F4, !shad_div. unfold ASHOFF. clear - F2. Z.div_mod_to_equations; lia. }
    unfold hidden in R_img. pose proof R_img as [(_ & RB1 & RB2) (_ & RT1 & RT2)].
    assert (AROB : aro RNG m6 BASE (4 * zlen (kind_base k))) by (split; [exact UBASE6| split; [exact RB1| exact RB2]]).
    assert (AROT : aro RNG m6 BITS (zlen (kind_bits k))) by (split; [exact UBITS6| split; [exact RT1| exact RT2]]).
    assert (ASTK6 : astk RNG lo (SPA + -16)).
    { split; [exact KLO|]. split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]. }
    (* [comment removed for export] *)
    set (N := Z.to_nat (8 + 8 * 2^tl)).
    rewrite <- (firstn_skipn N dt0) in DTA5. apply u8arr_app in DTA5. destruct DTA5 as [DTA6a DTA6b].
    assert (LNF : zlen (firstn N dt0) = 8 + 8 * 2^tl) by (rewrite firstn_length; subst N; clear - PT2 PT5 LD0; lia).
    rewrite LNF in DTA6b.
    assert (LSK : zlen (skipn N dt0) = zlen dt0 - (8 + 8 * 2^tl)) by (rewrite skipn_length; subst N; clear - PT2 PT5 LD0; lia).
    destruct (SUMS ltac:(clear - TLK KM; lia)) as [NGE NSUM].
    assert (ZRT : FseNCount.Zlength rt = 53) by (unfold FseNCount.Zlength; clear - LRT NCL LRT0; lia).
    hide_all_disj.
    eapply evtF_cut.
    { unfold zd_buildfse_stmtA, off_stack, apart in BFSE.
      eapply BFSE with (SPV := SPA + -16) (lo := lo) (DT := DTS) (NC := FF + 64) (BASE := BASE) (BITS := BITS) (W := W)
                       (maxSV := msv) (tl := tl) (k := k) (dt0 := firstn N dt0) (wb0 := wb0) (norm := rt);
      first [ exact DTA6a | exact LNF | exact WA5 | exact LW0 | exact (proj1 ARR5) | exact MSVR | exact NGE | exact NSUM | exact BASEB6 | exact BITSB6
            | exact ST5 | exact ARD | exact ARW | exact ARNC | exact AROB | exact AROT | exact ART6 | exact ASTK6 | exact MI6 | reflexivity
            | exact DTS4 | exact WAL2 | exact BASE4                                                  (* [comment removed for export] *)
            | lazymatch goal with |- (FF + 64) mod 2 = 0 => clear - F2; Z.div_mod_to_equations; lia end
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
      all: rewrite ?ZRT.
      all: [> clear - TLR TLK; lia
            | clear - MSVR KM; lia
            | clear - D4; lia
            | clear - D5 PT2 LD0; lia
            | clear - W4; lia
            | clear - W5; lia
            | clear - F0'; lia
            | clear - F0' ATR; lia
            | clear - IB1 IB2; lia
            | clear - IB3 IB4; lia
            | clear - G2 G3; lia
            | clear - KLO; unfold KHIGH in KLO; lia
            | clear - G2 G3 G5 KLO; unfold KHIGH in KLO; lia
            | unfold hidden in D2; clear - D2 PT2 LD0 G2 G3; lia
            | unfold hidden in W2; clear - W2 G2 G3; lia
            | left; clear - F3 G1; lia
            | left; clear - IB2 KLO; unfold KHIGH in KLO; lia
            | left; clear - IB4 KLO; unfold KHIGH in KLO; lia
            | unfold hidden in DSP2; clear - DSP2 PT2 LD0; lia
            | unfold hidden in D3; clear - D3 PT2 LD0; lia
            | unfold hidden in W3; clear - W3; lia
            | right; clear - IB2 D0'; lia
            | right; clear - IB4 D0'; lia
            | right; clear - IB2 W0'; lia
            | right; clear - IB4 W0'; lia
            | exact ARNC
            | clear - IB2; lia
            | clear - IB4; lia ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m7 & tb & wb' & -> & MU7 & WM7 & MI7 & ST7 & TB7 & TLOG & TOK & WA7 & WLEN).
    rd_retlit.
    (* [comment removed for export] *)
    assert (BI7 : BINV m7).
    { eapply BINV_STEP; [exact BI6| exact MU7| exact WM7| exact MI7| unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx PT2 LD0 G3; lia]. }
    assert (KLO' : 17594333495296 <= lo) by (unfold KHIGH in KLO; exact KLO).
    assert (LTB : zlen (seq_table_bytes tb) = 8 + 8 * 2^tl).
    { pose proof (seq_table_bytes_length tb) as STBL. pose proof TOK as (_ & TC & _). rewrite TLOG in TC. unfold FseNCount.Zlength in STBL, TC. clear - STBL TC; lia. }
    pose proof (ablk_disj_band _ _ D1) as DBD. pose proof (ablk_disj_band _ _ W1) as DBW. unfold KLS in DBD, DBW.
    assert (DSW7 : forall X nn, 0 <= X -> 0 <= nn -> X + nn <= 2^47 ->
              disjoint_from [(DTS, DTS + 8 + 8 * 2^tl); (W, W + zlen wb0); (SPA + -16 - 176, SPA + -16)] (shad X) (shad (X + nn - 1) + 1 - shad X)).
    { intros X nn H1 H2 H3. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
      split; [clear - H1 H2 H3 DBD PT2 LD0; Z.div_mod_to_equations; lia|].
      split; [clear - H1 H2 H3 DBW; Z.div_mod_to_equations; lia|].
      split; [clear - H1 H2 H3 KLO' G2 G3; Z.div_mod_to_equations; lia| exact I]. }
    pose proof (unpoisoned_munch _ _ _ _ _ UP6 MU7 ltac:(apply DSW7; [clear - P0'; lia| clear; lia| clear - P5; lia])) as UP7.
    clear BASEB6 BITSB6 UBASE6 UBITS6 UD6 UW6 AROB AROT ARD ARW ARNC ART6 ASTK6 UMSV6 UTL6 UNC6 MUL WML DSW7 AH6 FFR6 MU06 WM06 MI6 DTA6a WA5.
    hide DBD. hide DBW.
    unfold BSHU in XS6. fk_hold TB7. fk_hold DTA6b. fk_hold BI7. fk_hold BI6.
    assert (D2t : DTS + zlen dt0 <= SPA - 4928 \/ SPV + 16 <= DTS) by (unfold hidden in D2; clear - D2 G2 G3; lia).
    assert (P2t : DTP + 8 <= SPA - 4928 \/ SPV + 16 <= DTP) by (unfold hidden in P2; clear - P2 G2 G3; lia).
    assert (W2t : W + zlen wb0 <= SPA - 4928 \/ SPV + 16 <= W) by (unfold hidden in W2; clear - W2 G2 G3; lia).
    hide_all_disj.
    transport_after_call_hide bsegs m6 m7 MU7 WM7.
    unfold fk_held in DTA6b.
    assert (DJR : disjoint_from [(DTS, DTS + 8 + 8 * 2 ^ tl); (W, W + zlen wb0); (SPA + -16 - 176, SPA + -16)] (DTS + (8 + 8 * 2^tl)) (zlen (drop N dt0))).
    { cbn [disjoint_from]. rewrite LSK. unfold hidden in DSP2, D2t. repeat split; try exact I.
      - right. clear. lia.
      - clear - DSP2 PT2 PT5 LD0. lia.
      - clear - D2t PT2 PT5 LD0 G2 G3. lia. }
    pose proof (u8arr_transport _ _ _ _ _ _ DTA6b MU7 WM7 DJR) as DTR7. clear DJR.
    clear DTA6b. hide DSP2. hide D2t.
    zstep.                                                 (* [comment removed for export] *)
    release_frame FR0 ST7 SPA.
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (bs_sh_rd0 m7 DTP 8 DTP UP7 ltac:(clear; lia) ltac:(clear - DTP8; Z.div_mod_to_equations; lia) ltac:(clear - P4; lia) ltac:(clear - P5; lia)) as RDz.
    assert (RTz : rng RNG (Z.shiftr DTP 3 + SHB) 1).
    { eapply rng_sub'; [exact RP2|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold shspan. rewrite shad_div. unfold ASHOFF. clear - DTP8; Z.div_mod_to_equations; lia. }
    zstep. zstep. zstep.                                   (* [comment removed for export] *)
    zstep. if_false.                                       (* [comment removed for export] *)
    clear MU7 WM7. pose proof (munch_refl [(DTP, DTP + 8); (SHF, SHF + 32); (FF, FF + 8)] m7) as MUL2. pose proof (wmono_refl bsegs m7) as WML2.
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    hide_all_disj.
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    do 15 zstep.
    zstep. zstep. zstep.                                   (* [comment removed for export] *)
    zstep. bcase KF; [| exfalso; rewrite ?unsigned_lit in KF by (clear - F0'; lia); clear - KF F0'; lia].
    unfold fk_held in *. unhide.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    assert (BI9 : BINV m9).
    { eapply BINV_STEP; [exact BI7| exact MUL2| exact WML2| assumption| unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia]. }
    assert (DJT : disjoint_from [(DTP, DTP + 8); (SHF, SHF + 32); (FF, FF + 8)] DTS (zlen (map (Z_to_bv 8) (seq_table_bytes tb)))).
    { rewrite length_map. cbn [disjoint_from]. rewrite LTB. repeat split; try exact I.
      - clear - DSP1 PT2 PT5 LD0. lia.
      - clear - DSH PT2 PT5 LD0. lia.
      - clear - D3 PT2 PT5 LD0. lia. }
    pose proof (u8arr_transport _ _ _ _ _ _ TB7 MUL2 WML2 DJT) as TB9. clear DJT TB7.
    assert (DTA9 : u8arr bsegs m9 DTS (map (Z_to_bv 8) (seq_table_bytes tb) ++ drop N dt0)).
    { apply u8arr_app. split; [exact TB9|]. rewrite length_map, LTB. exact DTR7. }
    lazymatch type of XA5 with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in XA5 end.
    apply rw_cells_app in XA5. destruct XA5 as [XMAG _].
    lazymatch type of XR5 with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in XR5 end.
    apply rw_cells_app in XR5. destruct XR5 as [_ XP]. cbn [cells_size csize Nat.add length app] in XP.
    replace (FF + 170 + Z.of_nat 78) with (FF + 248) in XP by (clear; lia).
    destruct (rw_cells_forget _ _ _ _ FRA5) as [jfr FRA']. destruct (rw_cells_forget _ _ _ _ XS6) as [shb XS'].
    fold (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in SAV5. cbn [cells_size csize Nat.add length] in FRA', XS'.
    eapply (BS_EXIT m9 jfr _ shb _ _ _ n);
      [exact BI9| exact SAV5| exact FRA'| exact ST7| exact STG5| exact XMAG| exact XP| exact XL5| exact XS'| exact DTA9
      | apply Nat2Z.inj; rewrite length_app, length_map, Nat2Z.inj_add; clear - LTB LSK; lia
      | exact WA7| exact WLEN| exact DTPC5| clear - NR SLEN; lia| ].
    right. split; [clear - NR; lia|]. right. right. split; [right; exact TY2|]. split; [reflexivity|].
    exists tb. split; [exact TOK|].
    replace (length (seq_table_bytes tb)) with (length (map (Z_to_bv 8) (seq_table_bytes tb))) by apply length_map.
    rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
  Qed.
End BS.
End CANSEC1.
