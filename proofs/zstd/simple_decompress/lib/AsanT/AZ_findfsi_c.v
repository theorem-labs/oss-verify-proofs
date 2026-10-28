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
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b.
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
Definition FSHZ : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8;
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].

(* [comment removed for export] *)
Definition fsi_fin (off : Z) (h : frame_header) (r : fsi_loop_result) : fsi_result :=
  match r with
  | FL_err v => FSI_err v
  | FL_done ip rem nb =>
      if negb (fh_checksum h =? 0) && (rem <? 4) then FSI_err (ZERR ZE_srcSize_wrong)
      else
        let ip' := if fh_checksum h =? 0 then ip else ip + 4 in
        FSI nb (ip' - off) (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb * fh_bsmax h else fh_fcs h)
  end.
Lemma ffsi_main : forall src off size h,
  ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
  get_frame_header src off size = FH_ok h ->
  find_frame_size_info src off size = fsi_fin off h (fsi_blocks src (off + fh_hsize h) (size - fh_hsize h) 0).
Proof. intros src off size h SK G. unfold find_frame_size_info. rewrite SK, G. reflexivity. Qed.
Lemma ffsi_hdr_err : forall src off size v,
  ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
  get_frame_header src off size = FH_ret v ->
  find_frame_size_info src off size = if zd_is_error v then FSI_err v else FSI_err (ZERR ZE_srcSize_wrong).
Proof. intros src off size v SK G. unfold find_frame_size_info. rewrite SK, G. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fshz_rd : forall (m : amem) FF k, rw_cells bsegs m (shad FF) FSHZ -> 0 <= FF -> 0 <= k < 6 ->
  m (wa (ASHOFF + FF / 8 + 4 + k)) = Some (Z_to_bv 8 0).
Proof.
  intros m FF k H F0 Hk. unfold FSHZ in H. rewrite shad_div in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1] _)) in H. destruct H as [_ H].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  assert (STEP : forall a cs, rw_cells bsegs m a (C1 B00 :: cs) -> 0x625000 <= a -> m (wa a) = Some (Z_to_bv 8 0) /\ rw_cells bsegs m (a + 1) cs).
  { intros a cs Hc Ha. apply (proj1 (rw_cells_app bsegs _ _ [C1 B00] cs)) in Hc. destruct Hc as [Hx Hy].
    split; [exact (fk_byte_of_c1 m _ _ Hx Ha)| exact Hy]. }
  destruct (STEP _ _ H ltac:(unfold ASHOFF; lia)) as [R0 H1]. destruct (STEP _ _ H1 ltac:(unfold ASHOFF; lia)) as [R1 H2].
  destruct (STEP _ _ H2 ltac:(unfold ASHOFF; lia)) as [R2 H3]. destruct (STEP _ _ H3 ltac:(unfold ASHOFF; lia)) as [R3 H4].
  destruct (STEP _ _ H4 ltac:(unfold ASHOFF; lia)) as [R4 H5]. destruct (STEP _ _ H5 ltac:(unfold ASHOFF; lia)) as [R5 _].
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    [ rewrite <- R0 | rewrite <- R1 | rewrite <- R2 | rewrite <- R3 | rewrite <- R4 | rewrite <- R5 ]; f_equal; f_equal; lia.
Qed.
Lemma fshz_unp : forall (m : amem) FF, rw_cells bsegs m (shad FF) FSHZ -> FF mod 8 = 0 -> 0 <= FF -> FF + 256 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 32 + 48).
Proof.
  intros m FF H F8 F0 FH. split; [lia|]. split; [lia|]. intros G HG H1 H2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
  replace (ASHOFF + G) with (ASHOFF + FF / 8 + 4 + (G - FF / 8 - 4)) by lia. apply (fshz_rd m FF (G - FF / 8 - 4) H F0). Z.div_mod_to_equations; lia.
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
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis GETFH : zd_getfh_stmtA AI rng_fs.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis ASH : ashort LB 2.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis RSTKT : rng RNG lo (al_top L - lo).
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis INS : 0 < zlen src -> ainimg LB SRC (zlen src).

  Notation WR := [(FSIP, FSIP + 24)].
  Notation POST := (zd_findfsi_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV FSIP src off size lo m0).
  Notation RES := (find_frame_size_info src off size).

  Notation BINV := (AZ_findfsi_a.BINV AI L RNG st LB m0 SPV FSIP FF).
  Notation EINV := (AZ_findfsi_b.EINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA FSIP SRC src lo FF SHF FLG).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition LINV (m1 : amem) (h : frame_header) : Prop :=
    BINV m1 /\ rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists jA, rw_cells bsegs m1 SPA [CB 48 jA; C8 (Z_to_bv 64 FF)])
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 56) (SPV + -104)
    /\ (exists j, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 8 j])
    /\ rw_cells bsegs m1 (FF + 32) (zfh_cells h)
    /\ (exists j, rw_cells bsegs m1 (FF + 80) [CB 168 j; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m1 SHF FSHZ
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src) /\ unpoisoned m1 FSIP (FSIP + 24)
    /\ (exists j24, rw_cells bsegs m1 FSIP [CB 24 j24]) /\ aro_client RNG m1.

  (* [comment removed for export] *)
  Hypothesis PFIN : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84414 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Hypothesis PLOOP : forall m1 h (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word),
    LINV m1 h -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
    get_frame_header src off size = FH_ok h ->
    evtF bsegs RNG POST (STpc 0x8450c m1 x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size)
                              (Z_to_bv 64 (FF + 32)) x23 x24 x28 x29 x30 x31).

  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Ltac fsip_up UP MUL :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (UPc : unpoisoned mm FSIP (FSIP + 24))
        by (eapply unpoisoned_munch; [exact UP | exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
              gf_unhold; clear - G_fsip; Z.div_mod_to_equations; lia])
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma p_gen : forall m1 (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 : word),
    EINV m1 -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
    evtF bsegs RNG POST (STpc 0x84374 m1 x1 x5 x6 x7 x10 x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size)
                              x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 EI SK.
    pose proof EI as (BI & SAV & [jA FRA] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & [j24 FC] & ARO).
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_fsip as (P1 & P2). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8').
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5). pose proof R_fsip as (RP1 & RP2). pose proof G_src as (S1 & S2 & S3). pose proof R_src as (RS1 & RS2). pose proof R_ff as (RF1 & RF2 & RF3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof P1 as PL. pose proof (fk_ablk_lits _ _ F1) as FL. pose proof (fk_ablk_lits _ _ S1) as SL. pose proof (fk_ablk_lits _ _ L1) as LL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (clear - FL GS ATR; lia).
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 32 <= FLG) by (clear - LL GS ATR; lia).
    assert (PSH : FSIP + 24 <= SHF \/ SHF + 32 <= FSIP) by (clear - PL GS ATR; lia).
    assert (SSH : SRC + zlen src <= SHF \/ SHF + 32 <= SRC) by (clear - SL GS ATR; lia).
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (NZ : 0 < zlen src) by (clear - OFS N5 OFF0; lia).
    destruct (FHL _ _ _ _ _ AH1) as [FAB FABD]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & LY5).
    unfold FSH0 in XS.
    pose proof (munch_refl [(SHF, SHF + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold G_lo. fk_hold G_fsip. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_fsip. fk_hold R_ff. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold EI. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold SAV. fk_hold FRA. fk_hold STL. fk_hold STG. fk_hold XH. fk_hold XL. fk_hold SB1. fk_hold US. fk_hold UP. fk_hold FC. fk_hold ARO.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold PL. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold P2. fk_hold S2. fk_hold S3. fk_hold F7. fk_hold F8'. fk_hold L5.
    fk_hold FFSH. fk_hold FLSH. fk_hold PSH. fk_hold SSH.
    zstep.
    do 6 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    change (rw_cells bsegs m2 SHF FSHZ) in XS.
    gf_unhold.
    assert (AH2 : AHEAP AI L RNG st (FB2 FF :: LB) m2).
    { eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 32 - shad FF) with 32 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (SAV2 : rw_cells bsegs m2 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | unfold FSAVED; cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (FRA2 : rw_cells bsegs m2 SPA [CB 48 jA; C8 (Z_to_bv 64 FF)])
      by (eapply rw_cells_transport; [exact FRA | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (STG2 : stk bsegs m2 (SPA + 56) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG | exact MUL | exact WML | cbn; clear - GS G2 G3 KLO; unfold KHIGH in KLO; lia]).
    assert (XH2 : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 224 jH; C8 (Z_to_bv 64 FLG)])
      by (eapply rw_cells_transport; [exact XH | exact MUL | exact WML | cbn; clear - FFSH; lia]).
    assert (XL2 : rw_cells bsegs m2 FLG [C1 (Z_to_bv 8 1)]) by (eapply rw_cells_transport; [exact XL | exact MUL | exact WML | cbn; clear - FLSH; lia]).
    assert (FC2 : rw_cells bsegs m2 FSIP [CB 24 j24]) by (eapply rw_cells_transport; [exact FC | exact MUL | exact WML | cbn; clear - PSH; lia]).
    assert (SB2 : bytes_at bsegs m2 SRC (map (Z_to_bv 8) src)) by (eapply bytes_at_transport; [exact SB1 | exact MUL | rewrite length_map; cbn; clear - SSH; lia]).
    assert (US2 : unpoisoned m2 SRC (SRC + zlen src)).
    { eapply unpoisoned_munch; [exact US | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF.
      unfold ASHOFF. clear - F8' F2 SL NZ. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (UP2 : unpoisoned m2 FSIP (FSIP + 24)).
    { eapply unpoisoned_munch; [exact UP | exact MUL |]. cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF.
      unfold ASHOFF. clear - F7 F2 PL. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (ARO2 : aro_client RNG m2).
    { eapply aro_client_transport_gen; [exact WML | exact ARO | exact MUL |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - B1 B2 B3 FL. split; [| exact I]. Z.div_mod_to_equations. lia. }
    clear SAV FRA STL STG XL FC SB1 US UP ARO. rename MUL into MU12. rename WML into WM12.
    assert (LBH' : ablkLB (FB2 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB2 FF :: LB) 1) by (apply ashort_push; [exact ASH| clear; lia]).
    assert (ART2 : art m2).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH2) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP : afpre AI rng_fs L RNG st (FB2 FF :: LB) m2 lo SPA 1).
    { unfold afpre, astk. split; [exact AH2|]. split; [exact ASH'|]. split; [exact ART2|].
      split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4)] 224 jH [C8 (Z_to_bv 64 FLG)] [8; 48; 168]%nat) in XH2; [| reflexivity].
    cbn [mk_CB_cells app] in XH2.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 8 (firstn 8 jH)] _) XH2) as [XHA XHB].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XHB.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 48 (firstn 48 (skipn 8 jH))] _) XHB) as [XZ XHC].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XZ, XHC.
    match type of XZ with rw_cells _ _ ?a _ => replace a with (FF + 32) in XZ by (clear; lia) end.
    match type of XHC with rw_cells _ _ ?a _ => replace a with (FF + 80) in XHC by (clear; lia) end.
    clear XH2 XHB.
    assert (UZ2 : unpoisoned m2 (FF + 32) (FF + 32 + 48)).
    { apply (fshz_unp m2 FF); [rewrite <- F4; exact XS | clear - F2; Z.div_mod_to_equations; lia | clear - FL; lia | clear - FL ATR; lia]. }
    assert (SRCAP : ainblk (FB2 FF :: LB) SRC (zlen src)).
    { destruct (INS NZ) as [(b & Hb & Hb1 & Hb2)|[IM1 IM2]]; [| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      exists b. split; [right; exact Hb| split; [exact Hb1| exact Hb2]]. }
    zstep. zstep. zstep.
    zstep. unfold zd_getfh_stmtA, APZD_GETFH in GETFH.
    eapply evtF_cut.
    { eapply (GETFH L RNG st (FB2 FF :: LB)) with (lo := lo) (ZFH := FF + 32) (SRC := SRC) (src := src) (off := off) (size := size);
      first [ exact SB2 | exact OK | exact OFF0 | exact N5 | exact OFS | exact XZ | exact STL2 | exact G2 | exact AFP | exact ARO2 | exact MI | exact TP | reflexivity
            | clear - SL; lia
            | clear - F3 G1; lia
            | clear - S2 G3; lia
            | clear - F8'; lia
            | intros _; split; [exact S1| split; [exact US2| split; [exact RS1| exact RS2]]]
            | intros _; left; exact SRCAP
            | clear - F2; Z.div_mod_to_equations; lia
            | intros _; split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia] | split; [exact UZ2| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
            | exists FF, (FF + 256); split; [clear; lia|]; split; [clear; lia|]; split; [clear - F2; Z.div_mod_to_equations; lia|]; split; [clear - F2; Z.div_mod_to_equations; lia|];
              split; [clear - FL; lia|]; split; [unfold KEND; clear - FL ATR; lia|];
              rewrite <- F4; replace (shad (FF + 256) - SHF) with 32 by (rewrite F4, !shad_div; clear - F2; Z.div_mod_to_equations; lia);
              split; [exact (proj2 XS) | exact RF2]
            | exists (FB2 FF); split; [left; reflexivity| cbn; clear; lia]
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & cs & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & ZC5 & ZSZ5 & ZOK5).
    rd_retlit.
    (* [comment removed for export] *)
    set (W5 := [(FF + 32, FF + 32 + 48); (SPA - 4320, SPA)]) in MU5.
    assert (AW5 : aappW W5).
    { subst W5. unfold aappW. pose proof (ablk_disj_band _ _ F1) as DBF. unfold KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - DBF; lia|]. apply Forall_cons; [cbn [fst snd]; clear - KLO G2; lia|]. apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k H1 Hk. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - H1 Hk FABL F3 G1 G2 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV2 MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA2 MU5 WM5 ltac:(apply DSTK; clear; lia)) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG2 MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as STG5.
    (* [comment removed for export] *)
    assert (PFF : forall a, FF <= a < FF + 256 -> ~ (FF + 32 <= a < FF + 80) ->
              (in_fake (FB2 FF :: LB) a /\ outside [(FF + 32, FF + 32 + 48)] a) \/ (exists a', in_fake (FB2 FF :: LB) a' /\ a = shad a')).
    { intros a Ha N1. left. split; [exists 2, FF, 256; split; [left; reflexivity| exact Ha]|]. cbn [outside]. clear - Ha N1. split; [lia| exact I]. }
    assert (PSF : forall a, SHF <= a < SHF + 32 -> (in_fake (FB2 FF :: LB) a /\ outside [(FF + 32, FF + 32 + 48)] a) \/ (exists a', in_fake (FB2 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 2, FF, 256; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XHA ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XHA5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XHC ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; clear - Ha; lia)) as XHC5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 XS ltac:(unfold FSHZ; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    (* [comment removed for export] *)
    assert (XL5 : rw_cells bsegs m5 FLG [C1 (Z_to_bv 8 1)]).
    { rewrite L0. destruct (FFLAG _ _ _ _ _ 2 FF 256 AH5 ltac:(left; reflexivity)) as (X & _). exact X. }
    (* [comment removed for export] *)
    assert (FFR5' : ffr_pres W5 (FB2 FF :: LB) m2 m5).
    { eapply magree_mono; [exact FFR5|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      subst W5; cbn [outside app] in HO |- *. destruct HO as (O1 & _). exact (conj O1 I). }
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB2 FF :: LB) X k)
      by (intros X k (b & Hb & H1 & H2); exists b; split; [right; exact Hb| split; [exact H1| exact H2]]).
    assert (DFP : disjoint_from W5 FSIP 24) by (subst W5; cbn [disjoint_from]; clear - F7 P2 G2 G3; repeat split; lia).
    assert (DFSR : disjoint_from W5 SRC (zlen src)) by (subst W5; cbn [disjoint_from]; clear - F8' S2 G2 G3; repeat split; lia).
    (* [comment removed for export] *)
    pose proof (rw_cells_transport _ _ _ _ _ _ FC2 MU5 WM5 ltac:(apply DSTK; cbn; clear - P2 G3; lia)) as FC5.
    assert (UP5 : unpoisoned m5 FSIP (FSIP + 24)).
    { eapply unpoisoned_munch; [exact UP2 | exact MU5 |]. subst W5. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
      clear - PL P2 FABL FL G1 G2 G3 ATR KLO. unfold KHIGH in KLO. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ _ SRC (map (Z_to_bv 8) src) AH2 ltac:(rewrite length_map; exact SRCAP) ltac:(rewrite length_map; exact DFSR) MU5 FFR5' SB2) as SB5.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH2 SRCAP NZ ltac:(unfold KEND; clear - SL ATR; lia) AW5 MU5 FFR5' US2) as US5.
    assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO2| exact MU5| exact WM5| exact AW5| exact FAB]).
    (* [comment removed for export] *)
    assert (FFR05 : ffr_pres WR LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR1|]. eapply ffr_pres_trans.
      - apply ffr_pres_mono_nil1.
        eapply (fk_ffr_fin AI L RNG st LB m1 m1 m2 2 FF 256 SHF 32 [] [(FSIP, FSIP + 24)]);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] | constructor]
          | constructor
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MU12]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WM12 ].
      - eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
        + left. split; [exists c, A, k; split; [right; exact Hb| exact Ha]|].
          pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH1 _ Hb) as D1. cbn [ab_addr ab_size] in D1.
          cbn [outside]. clear - D1 Ha. split; [lia| exact I].
        + right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU05 : munch ([(FSIP, FSIP + 24); (SPV - 4672, SPV)] ++ fake_area L) m0 m5).
    { eapply munch_trans; [exact MU1|]. eapply munch_trans.
      - eapply munch_weaken; [| exact MU12]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
        destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 FA8 F2. Z.div_mod_to_equations. lia.
      - eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. unfold FAKESZ in *.
        clear - Hx F5 F6 G3. lia. }
    assert (WM05 : wmono bsegs m0 m5) by (exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM5))).
    assert (BI5 : BINV m5) by (split; [exact AH5| split; [exact FFR05| split; [exact MU05| split; [exact WM05| exact MI5]]]]).
    set (gfh := get_frame_header src off size) in *.
    assert (RRET : 0 <= fh_retval gfh < 18446744073709551616).
    { destruct gfh as [hh|v] eqn:G; cbn [fh_retval]; [clear; lia|]. pose proof (gfh_ret_pos src off size v N5 G) as RP. clear - RP; lia. }
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FC5; [| reflexivity]. cbn [mk_CB_cells app] in FC5.
    pose proof (munch_refl [(FSIP, FSIP + 24)] m5) as MUL. pose proof (wmono_refl bsegs m5) as WML.
    clear MU5 WM5 FFR5 FFR5' PFF PSF DSTK AW5 INCONS DFP DFSR SAV2 FRA2 STL2 STG2 XHA XZ XHC XS XL2 FC2 SB2 US2 UP2 ARO2 UZ2 AFP ART2 AH2 MU12 WM12 MI AH1 FFR1 MU1 WM1 XH EI.
    fk_hold G_lo. fk_hold G_fsip. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_fsip. fk_hold R_ff. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold L4. fk_hold FABD. fk_hold LY5. fk_hold L3. fk_hold SL. fk_hold LL. fk_hold FABL. fk_hold FLA. fk_hold P2. fk_hold S2. fk_hold S3. fk_hold F7. fk_hold F8'. fk_hold L5.
    fk_hold FFSH. fk_hold FLSH. fk_hold SSH. fk_hold ZOK5. fk_hold SRCAP. fk_hold LBH'. fk_hold ASH'.
    fk_hold SAV5. fk_hold FRA5. fk_hold STG5. fk_hold ST5. fk_hold XHA5. fk_hold XHC5. fk_hold XS5. fk_hold XL5. fk_hold ZC5. fk_hold SB5. fk_hold US5. fk_hold ARO5.
    fk_hold AH5. fk_hold FFR05. fk_hold MU05. fk_hold WM05. fk_hold BI5.
    zstep. replace (Z_to_bv 64 (-119)) with (Z_to_bv 64 18446744073709551497) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      assert (ER : exists v, gfh = FH_ret v /\ RES = FSI_err v /\ fh_retval gfh = v).
      { destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in KE |- *; [exfalso; clear - KE; lia|].
        exists v. split; [reflexivity|]. split; [| reflexivity]. subst gfh. rewrite (ffsi_hdr_err src off size v SK G).
        replace (zd_is_error v) with true by (symmetry; apply zd_is_error_true_iff; clear - KE; lia). reflexivity. }
      destruct ER as (v & EG & ER & EV). rewrite EV in *. clear EG.
      zstep. fsip_up UP5 MUL. fsip_sh UPc RP2 8. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
      zstep.                                                   (* [comment removed for export] *)
      zstep. fsip_up UP5 MUL. fsip_sh UPc RP2 16. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
      zstep. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
      zstep.                                                   (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      gf_unhold.
      destruct (rw_cells_forget _ _ _ _ FRA5) as [jfr FRA']. cbn [cells_size csize Nat.add] in FRA'.
      destruct (rw_cells_forget _ _ _ _ XS5) as [shb XS']. unfold FSHZ in XS'. cbn [cells_size csize Nat.add length] in XS'.
      pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XHA5)) as XM.
      pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 168 (firstn 168 (skipn 48 (skipn 8 jH)))] _) XHC5)) as XP.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
      match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 248) in XP by (clear; lia) end.
      eapply (PFIN m6 jfr _ shb _);
        [
        | eapply rw_cells_transport; [exact SAV5 | exact MUL | exact WML | unfold FSAVED; cbn; clear - P2 G2 G3; lia]
        | eapply rw_cells_transport; [exact FRA' | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
        | eapply stk_transport_disjoint; [exact ST5 | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
        | eapply stk_transport_disjoint; [exact STG5 | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
        | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - F7; lia]
        | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - F7; lia]
        | eapply rw_cells_transport; [exact XL5 | exact MUL | exact WML | cbn; clear - L5; lia]
        | eapply rw_cells_transport; [exact XS' | exact MUL | exact WML | cbn; clear - PSH; lia]
        | rewrite ER; cbn [fsi_csize fsi_bound]; exact FC5 ].
      split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM05 WML) | assumption]]]].
      + eapply (AI_frame AI); [exact AH5 | exact MUL | exact WML |].
        constructor; [cbn [fst snd]; left; left; clear - P1 P2 G1 G2 G3; lia | constructor].
      + eapply ffr_pres_trans; [exact FFR05|]. apply ffr_pres_mono_nil1.
        eapply (fk_ffr_fin AI L RNG st LB m5 m5 m6 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24)]);
          [ exact AH5 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] | constructor]
          | constructor
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WML ].
      + eapply munch_trans; [exact MU05|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        destruct (gfh_ok_of_ret0 src off size N5 ltac:(fold gfh; clear - K0 RRET; lia)) as [h G]. fold gfh in G.
        gf_unhold. rewrite (ZOK5 h G) in ZC5. replace (fh_retval gfh) with 0 by (clear - K0; lia).
        match type of XHC5 with rw_cells _ _ ?a _ => replace a with (FF + 80) in XHC5 by (clear; lia) end.
        apply (rw_cells_merge bsegs _ FSIP [] [CB 8 (firstn 8 j24); CB 8 (firstn 8 (skipn 8 j24)); CB 8 (firstn 8 (skipn 8 (skipn 8 j24)))] []) in FC5.
        cbn [app cells_size csize Nat.add] in FC5.
        eapply (PLOOP m5 h); [| exact SK | exact G].
        split; [exact BI5|]. split; [exact SAV5|]. split; [eexists; exact FRA5|]. split; [exact ST5|]. split; [exact STG5|].
        split; [eexists; exact XHA5|]. split; [exact ZC5|]. split; [eexists; exact XHC5|]. split; [exact XL5|]. split; [exact XS5|].
        split; [exact SB5|]. split; [exact US5|]. split; [exact UP5|]. split; [eexists; exact FC5| exact ARO5].
      + (* [comment removed for export] *)
        assert (ER : RES = FSI_err (ZERR ZE_srcSize_wrong)).
        { destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in K0, KE |- *; [exfalso; clear - K0; lia|].
          subst gfh. rewrite (ffsi_hdr_err src off size v SK G).
          replace (zd_is_error v) with false by (symmetry; apply zd_is_error_false_iff; clear - KE; lia). reflexivity. }
        zstep. fsip_up UP5 MUL. fsip_sh UPc RP2 8. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_false.
        zstep. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        zstep.                                                   (* [comment removed for export] *)
        zstep. fsip_up UP5 MUL. fsip_sh UPc RP2 16. zstep. zstep. zstep. clear RDz RTz UPc. zstep. if_true.
        zstep. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
        zstep.                                                   (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        gf_unhold.
        destruct (rw_cells_forget _ _ _ _ FRA5) as [jfr FRA']. cbn [cells_size csize Nat.add] in FRA'.
        destruct (rw_cells_forget _ _ _ _ XS5) as [shb XS']. unfold FSHZ in XS'. cbn [cells_size csize Nat.add length] in XS'.
        pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XHA5)) as XM.
        pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 168 (firstn 168 (skipn 48 (skipn 8 jH)))] _) XHC5)) as XP.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
        match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 248) in XP by (clear; lia) end.
        eapply (PFIN m6 jfr _ shb _);
          [
          | eapply rw_cells_transport; [exact SAV5 | exact MUL | exact WML | unfold FSAVED; cbn; clear - P2 G2 G3; lia]
          | eapply rw_cells_transport; [exact FRA' | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
          | eapply stk_transport_disjoint; [exact ST5 | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
          | eapply stk_transport_disjoint; [exact STG5 | exact MUL | exact WML | cbn; clear - P2 G2 G3; lia]
          | eapply rw_cells_transport; [exact XM | exact MUL | exact WML | cbn; clear - F7; lia]
          | eapply rw_cells_transport; [exact XP | exact MUL | exact WML | cbn; clear - F7; lia]
          | eapply rw_cells_transport; [exact XL5 | exact MUL | exact WML | cbn; clear - L5; lia]
          | eapply rw_cells_transport; [exact XS' | exact MUL | exact WML | cbn; clear - PSH; lia]
          | rewrite ER; cbn [fsi_csize fsi_bound]; exact FC5 ].
        split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM05 WML) | assumption]]]].
        * eapply (AI_frame AI); [exact AH5 | exact MUL | exact WML |].
          constructor; [cbn [fst snd]; left; left; clear - P1 P2 G1 G2 G3; lia | constructor].
        * eapply ffr_pres_trans; [exact FFR05|]. apply ffr_pres_mono_nil1.
          eapply (fk_ffr_fin AI L RNG st LB m5 m5 m6 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24)]);
            [ exact AH5 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
            | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] | constructor]
            | constructor
            | apply ffr_pres_refl
            | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
            | exact WML ].
        * eapply munch_trans; [exact MU05|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia.
  Qed.
End FS.
End CANSEC1.
