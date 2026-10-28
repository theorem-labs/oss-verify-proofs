(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_block_iface AZ_blk_iface5 AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d AZ_dmf_e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).
Notation B04 := (Z_to_bv 8 4).
Notation MAGIC_RETIRED := 1172321806.

Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Lemma dsho_unp : forall (m : amem) FF, rw_cells bsegs m (shad FF) DSHO -> FF mod 8 = 0 -> 6443008 <= FF -> FF + 256 <= 2^47 ->
  unpoisoned m (FF + 128) (FF + 140).
Proof.
  intros m FF H F8 F0 FH. unfold DSHO in H. rewrite shad_div in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF2] _)) in H.
  destruct H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 B00] _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 B04] _)) in H. destruct H as [H1 _].
  pose proof (fk_byte_of_c1 m _ _ H0 ltac:(unfold ASHOFF; lia)) as R0. pose proof (fk_byte_of_c1 m _ _ H1 ltac:(unfold ASHOFF; lia)) as R1.
  split; [lia|]. split; [lia|]. intros G HG Ha Hb.
  assert (E : G = FF / 8 + 16 \/ G = FF / 8 + 17) by (Z.div_mod_to_equations; lia).
  destruct E as [-> | ->].
  - exists B00. split; [rewrite <- R0; f_equal; f_equal; lia| left; reflexivity].
  - exists B04. split; [rewrite <- R1; f_equal; f_equal; lia| right]. replace (sval B04) with 4 by reflexivity. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.
Lemma dm_fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply dm_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma dm_fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply dm_fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.
Lemma dm_fcall_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply dm_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma dm_fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
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
    + eapply dm_disjoint_from_sub; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
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

Section DM.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo DCTX DST CAP SRC : Z) (src : list Z) (size FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 1099511627776.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 1099511627776.
  Hypothesis DNULL : DST = 0 -> CAP = 0.  Hypothesis DNN : DST <> 0 -> 4096 <= DST.  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis S_DC : DCTX + 95992 <= lo \/ SPV <= DCTX.
  Hypothesis S_DS : DST + CAP <= lo \/ SPV <= DST.
  Hypothesis S_SR : SRC + zlen src <= lo \/ SPV <= SRC.
  Hypothesis S_GT : 0xc7fd0 + 16 <= lo \/ SPV <= 0xc7fd0.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0xc7fd0 + 16 <= DCTX \/ DCTX + 95992 <= 0xc7fd0.
  Hypothesis GT_DS : 0xc7fd0 + 16 <= DST \/ DST + CAP <= 0xc7fd0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 7184 /\ SPV - 543 <= SPA <= SPV - 512 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                    /\ (DCTX + 95992 <= FF \/ FF + 256 <= DCTX) /\ (DST + CAP <= FF \/ FF + 256 <= DST) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC).
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG).
  (* [comment removed for export] *)
  Hypothesis B_dc : ablk DCTX (DCTX + 95992) /\ ainblk LB DCTX 95992.
  Hypothesis B_sr : ablk SRC (SRC + zlen src) /\ (0 < zlen src -> ainimg LB SRC (zlen src)).
  Hypothesis B_ds : 0 < CAP -> ablk DST (DST + CAP) /\ ainblk LB DST CAP.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_dc : rng RNG DCTX 95992 /\ rng RNG (shad DCTX) (shspan DCTX 95992).
  Hypothesis R_ds : 0 < CAP -> rng RNG DST CAP /\ rng RNG (shad DST) (shspan DST CAP).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.


  Notation WR := [(DCTX, DCTX + 95992); (DST, DST + CAP)].
  Notation POST := (zd_dmf_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP src size lo m0).
  Definition BINV (m1 : amem) : Prop :=
    AHEAP AI L RNG st (FB2 FF :: LB) m1 /\ ffr_pres WR LB m0 m1
    /\ munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.
  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 SHF) x22 (Z_to_bv 64 SHB) x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition DFR (v8 v16 v24 v32 vfl vdst : word) (j0 j384 : list byte) : list cell :=
    [CB 8 j0; C8 v8; C8 v16; C8 v24; C8 v32;
     C8 (Z_to_bv 64 10600); C8 (Z_to_bv 64 (FF + 40)); C8 (Z_to_bv 64 (DCTX + 30192)); C8 (Z_to_bv 64 (FF + 32));
     C8 (Z_to_bv 64 (DCTX + 30108)); C8 (Z_to_bv 64 (DCTX + 29960)); C8 (Z_to_bv 64 (DCTX + 29928)); C8 (Z_to_bv 64 (DCTX + 30232));
     C8 (Z_to_bv 64 (DCTX + 29944)); C8 (Z_to_bv 64 (DCTX + 30008)); C8 (Z_to_bv 64 (DCTX + 30112)); C8 (Z_to_bv 64 (FF + 128));
     C8 (Z_to_bv 64 (DCTX + 29912)); C8 (Z_to_bv 64 (DCTX + 4136)); C8 (Z_to_bv 64 (DCTX + 6192)); C8 (Z_to_bv 64 (DCTX + 26684));
     C8 (Z_to_bv 64 (DCTX + 29888)); C8 (Z_to_bv 64 (DCTX + 29976)); C8 (Z_to_bv 64 201326604); C8 (Z_to_bv 64 (DCTX + 10296));
     C8 (Z_to_bv 64 (DCTX + 24)); C8 (Z_to_bv 64 (DCTX + 16)); C8 (Z_to_bv 64 (DCTX + 8)); C8 (Z_to_bv 64 (DCTX + 30176));
     C8 (Z_to_bv 64 (DCTX + 29992)); C8 (Z_to_bv 64 (DCTX + 30200)); C8 (Z_to_bv 64 (DCTX + 32)); C8 (Z_to_bv 64 (DCTX + 30000));
     C8 (Z_to_bv 64 (DCTX + 30004)); C8 (Z_to_bv 64 (DCTX + 29996)); C8 (Z_to_bv 64 (DCTX + 29920)); C8 (Z_to_bv 64 (DCTX + 30204));
     C8 (Z_to_bv 64 (DCTX + 95984)); C8 (Z_to_bv 64 25481893); C8 (Z_to_bv 64 DST); C8 vfl; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 (DCTX + 30104)); C8 (Z_to_bv 64 (SHB + (DCTX + 30104) / 8)); C8 vdst; C8 (Z_to_bv 64 0);
     CB 16 j384; C8 (Z_to_bv 64 FF)].


  (* [comment removed for export] *)
  Definition DINV (m1 : amem) (tot : Z) : Prop :=
    BINV m1 /\ rw_cells bsegs m1 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists v8 v16 v24 v32 vfl j0 j384, rw_cells bsegs m1 SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384))
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 408) (SPV + -104)
    /\ (exists ja, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20853); C8 (Z_to_bv 64 0x84750); CB 104 ja])
    /\ (exists jb, rw_cells bsegs m1 (FF + 128) [CB 12 jb])
    /\ (exists jc, rw_cells bsegs m1 (FF + 140) [CB 108 jc; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m1 SHF DSHC
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src) /\ unpoisoned m1 DCTX (DCTX + 95992)
    /\ (0 < CAP -> unpoisoned m1 DST (DST + CAP)) /\ stk bsegs m1 DST (DST + CAP)
    /\ rw_cells bsegs m1 0xc7fd0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ aro_client RNG m1 /\ dctx_any m1 DCTX
    /\ azstk RNG m1 lo SPV.

  (* [comment removed for export] *)
  Definition AINV (m1 : amem) (off sz tot : Z) : Prop :=
    DINV m1 tot /\ 0 <= off /\ off + sz <= size /\ 0 <= sz /\ 0 <= tot <= CAP
    /\ (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r).
  Notation LHst mm off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 :=
    (STpc 0x84a88 mm x1 (Z_to_bv 64 8) (Z_to_bv 64 (-120)) x7 x10 (Z_to_bv 64 5) x12 x13 x14 (Z_to_bv 64 25481893) (Z_to_bv 64 1) (Z_to_bv 64 4)
          (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31).

  (* [comment removed for export] *)
  Ltac dm_hold_sep := fk_hold S_DC; fk_hold S_DS; fk_hold S_SR; fk_hold S_GT; fk_hold D_DC; fk_hold D_SR; fk_hold SR_DC; fk_hold GT_DC; fk_hold GT_DS;
    fk_hold DNULL; fk_hold DNN; fk_hold B_ds; fk_hold R_ds; fk_hold B_sr; fk_hold B_dc; fk_hold G_ff; fk_hold G_flg.
  (* [comment removed for export] *)
  Hypothesis PRES0 : forall m1 off sz tot res (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x20 = Z_to_bv 64 sz' /\ x26 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (STpc 0x84ee4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 res) x20 (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis ASH : ashort LB 7.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis RSTKT : rng RNG lo (al_top L - lo).
  Hypothesis AH_dc : ahull RNG m0 DCTX 95992.
  Hypothesis AH_sr : 0 < zlen src -> ahull RNG m0 SRC (zlen src).
  Hypothesis AH_ds : 0 < CAP -> ahull RNG m0 DST CAP.
  Variable TBL : tbl_pred.
  Hypothesis TBLL : tbl_laws TBL.
  Hypothesis GETCB : zd_getcblock_stmtA.

  (* [comment removed for export] *)
  Definition SINV (m1 : amem) : Prop :=
    rw_cells bsegs m1 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ stk bsegs m1 (SPA + 408) (SPV + -104)
    /\ (exists ja, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20853); C8 (Z_to_bv 64 0x84750); CB 104 ja])
    /\ (exists jc, rw_cells bsegs m1 (FF + 140) [CB 108 jc; C8 (Z_to_bv 64 FLG)])
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src) /\ unpoisoned m1 DCTX (DCTX + 95992)
    /\ (0 < CAP -> unpoisoned m1 DST (DST + CAP))
    /\ rw_cells bsegs m1 0xc7fd0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ aro_client RNG m1 /\ azstk RNG m1 lo SPV.

  (* [comment removed for export] *)
  Definition wapart (W : list (Z * Z)) : Prop := forall X k, 0 <= k ->
    (X + k <= lo \/ SPA <= X) -> (X + k <= SPA \/ SPA + 408 <= X) -> (X + k <= DCTX \/ DCTX + 95992 <= X) ->
    (0 < CAP -> X + k <= DST \/ DST + CAP <= X) -> (X + k <= FF + 128 \/ FF + 140 <= X) -> disjoint_from W X k.

  (* [comment removed for export] *)
  Definition BDC (m1 : amem) (h : frame_header) (PFX : Z) (llt mlt oft huf pde expd pcs dsz bt stg le fe : word)
      (xs : list cell) (ws : list word) : Prop :=
    dctx_ptrs bsegs m1 DCTX llt mlt oft huf /\
    dctx_h1 bsegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd /\
    rw_cells bsegs m1 (DCTX + 29928) (zfh_cells h) /\
    dctx_h3 bsegs m1 DCTX pcs dsz bt stg le fe /\
    dctx_xs bsegs m1 DCTX xs /\ (fh_checksum h <> 0 -> exists j1 msz j2, xs = xxh_cells j1 msz j2 /\ 0 <= msz < 32) /\
    dctx_h5 bsegs m1 DCTX ws /\ h5_frame_ok ws /\
    wnth ws H5_validateChecksum = Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1) /\
    wnth ws H5_isFrameDecompression = Z_to_bv 64 1 /\
    (exists jhb ovd dcb dce trace, dctx_tx bsegs m1 DCTX jhb ovd dcb dce trace) /\
    dctx_owned bsegs m1 DCTX /\
    TBL m1 DCTX llt mlt oft huf le fe.

  (* [comment removed for export] *)
  Definition FRAME_OK (off sz tot hsz : Z) (h : frame_header) : Prop :=
    0 <= off /\ off + sz <= size /\ 0 <= tot <= CAP /\
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) /\
    9 <= sz /\ hsz = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\ hsz + 3 <= sz /\
    is_skippable_magic (le32 src off) = false /\ get_frame_header src off hsz = FH_ok h.

  (* [comment removed for export] *)
  Definition KA_T (sz : Z) : Prop :=
    forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31).

  (* [comment removed for export] *)
  Notation BFR mm tot v32 vfl j0 j384 :=
    (rw_cells bsegs mm SPA (DFR (Z_to_bv 64 FF) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384)).

  (* [comment removed for export] *)
  Notation BLKst mm off sz tot ipb rem o cbs x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 :=
    (STpc 0x8500c mm x1 x5 x6 x7 x10 (Z_to_bv 64 rem) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + tot + o)) x19 (Z_to_bv 64 sz)
          (Z_to_bv 64 (SRC + ipb)) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Definition B_HEAD (off sz tot hsz : Z) (h : frame_header) (PFX ipb rem o : Z) : Prop :=
    forall m1 cbs bp (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) vfl j0 j384
           (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
      BINV m1 -> SINV m1 -> stk bsegs m1 lo SPA -> BFR m1 tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384 ->
      rw_cells bsegs m1 (FF + 128) (bp_cells bp) -> rw_cells bsegs m1 SHF DSHO -> stk bsegs m1 DST (DST + CAP) ->
      BDC m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
      get_cblock_size src ipb rem = Some (cbs, bp) -> zd_is_error cbs = false ->
      evtF bsegs RNG POST (BLKst m1 off sz tot ipb rem o cbs x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31).
  Hypothesis PBLK : forall (n : nat) off sz tot hsz h PFX ipb rem o,
    rem <= Z.of_nat n ->
    FRAME_OK off sz tot hsz h ->
    ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    off + hsz <= ipb -> ipb + rem <= off + sz -> 0 <= o <= CAP - tot ->
    (forall ip' rem' o', dblocks src (CAP - tot) ipb rem o ip' rem' o' -> dblocks src (CAP - tot) (off + hsz) (sz - hsz) 0 ip' rem' o') ->
    KA_T sz ->
    B_HEAD off sz tot hsz h PFX ipb rem o.

  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition GEOM : Prop :=
    (ATOP + 4096 <= lo /\ lo <= SPV - 7184 /\ SPV - 543 <= SPA /\ SPA <= SPV - 512 /\ SPV + 16 < 2^47)
    /\ (6443008 <= FF /\ FF + 256 <= ATOP /\ FF mod 8 = 0 /\ SHF = SHB + FF / 8 /\ SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
    /\ (6443008 <= DCTX /\ DCTX + 95992 <= ATOP)
    /\ (0 < CAP -> 6443008 <= DST /\ DST + CAP <= ATOP)
    /\ (6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47)
    /\ (6443008 <= al_fake L /\ al_fake L + FAKESZ <= ATOP /\ al_fake L mod 8 = 0 /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ)
    /\ (0 <= DST /\ DST + CAP < 2^47)
    /\ (17594333495296 <= ATOP /\ ATOP <= 2^47 - 4096)
    /\ (6443008 <= FLG /\ FLG + 1 <= ATOP /\ (FLG + 1 <= FF \/ FF + 256 <= FLG) /\ (FLG + 1 <= DCTX \/ DCTX + 95992 <= FLG)
        /\ (0 < CAP -> FLG + 1 <= DST \/ DST + CAP <= FLG)).
  Lemma dm_geom : forall m, AHEAP AI L RNG st (FB2 FF :: LB) m -> GEOM.
  Proof.
    intros m AH.
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9'). pose proof B_dc as [ABD IBD]. pose proof B_sr as [ABS _].
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct (FHL _ _ _ _ _ AH) as [FAB _].
    split; [clear - G1 G2 G3 G5; lia|].
    split. { pose proof (fk_ablk_lits _ _ F1) as FL. rewrite F4, shad_div. unfold ASHOFF. clear - FL F2 F3 ATR. Z.div_mod_to_equations. lia. }
    split; [pose proof (fk_ablk_lits _ _ ABD) as X; clear - X ATR; lia|].
    split; [intros HC; pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X ATR; lia|].
    split; [pose proof (fk_ablk_lits _ _ ABS) as X; clear - X ATR RS1; lia|].
    split. { pose proof (fk_ablk_lits _ _ FAB) as X. clear - X ATR F5 F6. unfold al_fake in *. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia| lia]. }
    split; [split; [destruct (Z.eq_dec DST 0) as [Hd|Hd]; [clear - Hd; lia| pose proof (DNN Hd) as X; clear - X; lia] | clear - RDST; lia]|].
    split; [clear - ATR; lia|].
    pose proof (fk_ablk_lits _ _ L1) as LL. pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    split; [clear - LL; lia|]. split; [exact L2|]. split; [exact FLA|].
    split; [destruct IBD as (bb & Hb & Hb1 & Hb2); pose proof (L4 bb ltac:(right; exact Hb)) as X; clear - X Hb1 Hb2; lia|].
    intros HC. destruct (proj2 (B_ds HC)) as (bb & Hb & Hb1 & Hb2). pose proof (L4 bb ltac:(right; exact Hb)) as X. clear - X Hb1 Hb2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_of : forall m tot v8 v16 v24 v32 vfl j0 j384 cs,
    BINV m -> SINV m -> stk bsegs m lo SPA ->
    rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384) ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    dctx_any m DCTX -> DINV m tot.
  Proof.
    intros m tot v8 v16 v24 v32 vfl j0 j384 cs BI (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS) STL FRA XB XBS XS DSK DA.
    pose proof BI as (AH & _). pose proof G_flg as (L0 & _).
    destruct (rw_cells_forget _ _ _ _ XB) as [jb XB']. rewrite XBS in XB'.
    split; [exact BI|]. split; [exact SAV|]. split; [do 7 eexists; exact FRA|]. split; [exact STL|]. split; [exact STG|].
    split; [exists ja; exact XA|]. split; [exists jb; exact XB'|]. split; [exists jc; exact XC|].
    split; [rewrite L0; destruct (FFLAG _ _ _ _ _ 2 FF 256 AH ltac:(left; reflexivity)) as (X & _); exact X|].
    split; [exact XS|]. split; [exact SB|]. split; [exact US|]. split; [exact UD|]. split; [exact UDS|]. split; [exact DSK|].
    split; [exact GOT|]. split; [exact ARO|]. split; [exact DA| exact AZS].
  Qed.

  Lemma sinv_of_dinv : forall m tot, DINV m tot -> SINV m.
  Proof.
    intros m tot (BI & SAV & _ & STL & STG & XA & XB & XC & XL & XS & SB & US & UD & UDS & DSK & GOT & ARO & DA & AZS).
    split; [exact SAV|]. split; [exact STG|]. split; [exact XA|]. split; [exact XC|]. split; [exact SB|]. split; [exact US|].
    split; [exact UD|]. split; [exact UDS|]. split; [exact GOT|]. split; [exact ARO| exact AZS].
  Qed.

  (* [comment removed for export] *)
  Lemma sinv_w : forall m m' W, SINV m -> AHEAP AI L RNG st (FB2 FF :: LB) m -> munch W m m' -> wmono bsegs m m' -> wapart W -> aappW W -> SINV m'.
  Proof.
    intros m m' W (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS) AH MU WM HW AW.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (G3 : SPV - 543 <= SPA <= SPV - 512) by (clear - G3a G3b; lia).
    pose proof G_ff as (_ & _ & _ & _ & _ & _ & F7 & F8' & F9').
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    assert (DSH : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. apply aappW_shadow_disjoint; [exact AW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - A B C AT1 AT2; Z.div_mod_to_equations; lia. }
    split; [eapply rw_cells_transport; [exact SAV| exact MU| exact WM| apply HW; cbn; [clear| clear - G3| clear - G3| clear - S_DC G2 G3| clear - S_DS G2 G3| clear - F3 G1 G2 G3]; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MU| exact WM| apply HW; [clear - G3| clear| clear| clear - S_DC G2 G3| clear - S_DS G2 G3| clear - F3 G1 G2 G3]; lia]|].
    split; [exists ja; eapply rw_cells_transport; [exact XA| exact MU| exact WM| apply HW; cbn; [clear| clear - F3 G1| clear - F3 G1 G2 G3| clear - F7| clear - F8'| clear]; lia]|].
    split; [exists jc; eapply rw_cells_transport; [exact XC| exact MU| exact WM| apply HW; cbn; [clear| clear - F3 G1| clear - F3 G1 G2 G3| clear - F7| clear - F8'| clear]; lia]|].
    split; [eapply bytes_at_transport; [exact SB| exact MU| rewrite length_map; apply HW; [clear - SBL| clear - S_SR G2 G3| clear - S_SR G2 G3| clear - SR_DC| clear - D_SR| clear - F9']; lia]|].
    split; [eapply unpoisoned_munch; [exact US| exact MU| apply DSH; clear - SL1 SL2 SBL; lia]|].
    split; [eapply unpoisoned_munch; [exact UD| exact MU| apply DSH; clear - D1 D2 AT2; lia]|].
    split; [intros HC; eapply unpoisoned_munch; [exact (UDS HC)| exact MU| apply DSH; clear - D0 D3 HC; lia]|].
    split; [eapply rw_cells_transport; [exact GOT| exact MU| exact WM| apply HW; cbn; [clear| clear - S_GT G1 G2 G3 AT1| clear - S_GT G1 G2 G3 AT1| clear - GT_DC| clear - GT_DS| clear - FL]; lia]|].
    split; [eapply aro_client_transport; [exact ARO| exact MU| exact WM| exact AW]|].
    eapply azstk_transport; [exact AZS| exact MU| exact WM| exact AW| clear - G2 G1 AT1; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dm_inblk : forall b, 0 < zlen src ->
    ainblk (b :: LB) SRC (zlen src) /\ ainblk (b :: LB) DCTX 95992 /\ (0 < CAP -> ainblk (b :: LB) DST CAP).
  Proof.
    intros b NZ. pose proof B_sr as [ABS INS]. pose proof B_dc as [_ IBD]. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    split.
    - destruct (INS NZ) as [(bb & Hb & Hb1 & Hb2)|[IM1 IM2]]; [| pose proof (fk_ablk_lits _ _ ABS) as SL; unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia].
      exists bb. split; [right; exact Hb| split; [exact Hb1| exact Hb2]].
    - split; [destruct IBD as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]|].
      intros HC. destruct (proj2 (B_ds HC)) as (bb & Hb & Hb1 & Hb2). exists bb. split; [right; exact Hb| split; [exact Hb1| exact Hb2]].
  Qed.
  Lemma dm_inblk_sub : forall LB' X n X' n', ainblk LB' X n -> X <= X' -> X' + n' <= X + n -> ainblk LB' X' n'.
  Proof. intros LB' X n X' n' (bb & Hb & H1 & H2) A B. exists bb. split; [exact Hb| clear - H1 H2 A B; lia]. Qed.

  (* [comment removed for export] *)
  Lemma sinv_F : forall m m' W, SINV m -> AHEAP AI L RNG st (FB2 FF :: LB) m -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' ->
    ffr_pres W (FB2 FF :: LB) m m' -> wapart W -> aappW W -> 0 < zlen src -> SINV m'.
  Proof.
    intros m m' W (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS) AH MU WM FFR HW AW NZ.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (G3 : SPV - 543 <= SPA <= SPV - 512) by (clear - G3a G3b; lia).
    pose proof G_ff as (_ & _ & _ & _ & _ & _ & F7 & F8' & F9').
    destruct (FHL _ _ _ _ _ AH) as [FAB _].
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    destruct (dm_inblk (FB2 FF) NZ) as (IS & ID & IDS).
    (* [comment removed for export] *)
    assert (DSTK : forall X k, SPA + 408 <= X -> 0 <= k -> X + k <= 2^47 -> disjoint_from (W ++ fake_area L) X k).
    { intros X k H1 Hk H2. apply disjoint_from_app2.
      - apply HW; [exact Hk| clear - H1 G3; lia| clear - H1; lia| clear - H1 D2 G1 G2 G3; lia| intros HC; specialize (DSL HC); clear - H1 DSL G1 G2 G3; lia| clear - H1 F3 G1 G2 G3; lia].
      - cbn [disjoint_from fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *. clear - H1 Hk H2 A2 A1 G1 G2 G3 AT1 AT2. repeat split; Z.div_mod_to_equations; lia. }
    assert (PFF : forall X k a, FF <= X -> X + k <= FF + 256 -> disjoint_from W X k -> X <= a < X + k ->
              (in_fake (FB2 FF :: LB) a /\ outside W a) \/ (exists a', in_fake (FB2 FF :: LB) a' /\ a = shad a')).
    { intros X k a HX Hk DJ Ha. left. split; [exists 2, FF, 256; split; [left; reflexivity| clear - HX Hk Ha; lia]|].
      eapply disjoint_outside; [exact DJ| exact Ha]. }
    split; [eapply rw_cells_transport; [exact SAV| exact MU| exact WM| apply DSTK; cbn; clear - G3 G5; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MU| exact WM| apply DSTK; clear - G3 G5; lia]|].
    split.
    { exists ja. eapply rw_cells_magree; [exact FFR| exact XA|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros a Ha.
      eapply (PFF FF 128); [clear; lia| clear; lia| | exact Ha].
      apply HW; [clear; lia| clear - F3 G1; lia| clear - F3 G1 G2 G3; lia| clear - F7; lia| clear - F8'; lia| clear; lia]. }
    split.
    { exists jc. eapply rw_cells_magree; [exact FFR| exact XC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros a Ha.
      eapply (PFF (FF + 140) 116); [clear; lia| clear; lia| | exact Ha].
      apply HW; [clear; lia| clear - F3 G1; lia| clear - F3 G1 G2 G3; lia| clear - F7; lia| clear - F8'; lia| clear; lia]. }
    assert (DSR : disjoint_from W SRC (zlen src))
      by (apply HW; [clear - SBL| clear - S_SR G2 G3| clear - S_SR G2 G3| clear - SR_DC| clear - D_SR| clear - F9']; lia).
    split; [eapply (dm_fcall_bytes_pres AI FHL); [exact AH| rewrite length_map; exact IS| rewrite length_map; exact DSR| exact MU| exact FFR| exact SB]|].
    split; [eapply (dm_fcall_unp_pres AI FHL); [exact AH| exact IS| exact NZ| unfold KEND; clear - SL2; lia| exact AW| exact MU| exact FFR| exact US]|].
    split; [eapply (dm_fcall_unp_pres AI FHL); [exact AH| exact ID| clear; lia| unfold KEND; clear - D2 AT2; lia| exact AW| exact MU| exact FFR| exact UD]|].
    split; [intros HC; eapply (dm_fcall_unp_pres AI FHL); [exact AH| exact (IDS HC)| exact HC| unfold KEND; clear - D3; lia| exact AW| exact MU| exact FFR| exact (UDS HC)]|].
    split.
    { eapply rw_cells_transport; [exact GOT| exact MU| exact WM|]. apply disjoint_from_app2.
      - apply HW; cbn; [clear| clear - S_GT G1 G2 G3 AT1| clear - S_GT G1 G2 G3 AT1| clear - GT_DC| clear - GT_DS| clear - FL]; lia.
      - cbn [disjoint_from fake_area cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *. clear - A1. repeat split; Z.div_mod_to_equations; lia. }
    split; [eapply aro_client_transport_F; [exact ARO| exact MU| exact WM| exact AW| exact FAB]|].
    eapply azstk_transport_F; [exact AZS| exact MU| exact WM| exact AW| exact FAB| exact A8| clear - A2 G1; lia| clear - G1 G2 AT1; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sinv_sh : forall m m' i j, SINV m -> AHEAP AI L RNG st (FB2 FF :: LB) m -> munch [(SHF + i, SHF + j)] m m' -> wmono bsegs m m' ->
    0 <= i -> i <= j -> j <= 32 -> SINV m'.
  Proof.
    intros m m' i j (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS) AH MU WM Hi Hij Hj.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (G3 : SPV - 543 <= SPA <= SPV - 512) by (clear - G3a G3b; lia).
    pose proof G_ff as (_ & _ & _ & _ & _ & _ & F7 & F8' & F9').
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    (* [comment removed for export] *)
    assert (DJA : forall X k, (X + k <= 2147446784 \/ 17594333495296 <= X) -> disjoint_from [(SHF + i, SHF + j)] X k)
      by (intros X k H; cbn [disjoint_from]; clear - H GS1 GS2 Hi Hij Hj; split; [lia| exact I]).
    assert (DJS : forall X n, 0 <= X -> (X + n <= FF \/ FF + 256 <= X) -> disjoint_from [(SHF + i, SHF + j)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n H0 H1. cbn [disjoint_from]. rewrite !shad_div, ESHF. unfold ASHOFF. clear - H0 H1 F8 Hi Hij Hj. split; [| exact I]. Z.div_mod_to_equations. lia. }
    split; [eapply rw_cells_transport; [exact SAV| exact MU| exact WM| apply DJA; clear - G1 G2 G3 AT1; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MU| exact WM| apply DJA; clear - G1 G2 G3 AT1; lia]|].
    split; [exists ja; eapply rw_cells_transport; [exact XA| exact MU| exact WM| apply DJA; pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as X; cbn; clear - X; lia]|].
    split; [exists jc; eapply rw_cells_transport; [exact XC| exact MU| exact WM| apply DJA; pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as X; cbn; clear - X; lia]|].
    split; [eapply bytes_at_transport; [exact SB| exact MU| rewrite length_map; apply DJA; pose proof (fk_ablk_lits _ _ (proj1 B_sr)) as X; clear - X; lia]|].
    split; [eapply unpoisoned_munch; [exact US| exact MU| apply DJS; clear - SL1 F9'; lia]|].
    split; [eapply unpoisoned_munch; [exact UD| exact MU| apply DJS; clear - D1 F7; lia]|].
    split; [intros HC; eapply unpoisoned_munch; [exact (UDS HC)| exact MU| apply DJS; clear - D0 F8' HC; lia]|].
    split; [eapply rw_cells_transport; [exact GOT| exact MU| exact WM| apply DJA; cbn; clear; lia]|].
    split.
    { eapply aro_client_transport_gen; [exact WM| exact ARO| exact MU|]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF.
      clear - B1 B2 B3 FL Hi Hij Hj. split; [| exact I]. Z.div_mod_to_equations. lia. }
    destruct AZS as (RLO & RHI & U & H & W0 & AB & R). exists RLO, RHI.
    split; [| split; [exact H| split; [eapply wr_at_transport; [exact W0| exact WM]| split; [exact AB| exact R]]]].
    eapply unpoisoned_munch; [exact U| exact MU|]. cbn [disjoint_from]. rewrite !shad_div, ESHF. unfold ASHOFF. clear - G1 G2 F3 F8 Hi Hij Hj. split; [| exact I]. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma binv_w : forall m m' Wr Wa, BINV m -> munch (Wr ++ Wa) m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    Forall (fun iv => fst iv <= snd iv /\ ((DCTX <= fst iv /\ snd iv <= DCTX + 95992) \/ (0 < CAP /\ DST <= fst iv /\ snd iv <= DST + CAP))) Wr ->
    Forall (fun iv => fst iv <= snd iv /\ ((SPV - 7184 <= fst iv /\ snd iv <= SPV) \/ (FF + 128 <= fst iv /\ snd iv <= FF + 140))) Wa ->
    BINV m'.
  Proof.
    intros m m' Wr Wa (AH & FFR & MU0 & WM0 & MI) MU WM MI' HWr HWa.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    pose proof G_ff as (F1 & F2 & _ & F4 & _). pose proof B_dc as [ABD IBD].
    split.
    { eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
      apply Forall_app. split.
      - eapply Forall_impl; [| exact HWr]. intros [x y] [Hle [[A B]|(HC & A & B)]]; cbn [fst snd] in *.
        + apply fk_acr_inblk. destruct IBD as (bb & Hb & Hb1 & Hb2). exists bb. split; [right; exact Hb| clear - A B Hle Hb1 Hb2; lia].
        + apply fk_acr_inblk. destruct (proj2 (B_ds HC)) as (bb & Hb & Hb1 & Hb2). exists bb. split; [right; exact Hb| clear - A B Hle Hb1 Hb2; lia].
      - eapply Forall_impl; [| exact HWa]. intros [x y] [Hle [[A B]|[A B]]]; cbn [fst snd] in *.
        + left. left. clear - A B Hle G1 G2 G5. lia.
        + eapply fk_acr_frame; [left; reflexivity| clear - A; lia| clear - A B Hle; lia]. }
    split.
    { eapply ffr_pres_trans; [exact FFR|]. eapply dm_ffr_pres_weaken.
      - eapply (fk_ffr_fin AI L RNG st LB m m m' 2 FF 256 SHF 0 Wr Wa);
          [ exact AH | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WM ].
        + eapply Forall_impl; [| exact HWa]. intros [x y] [Hle [[A B]|[A B]]]; cbn [fst snd] in *; (split; [exact Hle|]).
          * left. clear - A B G1 G2 G5. lia.
          * right. split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH b Hb) as HB; clear - HB A B; lia| exists FF, (FF + 256); split; [exact F1| clear - A B; lia]].
        + eapply Forall_impl; [| exact HWr]. intros [x y] [Hle [[A B]|(HC & A & B)]]; cbn [fst snd] in *; (split; [| exact Hle]).
          * exists DCTX, (DCTX + 95992). split; [exact ABD| clear - A B; lia].
          * exists DST, (DST + CAP). split; [exact (proj1 (B_ds HC))| clear - A B; lia].
        + eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx.
          apply (proj1 (fk_outside_app _ _ _)) in Hx. destruct Hx as [Hx1 Hx2]. apply (proj1 (fk_outside_app _ _ _)) in Hx2. destruct Hx2 as [Hx2 _].
          apply (proj2 (fk_outside_app _ _ _)). split; [exact Hx1| exact Hx2].
      - unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as (O1 & O2 & _).
        clear - HWr O1 O2. induction HWr as [|[a b] Wr [Hle HH] HWr IH]; [exact I|]. cbn [outside fst snd] in *.
        split; [clear IH HWr; destruct HH as [[A B]|(HC & A & B)]; lia| exact IH]. }
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx.
      apply (proj1 (fk_outside_app _ _ _)) in Hx. destruct Hx as [Hx1 Hx2]. cbn [outside fake_area] in Hx1, Hx2.
      destruct Hx1 as (O1 & O2 & O3 & _). destruct Hx2 as (O4 & O5 & _).
      apply (proj2 (fk_outside_app _ _ _)). split.
      - clear - HWr O1 O2. induction HWr as [|[a b] Wr [Hle HH] HWr IH]; [exact I|]. cbn [outside fst snd] in *.
        split; [clear IH HWr; destruct HH as [[A B]|(HC & A & B)]; lia| exact IH].
      - clear - HWa O3 O4 A4 A5. induction HWa as [|[a b] Wa [Hle HH] HWa IH]; [exact I|]. cbn [outside fst snd] in *.
        split; [clear IH HWa; destruct HH as [[A B]|[A B]]; lia| exact IH]. }
    split; [exact (wmono_trans _ _ _ _ WM0 WM)| exact MI'].
  Qed.

  (* [comment removed for export] *)
  Lemma binv_F : forall m m' W, BINV m -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    AHEAP AI L RNG st (FB2 FF :: LB) m' -> ffr_pres W (FB2 FF :: LB) m m' ->
    Forall (fun iv => fst iv <= snd iv /\ ((DCTX <= fst iv /\ snd iv <= DCTX + 95992) \/ (0 < CAP /\ DST <= fst iv /\ snd iv <= DST + CAP)
                                            \/ (SPV - 7184 <= fst iv /\ snd iv <= SPV))) W ->
    BINV m'.
  Proof.
    intros m m' W (AH & FFR & MU0 & WM0 & MI) MU WM MI' AH' FFR' HW.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & _).
    split; [exact AH'|].
    split.
    { eapply ffr_pres_trans; [exact FFR|]. unfold ffr_pres in FFR' |- *. eapply magree_mono; [exact FFR'|].
      intros a [[(c & A & n & Hin & Ha) HO]|(a' & (c & A & n & Hin & Ha) & ->)].
      - left. split; [exists c, A, n; split; [right; exact Hin| exact Ha]|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        cbn [outside] in HO. destruct HO as (O1 & O2 & _).
        clear - HW Ha B3 O1 O2 G1 G2. induction HW as [|[x y] W [Hle HH] HW IH]; [exact I|]. cbn [outside fst snd] in *.
        split; [clear IH HW; destruct HH as [[P Q]|[(HC & P & Q)|[P Q]]]; lia| exact IH].
      - right. exists a'. split; [exists c, A, n; split; [right; exact Hin| exact Ha]| reflexivity]. }
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx.
      apply (proj1 (fk_outside_app _ _ _)) in Hx. destruct Hx as [Hx1 Hx2]. apply (proj2 (fk_outside_app _ _ _)). split; [| exact Hx2].
      cbn [outside] in Hx1. destruct Hx1 as (O1 & O2 & O3 & _).
      clear - HW O1 O2 O3. induction HW as [|[a b] W [Hle HH] HW IH]; [exact I|]. cbn [outside fst snd] in *.
      split; [clear IH HW; destruct HH as [[P Q]|[(HC & P & Q)|[P Q]]]; lia| exact IH]. }
    split; [exact (wmono_trans _ _ _ _ WM0 WM)| exact MI'].
  Qed.

  (* [comment removed for export] *)
  Lemma binv_sh : forall m m' i j, BINV m -> munch [(SHF + i, SHF + j)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    0 <= i -> i <= j -> j <= 32 -> BINV m'.
  Proof.
    intros m m' i j (AH & FFR & MU0 & WM0 & MI) MU WM MI' Hi Hij Hj.
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & _ & _ & _ & (A1 & A2 & A8 & A4 & A5) & _).
    pose proof G_ff as (F1 & F2 & _ & F4 & _).
    split.
    { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [cbn [fst snd]| constructor].
      replace (SHF + i) with (shad (FF + 8 * i)) by (rewrite ESHF, shad_div; unfold ASHOFF; clear - F8; Z.div_mod_to_equations; lia).
      replace (SHF + j - shad (FF + 8 * i)) with (j - i) by (rewrite ESHF, shad_div; unfold ASHOFF; clear - F8; Z.div_mod_to_equations; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 (FF + 8 * i) (j - i)); [left; reflexivity| clear - Hi; lia| clear - Hi Hij Hj; lia| clear - F8; Z.div_mod_to_equations; lia| clear - FL Hi; lia]. }
    split.
    { eapply ffr_pres_trans; [exact FFR|]. apply dm_ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m m m' 2 FF 256 SHF j [] []);
        [ exact AH | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear - Hj; lia | clear - Hi Hij; lia
        | constructor | constructor | apply ffr_pres_refl | | exact WM ].
      cbn [app]. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx Hi. lia. }
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx.
      rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx A4 A5 A8 F8 Hi Hj. Z.div_mod_to_equations. lia. }
    split; [exact (wmono_trans _ _ _ _ WM0 WM)| exact MI'].
  Qed.

  (* [comment removed for export] *)
  Lemma bdc_any : forall m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> dctx_any m DCTX.
  Proof.
    intros m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws (A1 & A2 & A3 & A4 & A5 & _ & A6 & A7 & _ & _ & (j1 & j2 & j3 & j4 & j5 & A8) & A9 & _).
    exists llt, mlt, oft, huf, pde, (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), expd, (zfh_cells h), pcs, dsz, bt, stg, le, fe, xs, ws, j1, j2, j3, j4, j5.
    split; [exact A1|]. split; [exact A2|]. split; [split; [exact A3| reflexivity]|]. split; [exact A4|]. split; [exact A5|].
    split; [exact A6|]. split; [exact A7|]. split; [exact A8| exact A9].
  Qed.

  Lemma bdc_w2 : forall W m m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws xs',
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m -> mem_inv bsegs m' ->
    disjoint_from W DCTX 30008 -> disjoint_from W (DCTX + 30096) 65896 ->
    dctx_xs bsegs m' DCTX xs' -> (fh_checksum h <> 0 -> exists j1 msz j2, xs' = xxh_cells j1 msz j2 /\ 0 <= msz < 32) ->
    BDC m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs' ws.
  Proof.
    intros W m m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws xs'
           (PT & H1 & FP & H3 & _ & _ & [H5C H5L] & H5OK & K_VCK & K_ISF & (jhb & ovd & dcb & dce & trace & TX) & [OWE OWX] & TB) MU WM MI MI' DJ1 DJ2 XS' XSI'.
    assert (TR1 : forall A cs, rw_cells bsegs m A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 30008 -> rw_cells bsegs m' A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ1 | exact L1 | clear - L2; lia]. }
    assert (TR2 : forall A cs, rw_cells bsegs m A cs -> DCTX + 30096 <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m' A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ2 | exact L1 | clear - L2; lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_h5, dctx_tx, dctx_owned in *.
    split; [apply TR1; [exact PT | clear; lia | cbn; clear; lia]|].
    split; [apply TR1; [exact H1 | clear; lia | cbn; clear; lia]|].
    split; [apply TR1; [exact FP | clear; lia | cbn; clear; lia]|].
    split; [apply TR1; [exact H3 | clear; lia | cbn; clear; lia]|].
    split; [exact XS'|]. split; [exact XSI'|].
    split; [split; [apply TR2; [exact H5C | clear; lia | rewrite (h5_cells_size _ H5L); clear; lia]| exact H5L]|].
    split; [exact H5OK|]. split; [exact K_VCK|]. split; [exact K_ISF|].
    split; [exists jhb, ovd, dcb, dce, trace; apply TR2; [exact TX | clear; lia | cbn; clear; lia]|].
    split; [split|].
    - eapply stk_transport_disjoint; [exact OWE | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ1 | clear; lia | clear; lia].
    - eapply stk_transport_disjoint; [exact OWX | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ2 | clear; lia | clear; lia].
    - eapply (tbl_frame TBL TBLL m m' W); [exact TB | exact MU | exact MI | exact MI' |].
      intros x Hx. eapply disjoint_outside; [exact DJ1 | clear - Hx; lia].
  Qed.

  Lemma bdc_w : forall W m m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m -> mem_inv bsegs m' ->
    disjoint_from W DCTX 95992 ->
    BDC m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws.
  Proof.
    intros W m m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws BD MU WM MI MI' DJ.
    pose proof BD as (_ & _ & _ & _ & [XSC XSSZ] & XSI & _).
    eapply bdc_w2; [exact BD| exact MU| exact WM| exact MI| exact MI'| | | | exact XSI].
    - eapply dm_disjoint_from_sub; [exact DJ| clear; lia| clear; lia].
    - eapply dm_disjoint_from_sub; [exact DJ| clear; lia| clear; lia].
    - split; [| exact XSSZ]. eapply rw_cells_transport; [exact XSC| exact MU| exact WM|]. rewrite XSSZ. eapply dm_disjoint_from_sub; [exact DJ| clear; lia| clear; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dm_dja : forall m i j X k, AHEAP AI L RNG st (FB2 FF :: LB) m -> 0 <= i -> i <= j -> j <= 32 ->
    (X + k <= 2147446784 \/ 17594333495296 <= X) -> disjoint_from [(SHF + i, SHF + j)] X k.
  Proof.
    intros m i j X k AH Hi Hij Hj H. pose proof (dm_geom m AH) as (_ & (FL & F3 & F8 & ESHF & GS1 & GS2) & _).
    cbn [disjoint_from]. clear - H GS1 GS2 Hi Hij Hj. split; [lia| exact I].
  Qed.
  Lemma dsk_keep : forall W m m', stk bsegs m DST (DST + CAP) -> munch W m m' -> wmono bsegs m m' ->
    (0 < CAP -> disjoint_from W DST CAP) -> stk bsegs m' DST (DST + CAP).
  Proof.
    intros W m m' DSK MU WM DJ. pose proof DSK as (D0 & D1 & _).
    destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
    - eapply stk_transport_disjoint; [exact DSK| exact MU| exact WM|]. replace (DST + CAP - DST) with CAP by (clear; lia). exact (DJ HC).
    - replace (DST + CAP) with DST by (clear - HC RC0; lia). apply dm_stk_empty; [exact D0| clear - D1 RC0; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma p_berr : forall m off sz tot res v32 vfl j0 j384 cs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot v32 vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> dctx_any m DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 -> zd_is_error res = true ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x851a8 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 res) x20 x22 x24 (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot res v32 vfl j0 j384 cs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x24 x26 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK DA ROFF RSZ RT RRES ER ACC KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & _ & _ & _ & (AT1 & AT2) & _).
    pose proof R_ff as (RF1 & RF2 & RF3).
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold DA. fk_hold ACC. fk_hold KA. fk_hold FFR. fk_hold MU0. fk_hold PRES0. fk_hold FRA.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_dc. fk_hold DSL.
    dm_hold_sep.
    unfold DSHO in XS.
    zstep.                                               (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    pose proof (munch_refl [(SHF + 16, SHF + 18)] m) as MU2. pose proof (wmono_refl bsegs m) as WM2.
    zstep. zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    change (rw_cells bsegs m2 SHF DSHC) in XS.
    assert (FRA2 : BFR m2 tot v32 vfl j0 j384)
      by (unfold DFR; eapply rw_cells_transport; [exact FRA| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| cbn; clear - G1 G2 G3a AT1; lia]]).
    pose proof FRA2 as FRA2u. unfold DFR in FRA2u.
    zstep. zstep. zstep.
    clear FRA2u.
    zstep.                                               (* [comment removed for export] *)
    gf_unhold.
    lazymatch goal with MIc : mem_inv bsegs m2 |- _ => rename MIc into MI2 end.
    pose proof (binv_sh m m2 16 18 BI MU2 WM2 MI2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as BI2.
    pose proof (sinv_sh m m2 16 18 SI AH MU2 WM2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as SI2.
    assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| clear - G1 AT1; lia]]).
    assert (XB2 : rw_cells bsegs m2 (FF + 128) cs)
      by (eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| rewrite XBS; pose proof (fk_ablk_lits _ _ (proj1 G_ff)) as X; clear - X; lia]]).
    assert (DSK2 : stk bsegs m2 DST (DST + CAP))
      by (eapply dsk_keep; [exact DSK| exact MU2| exact WM2| intros HC; eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X; lia]]).
    assert (DA2 : dctx_any m2 DCTX)
      by (eapply dm_dctx_any_transport; [exact DA| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 B_dc)) as X; clear - X; lia]]).
    eapply (PRES0 m2 off sz tot res); [| exact ROFF| exact RSZ| exact RT| exact RRES| exact ACC| intros E; rewrite ER in E; discriminate E| exact KA].
    eapply (dinv_of m2 tot); [exact BI2| exact SI2| exact STL2| exact FRA2| exact XB2| exact XBS| exact XS| exact DSK2| exact DA2].
  Qed.
  (* [comment removed for export] *)
  Lemma p_berr0 : forall m off sz tot res v32 vfl j0 j384 cs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x26 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot v32 vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> dctx_any m DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 -> zd_is_error res = true ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x851a4 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 (Z_to_bv 64 res) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot res v32 vfl j0 j384 cs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x26 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK DA ROFF RSZ RT RRES ER ACC KA.
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold DA. fk_hold ACC. fk_hold KA. fk_hold PRES0. fk_hold FRA. fk_hold XS.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_dc. dm_hold_sep.
    zstep.                                               (* [comment removed for export] *)
    gf_unhold. eapply (p_berr m off sz tot res v32 vfl j0 j384 cs); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_keep_F : forall W m m' cs, rw_cells bsegs m SPA cs -> cells_size cs = 408%nat -> AHEAP AI L RNG st (FB2 FF :: LB) m ->
    munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> disjoint_from W SPA 408 -> rw_cells bsegs m' SPA cs.
  Proof.
    intros W m m' cs FRA SZ AH MU WM DJ. pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & _ & _ & _ & _ & (A1 & A2 & A8 & A4 & A5) & _ & (AT1 & AT2) & _).
    eapply rw_cells_transport; [exact FRA| exact MU| exact WM|]. rewrite SZ. apply disjoint_from_app2; [exact DJ|].
    cbn [disjoint_from fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *. clear - A1 A2 G1 G2 G3a G3b G5 AT1 AT2. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma xs_keep_F : forall W m m' cs, rw_cells bsegs m SHF cs -> cells_size cs = 32%nat -> ffr_pres W (FB2 FF :: LB) m m' -> rw_cells bsegs m' SHF cs.
  Proof.
    intros W m m' cs XS SZ FFR. pose proof G_ff as (F1 & F2 & F3 & F4 & _).
    eapply rw_cells_magree; [exact FFR| exact XS|]. rewrite SZ. intros a Ha. right. exists (8 * (a - SHB)). rewrite F4, shad_div in Ha. unfold ASHOFF in Ha.
    split; [exists 2, FF, 256; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
    rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia.
  Qed.
  Lemma xb_keep_F : forall W m m' cs, rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> ffr_pres W (FB2 FF :: LB) m m' ->
    disjoint_from W (FF + 128) 12 -> rw_cells bsegs m' (FF + 128) cs.
  Proof.
    intros W m m' cs XB SZ FFR DJ.
    eapply rw_cells_magree; [exact FFR| exact XB|]. rewrite SZ. intros a Ha. left.
    split; [exists 2, FF, 256; split; [left; reflexivity| clear - Ha; lia]| eapply disjoint_outside; [exact DJ| exact Ha]].
  Qed.
  Lemma xs_keep_w : forall W m m' cs, rw_cells bsegs m SHF cs -> cells_size cs = 32%nat -> AHEAP AI L RNG st (FB2 FF :: LB) m ->
    munch W m m' -> wmono bsegs m m' -> aappW W -> rw_cells bsegs m' SHF cs.
  Proof.
    intros W m m' cs XS SZ AH MU WM AW. pose proof (dm_geom m AH) as (_ & (FL & F3 & F8 & ESHF & GS1 & GS2) & _ & _ & _ & _ & _ & (AT1 & AT2) & _).
    eapply rw_cells_transport; [exact XS| exact MU| exact WM|]. rewrite SZ.
    apply aappW_shadow_disjoint; [exact AW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - GS1 GS2; lia.
  Qed.
  Lemma dsk_keep_F : forall W m m', stk bsegs m DST (DST + CAP) -> AHEAP AI L RNG st (FB2 FF :: LB) m -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' ->
    ffr_pres W (FB2 FF :: LB) m m' -> (0 < CAP -> disjoint_from W DST CAP) -> 0 < zlen src -> stk bsegs m' DST (DST + CAP).
  Proof.
    intros W m m' DSK AH MU WM FFR DJ NZ. pose proof DSK as (D0 & D1 & _).
    destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
    - destruct (dm_inblk (FB2 FF) NZ) as (_ & _ & IDS).
      eapply (dm_fcall_stk_pres AI FHL); [exact AH| replace (DST + CAP - DST) with CAP by (clear; lia); exact (IDS HC)| replace (DST + CAP - DST) with CAP by (clear; lia); exact (DJ HC)| exact MU| exact WM| exact FFR| exact DSK].
    - replace (DST + CAP) with DST by (clear - HC RC0; lia). apply dm_stk_empty; [exact D0| clear - D1 RC0; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma p_gcb : forall m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384) ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x84fb8 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD FOK WIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof G_ff as (F1 & F2 & _ & F4 & _ & _ & F7 & F8' & F9'). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_src as [RSa RSb]. pose proof B_sr as [ABS _].
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; clear; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    assert (NZ : 0 < zlen src) by (clear - R9 RSZ ROFF NLEN; hlia).
    pose proof SI as (_ & _ & _ & _ & SB & US & _). pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold FFR. fk_hold MU0. fk_hold PRES0. fk_hold PBLK. fk_hold WIN. fk_hold GFH. fk_hold NSK.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_dc. fk_hold DSL. fk_hold SB. fk_hold US. fk_hold RSb. fk_hold GETCB.
    fk_hold F7. fk_hold F8'. fk_hold F9'.
    dm_hold_sep.
    unfold DFR in FRA. unfold DSHC in XS.
    pose proof (munch_refl [(SPA + 8, SPA + 32)] m) as MUA. pose proof (wmono_refl bsegs m) as WMA. pose proof MI as MIh. fk_hold MIh. fk_hold XS.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with MIc : mem_inv bsegs m1 |- _ => rename MIc into MI1 end.
    unfold fk_held in BI, SI, STL, XB, DSK, BD, MIh, XS.
    assert (AWA : aappW [(SPA + 8, SPA + 32)]).
    { unfold aappW, KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a G3b G5 AT1; hlia| apply Forall_nil]. }
    assert (WAA : wapart [(SPA + 8, SPA + 32)]) by (intros X k Hk A1 A2 A3 A4 A5; cbn [disjoint_from]; clear - Hk A2; repeat split; hlia).
    pose proof (binv_w m m1 [] _ BI MUA WMA MI1 ltac:(constructor)
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; hlia| apply Forall_nil])) as BI1.
    pose proof (sinv_w m m1 _ SI AH MUA WMA WAA AWA) as SI1.
    assert (STL1 : stk bsegs m1 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MUA| exact WMA| cbn; clear; repeat split; hlia]).
    assert (XB1 : rw_cells bsegs m1 (FF + 128) cs)
      by (eapply rw_cells_transport; [exact XB| exact MUA| exact WMA| rewrite XBS; cbn; clear - F3 G1 G2 G3a; repeat split; hlia]).
    pose proof (xs_keep_w _ m m1 _ XS eq_refl AH MUA WMA AWA) as XS1.
    assert (DSK1 : stk bsegs m1 DST (DST + CAP))
      by (eapply dsk_keep; [exact DSK| exact MUA| exact WMA| intros HC; specialize (DSL HC); cbn; clear - DSL G1 G2 G3a HC; repeat split; hlia]).
    assert (BD1 : BDC m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
      by (eapply bdc_w; [exact BD| exact MUA| exact WMA| exact MIh| exact MI1| cbn; clear - D2 G1 G2 G3a; repeat split; hlia]).
    pose proof BI1 as (AH1 & _).
    clear BI SI STL XB XS DSK BD MUA WMA MIh AH WAA AWA FFR MU0 WM0 SB US. clear m. rename m1 into m.
    rename BI1 into BI, SI1 into SI, STL1 into STL, XB1 into XB, XS1 into XS, DSK1 into DSK, BD1 into BD, MI1 into MI, AH1 into AH.
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD.
    (* [comment removed for export] *)
    zstep. zstep.
    replace (SRC + off + hsz) with (SRC + (off + hsz)) by (clear; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(SHF + 16, SHF + 18)] m) as MU3. pose proof (wmono_refl bsegs m) as WM3. pose proof MI as MI2h. fk_hold MI2h.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with MIc : mem_inv bsegs m3 |- _ => rename MIc into MI3 end.
    change (rw_cells bsegs m3 SHF DSHO) in XS. rename XS into XS3.
    unfold fk_held in BI, SI, STL, XB, DSK, BD, MI2h.
    pose proof (binv_sh m m3 16 18 BI MU3 WM3 MI3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as BI3.
    pose proof (sinv_sh m m3 16 18 SI AH MU3 WM3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as SI3.
    assert (STL3 : stk bsegs m3 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MU3| exact WM3| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| clear - G1 AT1; hlia]]).
    rename FRA into FRA3.                               (* [comment removed for export] *)
    assert (XB3 : rw_cells bsegs m3 (FF + 128) cs)
      by (eapply rw_cells_transport; [exact XB| exact MU3| exact WM3| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| rewrite XBS; pose proof (fk_ablk_lits _ _ F1) as X; clear - X; hlia]]).
    assert (DSK3 : stk bsegs m3 DST (DST + CAP))
      by (eapply dsk_keep; [exact DSK| exact MU3| exact WM3| intros HC; eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X; hlia]]).
    assert (BD3 : BDC m3 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
      by (eapply bdc_w; [exact BD| exact MU3| exact WM3| exact MI2h| exact MI3| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 B_dc)) as X; clear - X; hlia]]).
    pose proof BI3 as (AH3 & _).
    clear BI SI STL XB DSK BD MU3 WM3 MI2h.
    (* [comment removed for export] *)
    fk_hold BI3. fk_hold STL3. fk_hold XB3. fk_hold DSK3. fk_hold BD3.
    zstep. zstep. zstep. zstep. zstep.
    unfold fk_held in BI3, STL3, XB3, DSK3, BD3, GETCB.
    pose proof SI3 as (SAV3 & STG3 & XA3 & XC3 & SB3 & US3 & UD3 & UDS3 & GOT3 & ARO3 & AZS3).
    assert (ART3 : art m3).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH3) as (_ & A & B & C & D & E & F' & G' & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
    assert (UB3 : unpoisoned m3 (FF + 128) (FF + 140)) by (apply dsho_unp; [rewrite <- F4; exact XS3| exact F8| exact FL| clear - F3 AT2; hlia]).
    unfold zd_getcblock_stmtA, APZD_GETCBLOCK in GETCB.
    eapply evtF_cut.
    { eapply (GETCB RNG) with (SPV := SPA) (lo := lo) (SRC := SRC) (BP := FF + 128) (src := src) (ip := off + hsz) (size := sz - hsz);
      first [ exact SB3 | exact OK | exact XB3 | exact XBS | exact STL3 | exact MI3 | exact ART3 | reflexivity
            | lazymatch goal with
              | |- 0 <= off + hsz => clear - ROFF RHS; hlia
              | |- 0 <= sz - hsz => clear - RH; hlia
              | |- off + hsz + (sz - hsz) <= _ => clear - RSZ NLEN; hlia
              | |- 0 < SRC => clear - SL1; hlia
              | |- 0 < FF + 128 => clear - FL; hlia
              | |- (FF + 128) mod 4 = 0 => clear - F8; Z.div_mod_to_equations; hlia
              | |- lo <= SPA - _ => clear - G2 G3a; hlia
              | |- SPA < _ => clear - G3b G5; hlia
              | |- FF + 128 + 12 <= lo \/ _ => clear - F3 G1; hlia
              | |- SRC + _ <= lo \/ SPA <= SRC => clear - S_SR G3b; hlia
              | |- areg _ _ SRC _ => intros _; split; [exact ABS| split; [exact US3| split; [exact RSa| exact RSb]]]
              | |- areg _ _ (FF + 128) _ => intros _; split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia] | split; [replace (FF + 128 + 12) with (FF + 140) by (clear; lia); exact UB3| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
              | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; hlia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; hlia]| exact RI]]
              | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; f_equal; lia
              end
            | lazymatch goal with |- ?Gg => idtac "GETCB-LEFT:" Gg end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & cs4 & -> & MU4 & WM4 & MI4 & STL4 & XB4 & XBS4 & XBOK).
    rd_retlit.
    (* [comment removed for export] *)
    assert (AW4 : aappW [(FF + 128, FF + 128 + 12); (SPA - 16, SPA)]).
    { pose proof (ablk_disj_band _ _ F1) as FB. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - FB; hlia|]. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; hlia| apply Forall_nil]. }
    assert (WA4 : wapart [(FF + 128, FF + 128 + 12); (SPA - 16, SPA)]) by (intros X k Hk A1 A2 A3 A4 A5; cbn [disjoint_from]; clear - Hk A1 A5 G2 G3a; repeat split; hlia).
    pose proof (binv_w m3 m4 [] _ BI3 MU4 WM4 MI4 ltac:(constructor)
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; hlia| apply Forall_nil]])) as BI4.
    pose proof (sinv_w m3 m4 _ SI3 AH3 MU4 WM4 WA4 AW4) as SI4.
    assert (FRA4 : BFR m4 tot v32 vfl j0 j384)
      by (unfold DFR; eapply rw_cells_transport; [exact FRA3| exact MU4| exact WM4| cbn; clear - F3 G1 G2 G3a; repeat split; hlia]).
    pose proof (xs_keep_w _ m3 m4 _ XS3 eq_refl AH3 MU4 WM4 AW4) as XS4.
    assert (DSK4 : stk bsegs m4 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK3| exact MU4| exact WM4| intros HC; specialize (DSL HC); cbn; clear - DSL F8' HC G1 G2 G3a; repeat split; hlia]).
    assert (BD4 : BDC m4 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws) by (eapply bdc_w; [exact BD3| exact MU4| exact WM4| exact MI3| exact MI4| cbn; clear - F7 D2 G1 G2 G3a; repeat split; hlia]).
    pose proof BI4 as (AH4 & _).
    clear SAV3 STG3 XA3 XC3 SB3 US3 UD3 UDS3 GOT3 ARO3 AZS3 ART3 UB3 FRA3 XS3 BI3 SI3 STL3 XB3 DSK3 BD3 MU4 WM4 MI3 AH3 AW4 WA4.
    (* [comment removed for export] *)
    assert (RRET : 0 <= cblock_ret (get_cblock_size src (off + hsz) (sz - hsz)) < 18446744073709551616).
    { clear - OK. unfold get_cblock_size.
      destruct (sz - hsz <? ZD_blockHeaderSize); cbn [cblock_ret].
      - unfold ZERR, ZE_srcSize_wrong. lia.
      - pose proof (cblock_props_range (le24 src (off + hsz)) (le24_range src OK (off + hsz))) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
        unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected.
        destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia. }
    fk_hold BI4. fk_hold SI4. fk_hold STL4. fk_hold XB4. fk_hold XS4. fk_hold DSK4. fk_hold BD4. fk_hold XBOK. fk_hold FRA4.
    zstep. zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      unfold fk_held in BI4, SI4, STL4, XB4, XS4, DSK4, BD4, ACC, KA, FRA4.
      eapply (p_berr0 m4 off sz tot _ v32 vfl j0 j384 cs4);
        [exact BI4| exact SI4| exact STL4| exact FRA4| exact XB4| exact XBS4| exact XS4| exact DSK4| exact (bdc_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BD4)
        | exact ROFF| exact RSZ| exact RT| exact RRET| | exact ACC| exact KA].
      apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. clear - KE RRET. lia.
    - (* [comment removed for export] *)
      destruct (get_cblock_size src (off + hsz) (sz - hsz)) as [[cbs bp]|] eqn:GCB; cbn [cblock_ret] in *;
        [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; clear - KE; hlia].
      unfold fk_held in XBOK, XB4. rewrite (XBOK cbs bp eq_refl) in XB4. fk_hold XB4.
      unfold fk_held in FRA4. unfold DFR in FRA4.
      pose proof (munch_refl [(SPA + 32, SPA + 40)] m4) as MU5. pose proof (wmono_refl bsegs m4) as WM5. pose proof MI4 as MI4h. fk_hold MI4h.
      zstep.                                             (* [comment removed for export] *)
      zstep. zstep.
      replace (DST + tot + (CAP - tot)) with (DST + CAP) by (clear; lia).
      zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      lazymatch goal with MIc : mem_inv bsegs m5 |- _ => rename MIc into MI5 end.
      unfold fk_held in BI4, SI4, STL4, XB4, XS4, DSK4, BD4, GCB, ACC, KA, PBLK, WIN, MI4h.
      assert (AW5 : aappW [(SPA + 32, SPA + 40)]).
      { unfold aappW, KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a G3b G5 AT1; hlia| apply Forall_nil]. }
      assert (WA5 : wapart [(SPA + 32, SPA + 40)]) by (intros X k Hk A1 A2 A3 A4 A5; cbn [disjoint_from]; clear - Hk A2; repeat split; hlia).
      pose proof (binv_w m4 m5 [] _ BI4 MU5 WM5 MI5 ltac:(constructor)
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; hlia| apply Forall_nil])) as BI5.
      pose proof (sinv_w m4 m5 _ SI4 AH4 MU5 WM5 WA5 AW5) as SI5.
      assert (STL5 : stk bsegs m5 lo SPA) by (eapply stk_transport_disjoint; [exact STL4| exact MU5| exact WM5| cbn; clear; repeat split; hlia]).
      assert (XB5 : rw_cells bsegs m5 (FF + 128) (bp_cells bp))
        by (eapply rw_cells_transport; [exact XB4| exact MU5| exact WM5| cbn; clear - F3 G1 G2 G3a; repeat split; hlia]).
      pose proof (xs_keep_w _ m4 m5 _ XS4 eq_refl AH4 MU5 WM5 AW5) as XS5.
      assert (DSK5 : stk bsegs m5 DST (DST + CAP))
        by (eapply dsk_keep; [exact DSK4| exact MU5| exact WM5| intros HC; specialize (DSL HC); cbn; clear - DSL G1 G2 G3a HC; repeat split; hlia]).
      assert (BD5 : BDC m5 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
        by (eapply bdc_w; [exact BD4| exact MU5| exact WM5| exact MI4h| exact MI5| cbn; clear - D2 G1 G2 G3a; repeat split; hlia]).
      assert (NEC : zd_is_error cbs = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - KE RRET; hlia).
      pose proof (PBLK (Z.to_nat (sz - hsz)) off sz tot hsz h PFX (off + hsz) (sz - hsz) 0) as HB.
      unfold B_HEAD in HB. replace (DST + tot + 0) with (DST + tot) in HB by (clear; lia).
      eapply HB; [clear - RH; hlia| exact FOK| exact WIN| clear; lia| clear; lia| clear - RT; hlia| intros ip' rem' o' D; exact D| exact KA
                | exact BI5| exact SI5| exact STL5| exact FRA4| exact XB5| exact XS5| exact DSK5| exact BD5| exact GCB| exact NEC].
  Qed.
End DM.
End CANSEC1.
