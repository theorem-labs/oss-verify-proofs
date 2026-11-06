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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_block_iface AZ_blk_iface5 AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d AZ_dmf_e AZ_dmf_f.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Lemma dm_ffr_pres_weaken : forall W W' LB (m m' : amem), ffr_pres W LB m m' -> sub_fp W W' -> ffr_pres W' LB m m'.
Proof.
  intros W W' LB m m' H HS. unfold ffr_pres in *. eapply magree_mono; [exact H|].
  intros a [[IFa OW]|EX]; [left; split; [exact IFa| apply HS; exact OW] | right; exact EX].
Qed.

Lemma dm_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
Qed.

Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Lemma dm_sh_rd0s : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr p 3 + SHB)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.

(* [comment removed for export] *)
Lemma dm_h5_begin : forall ws, length ws = 44%nat -> h5_frame_ok ws ->
  h5_frame_ok (wupd (wupd ws H5_isFrameDecompression (Z_to_bv 64 1)) H5_dictID wz0)
  /\ wnth (wupd (wupd ws H5_isFrameDecompression (Z_to_bv 64 1)) H5_dictID wz0) H5_isFrameDecompression = Z_to_bv 64 1.
Proof.
  intros ws L OK. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [| discriminate L].
  unfold h5_frame_ok in *.
  cbv beta iota delta [wnth wupd nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
      H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression H5_dictID] in *.
  split; [exact OK| reflexivity].
Qed.

Lemma dm_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & W & R) H1 H2. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.
Lemma h5_split44 : forall ws : list word, length ws = 44%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43,
  ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21; w22; w23; w24; w25; w26; w27; w28; w29; w30; w31; w32; w33; w34; w35; w36; w37; w38; w39; w40; w41; w42; w43].
Proof.
  intros ws L. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [| discriminate L]. do 44 eexists. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

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
  Hypothesis S_GT : 0xcc668 + 16 <= lo \/ SPV <= 0xcc668.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0xcc668 + 16 <= DCTX \/ DCTX + 95992 <= 0xcc668.
  Hypothesis GT_DS : 0xcc668 + 16 <= DST \/ DST + CAP <= 0xcc668.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 7088 /\ SPV - 447 <= SPA <= SPV - 416 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
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
  Notation BINV := (AZ_dmf_f.BINV AI L RNG st LB m0 SPV DCTX DST CAP FF).
  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 SHF) x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation DFR := (AZ_dmf_f.DFR DCTX DST FF).
  Notation DINV := (AZ_dmf_f.DINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG).
  (* [comment removed for export] *)
  Notation AINV := (AZ_dmf_f.AINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Notation LHst mm off sz tot x1 x10 x12 x13 x14 x19 x24 x25 x28 x29 x30 x31 :=
    (STpc 0x84c60 mm x1 (Z_to_bv 64 8) (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x10 (Z_to_bv 64 5) x12 x13 x14 (Z_to_bv 64 1) (Z_to_bv 64 5) (Z_to_bv 64 4)
          (Z_to_bv 64 DCTX) x19 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) x24 x25 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 0) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Ltac dm_hold_sep := fk_hold S_DC; fk_hold S_DS; fk_hold S_SR; fk_hold S_GT; fk_hold D_DC; fk_hold D_SR; fk_hold SR_DC; fk_hold GT_DC; fk_hold GT_DS;
    fk_hold DNULL; fk_hold DNN; fk_hold B_ds; fk_hold R_ds; fk_hold B_sr; fk_hold B_dc; fk_hold G_ff; fk_hold G_flg.
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
  Hypothesis XXHRESET : zd_xxh_reset_stmtA.

  Notation SINV := (AZ_dmf_f.SINV RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF FLG).
  Notation wapart := (AZ_dmf_f.wapart SPA lo DCTX DST CAP FF).
  Notation BDC0 := (AZ_dmf_e.BDC0 DCTX).
  Notation BDC := (AZ_dmf_f.BDC DCTX TBL).
  Notation FRAME_OK := (AZ_dmf_f.FRAME_OK CAP src size).
  Notation KA_T := (AZ_dmf_f.KA_T AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Notation BFR mm tot v24 v32 v40 vfl j0 j288 :=
    (rw_cells bsegs mm SPA (DFR (Z_to_bv 64 ((DCTX + 29960) ≫ 3 + SHB)) (Z_to_bv 64 ((DCTX + 30112) ≫ 3)) v24 v32 v40 vfl (Z_to_bv 64 (CAP - tot)) j0 j288)).
  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Notation dm_geom := (AZ_dmf_f.dm_geom AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation sinv_w := (AZ_dmf_f.sinv_w AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST S_DC S_DS S_SR S_GT D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation binv_w := (AZ_dmf_f.binv_w AI fflag L RNG st LB m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds LBH FHL).
  Notation xs_keep_w := (AZ_dmf_f.xs_keep_w AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation dsk_keep := (AZ_dmf_f.dsk_keep DST CAP RC0).

  (* [comment removed for export] *)
  Hypothesis PGCB : forall m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v24 v32 v40 vfl j0 j288 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot v24 v32 v40 vfl j0 j288 ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x8507c m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 hsz) (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz)
                              (Z_to_bv 64 (-72)) x25 (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation CKSst mm off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 :=
    (STpc 0x84f44 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 hsz) (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz)
          (Z_to_bv 64 (-72)) x25 (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Ltac dc_sh UD RDS k :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (dm_sh_rd0s mm DCTX 95992 (DCTX + k) UD ltac:(clear; lia)
                  ltac:(match goal with D2 : DCTX mod 8 = 0 |- _ => clear - D2; Z.div_mod_to_equations; lia end)
                  ltac:(match goal with DCr : 6459392 <= DCTX /\ _ |- _ => clear - DCr; lia end)
                  ltac:(match goal with DCr : 6459392 <= DCTX /\ _, ATR : (_ <= ATOP <= _) |- _ => clear - DCr ATR; lia end)) as RDz;
    assert (RTz : rng RNG ((DCTX + k) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RDS|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; match goal with D2 : DCTX mod 8 = 0 |- _ => clear - D2; Z.div_mod_to_equations; lia end)
    end.
  (* [comment removed for export] *)
  Ltac ud_refresh UD0 UD MU AW DCr ATR :=
    try clear UD; pose proof UD0 as UD; unfold fk_held in UD;
    eapply unpoisoned_munch in UD; [| exact MU| apply aappW_shadow_disjoint; [exact AW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - DCr ATR; Z.div_mod_to_equations; lia].
  Ltac nrm_not_by tac := match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by tac end.

  (* [comment removed for export] *)
  Lemma p_pcs : forall m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v16 v24 v32 v40 vfl j0 j288 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA ->
    rw_cells bsegs m SPA (DFR (Z_to_bv 64 ((DCTX + 29960) ≫ 3 + SHB)) v16 v24 v32 v40 vfl (Z_to_bv 64 (CAP - tot)) j0 j288) ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x85008 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 hsz) (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz)
                              (Z_to_bv 64 (-72)) x25 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 ((DCTX + 30112) ≫ 3)) x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v16 v24 v32 v40 vfl j0 j288 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD FOK WIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (DCr : 6459392 <= DCTX /\ DCTX + 95992 <= ATOP) by (clear - D1 D2; lia).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof G_ff as (F1 & F2 & _ & F4 & _ & _ & F7 & F8' & F9'). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_dc as [RD RDS]. pose proof B_dc as [ABD IBD].
    pose proof RD8 as DM8.
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; clear; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    pose proof B_sr as [ABS _]. pose proof (fk_ablk_lits _ _ ABS) as SBL0.
    pose proof SI as (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS). pose proof UD as UD0. fk_hold UD0.
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    pose proof BD as (PT & H1 & FP & H3 & XSC & XSK & H5 & H5OK & KVC & ISF & TX & OWN & TB).
    assert (SDA : DCTX + 95992 <= SPA \/ SPV <= DCTX) by (clear - S_DC G2 G3a; lia).
    (* [comment removed for export] *)
    destruct H5 as [H5C H5L]. pose proof H5OK as (_ & _ & _ & K_MBS & _).
    destruct (h5_split44 ws H5L) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21
                                     & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & EWS).
    pose proof H5C as H5Co. rewrite EWS in H5C, K_MBS.
    cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_maxBlockSizeParam] in H5C, K_MBS. unfold wz0 in K_MBS. subst w23.
    unfold dctx_h3 in H3.
    unfold DFR in FRA.
    assert (AWA : aappW [(SPA + 16, SPA + 24); (DCTX + 29976, DCTX + 29984)]).
    { pose proof (ablk_disj_band _ _ ABD) as DBD. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBD; lia| apply Forall_nil]. }
    fk_hold KA. fk_hold ACC. fk_hold WIN. fk_hold NSK. fk_hold PGCB. fk_hold XXHRESET. fk_hold FFR. fk_hold MU0. fk_hold EWS. fk_hold GFH. fk_hold FOK. fk_hold H5OK. fk_hold XSK. fk_hold KVC.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold F7. fk_hold F8'. fk_hold F9'. fk_hold DSL. fk_hold IBD. fk_hold LBH. fk_hold RFS. fk_hold RSTKT.
    fk_hold SAV. fk_hold STG. fk_hold XA. fk_hold XC. fk_hold SB. fk_hold US. fk_hold UDS. fk_hold GOT. fk_hold ARO. fk_hold AZS. fk_hold XB. fk_hold XS. fk_hold DSK. fk_hold STL.
    fk_hold PT. fk_hold H1. fk_hold FP. fk_hold XSC. fk_hold TX. fk_hold OWN. fk_hold TB. fk_hold SI. fk_hold BI. fk_hold H5Co. fk_hold BD.
    fk_hold FLF. fk_hold FLD. fk_hold FLS. fk_hold A4. fk_hold A5.
    dm_hold_sep.
    pose proof (munch_refl [(SPA + 16, SPA + 24); (DCTX + 29976, DCTX + 29984)] m) as MUA. pose proof (wmono_refl bsegs m) as WMA. pose proof MI as MIh. fk_hold MIh.
    (* [comment removed for export] *)
    zstep.
    ud_refresh UD0 UD MUA AWA DCr ATR.
    (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    dc_sh UD RDS 29976. zstep. zstep. zstep. clear RDz RTz.   (* [comment removed for export] *)
    try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. try replace (uxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                     (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    zstep. nrm_not_by ltac:(clear - RS0 RS1 ROFF RSZ RH RHS NLEN; lia).   (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    ud_refresh UD0 UD MUA AWA DCr ATR.
    zstep. if_cases KU; zify_cond KU; [exfalso; clear - KU RS0 RS1 ROFF RSZ RH RHS NLEN; lia| clear KU].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    dc_sh UD RDS 30232. zstep. zstep. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                     (* [comment removed for export] *)
    zstep. rewrite (sx32w_small 0) by (clear; lia).      (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    zstep. if_true.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with MIc : mem_inv bsegs m2 |- _ => rename MIc into MI2 end.
    gf_unhold.
    (* [comment removed for export] *)
    assert (DJ2 : forall X k, (X + k <= SPA + 16 \/ SPA + 24 <= X) -> (X + k <= DCTX + 29976 \/ DCTX + 29984 <= X) -> 0 <= k ->
              disjoint_from [(SPA + 16, SPA + 24); (DCTX + 29976, DCTX + 29984)] X k)
      by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; lia).
    pose proof (binv_w m m2 [(DCTX + 29976, DCTX + 29984)] [(SPA + 16, SPA + 24)] BI
                  ltac:(eapply munch_weaken; [| exact MUA]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia) WMA MI2
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])
                  ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI2.
    assert (WA2 : wapart [(SPA + 16, SPA + 24); (DCTX + 29976, DCTX + 29984)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; apply DJ2; [clear - Q2; lia| clear - Q3; lia| exact Hk]).
    pose proof (sinv_w m m2 _ SI AH MUA WMA WA2 AWA) as SI2.
    assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MUA| exact WMA| apply DJ2; [clear; lia| clear - S_DC G2 G3a G3b; lia| clear - G1 G2 G3a ATR; lia]]).
    assert (XB2 : rw_cells bsegs m2 (FF + 128) cs) by (eapply rw_cells_transport; [exact XB| exact MUA| exact WMA| rewrite XBS; apply DJ2; [clear - F3 G1 G2 G3a; lia| clear - F7; lia| clear; lia]]).
    pose proof (xs_keep_w _ m m2 _ XS eq_refl AH MUA WMA AWA) as XS2.
    assert (DSK2 : stk bsegs m2 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MUA| exact WMA| intros HC; specialize (DSL HC); apply DJ2; [clear - DSL G1 G2 G3a; lia| clear - D_DC HC; lia| clear - HC; lia]]).
    assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd (Z_to_bv 64 (bv_unsigned pcs + hsz)) dsz bt stg le fe xs ws).
    { split; [unfold dctx_ptrs in *; eapply rw_cells_transport; [exact PT| exact MUA| exact WMA| apply DJ2; cbn; [clear - SDA G3b| clear| clear]; lia]|].
      split; [unfold dctx_h1 in *; eapply rw_cells_transport; [exact H1| exact MUA| exact WMA| apply DJ2; cbn; [clear - SDA G3b| clear| clear]; lia]|].
      split; [eapply rw_cells_transport; [exact FP| exact MUA| exact WMA| apply DJ2; unfold zfh_cells; cbn; [clear - SDA G3b| clear| clear]; lia]|].
      split; [unfold dctx_h3; first [exact H3 | lazymatch goal with |- ?G => idtac "H3-LEFT:" G; fail end]|].
      split; [destruct XSC as [XSC1 XSSZ]; split; [eapply rw_cells_transport; [exact XSC1| exact MUA| exact WMA| rewrite XSSZ; apply DJ2; [clear - SDA G3b| clear| clear]; lia]| exact XSSZ]|].
      split; [exact XSK|].
      split; [split; [eapply rw_cells_transport; [exact H5Co| exact MUA| exact WMA| rewrite (h5_cells_size _ H5L); apply DJ2; [clear - SDA G3b| clear| clear]; lia]| exact H5L]|].
      split; [exact H5OK|]. split; [exact KVC|]. split; [exact ISF|].
      split; [destruct TX as (jhb & ovd & dcb & dce & trace & TX1); exists jhb, ovd, dcb, dce, trace; unfold dctx_tx in *;
              eapply rw_cells_transport; [exact TX1| exact MUA| exact WMA| apply DJ2; cbn; [clear - SDA G3b| clear| clear]; lia]|].
      split; [destruct OWN as [OWE OWX]; split; (eapply stk_transport_disjoint; [eassumption| exact MUA| exact WMA| apply DJ2; [clear - SDA G3b| clear| clear]; lia])|].
      eapply (tbl_frame TBL TBLL); [exact TB| exact MUA| exact MIh| exact MI2| intros x Hx; cbn [outside]; clear - Hx SDA G3b; repeat split; lia]. }
    clear MUA WMA.
    eapply (PGCB m2 off sz tot hsz h PFX llt mlt oft huf pde expd _ dsz bt stg le fe xs ws v24 v32 v40 vfl j0 j288 cs);
      [exact BI2| exact SI2| exact STL2| exact FRA| exact XB2| exact XBS| exact XS2| exact DSK2| exact BD2| exact FOK| exact WIN| exact KA].
  Qed.

  (* [comment removed for export] *)
  Lemma p_cks : forall m4 off sz tot hsz h PFX xs ws jhb ovd dcb dce v8 v16 v24 v32 v40 vfl j0 j288 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word),
    BINV m4 -> SINV m4 -> stk bsegs m4 lo SPA -> rw_cells bsegs m4 SPA (DFR v8 v16 v24 v32 v40 vfl (Z_to_bv 64 (CAP - tot)) j0 j288) ->
    rw_cells bsegs m4 (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m4 SHF DSHC -> stk bsegs m4 DST (DST + CAP) ->
    BDC0 m4 PFX (zfh_cells h) xs ws jhb ovd dcb dce ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (CKSst m4 off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31).
  Proof.
    intros m4 off sz tot hsz h PFX xs ws jhb ovd dcb dce v8 v16 v24 v32 v40 vfl j0 j288 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD FOK WIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m4 AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (DCr : 6459392 <= DCTX /\ DCTX + 95992 <= ATOP) by (clear - D1 D2; lia).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof G_ff as (F1 & F2 & _ & F4 & _ & _ & F7 & F8' & F9'). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_dc as [RD RDS]. pose proof B_dc as [ABD IBD].
    pose proof RD8 as D2'. rename D2' into DM8.
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & RFCS & RWIN & RBSM & _ & RCK & _).
    pose proof BD as (PT & H1 & [FP FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & ISF & TX & OWN & BHUF & BREP). clear BD.
    pose proof SI as (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS). pose proof UD as UD0. fk_hold UD0.
    assert (SDA : DCTX + 95992 <= SPA \/ SPV <= DCTX) by (clear - S_DC G2 G3a; lia).
    (* [comment removed for export] *)
    pose proof H5OK as (K_FMT & K_FIC & K_RMD & K_MBS & K_REST).
    destruct (h5_split44 ws H5L) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21
                                     & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & EWS).
    rewrite EWS in H5C, K_FMT, K_FIC, K_RMD, K_MBS, ISF.
    cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_isFrameDecompression] in H5C, K_FMT, K_FIC, K_RMD, K_MBS, ISF.
    unfold wz0 in K_FMT, K_FIC, K_RMD, K_MBS. subst w1 w2 w21 w23 w12.
    pose proof FP as FPz. unfold zfh_cells in FP. unfold dctx_h3 in H3.
    unfold DFR in FRA.
    fk_hold KA. fk_hold ACC. fk_hold WIN. fk_hold NSK. fk_hold PGCB. fk_hold XXHRESET. fk_hold FFR. fk_hold MU0. fk_hold K_REST. fk_hold EWS. fk_hold GFH.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold F7. fk_hold F8'. fk_hold F9'. fk_hold DSL. fk_hold IBD. fk_hold LBH. fk_hold RFS. fk_hold RSTKT.
    fk_hold SAV. fk_hold STG. fk_hold XA. fk_hold XC. fk_hold SB. fk_hold US. fk_hold UDS. fk_hold GOT. fk_hold ARO. fk_hold AZS. fk_hold XB. fk_hold XS. fk_hold DSK. fk_hold STL.
    fk_hold PT. fk_hold H1. fk_hold FPz. fk_hold XSC. fk_hold TX. fk_hold OWN. fk_hold BHUF. fk_hold BREP. fk_hold SI. fk_hold BI.
    fk_hold FLF. fk_hold FLD. fk_hold FLS. fk_hold A4. fk_hold A5.
    dm_hold_sep.
    (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    dc_sh UD RDS 30224. zstep. zstep. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                     (* [comment removed for export] *)
    zstep. rewrite (sx32w_small 0) by (clear; lia).      (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR; [| exfalso; clear - KR; lia]. clear KR.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    zstep. zstep.                                        (* [comment removed for export] *)
    assert (AWA : aappW [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)]).
    { pose proof (ablk_disj_band _ _ ABD) as DBD. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBD; lia| apply Forall_nil]. }
    pose proof (munch_refl [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)] m4) as MUA. pose proof (wmono_refl bsegs m4) as WMA. pose proof MI as MIh. fk_hold MIh.
    zstep.                                               (* [comment removed for export] *)
    ud_refresh UD0 UD MUA AWA DCr ATR.
    dc_sh UD RDS 29960. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
    zstep. if_false.                                     (* [comment removed for export] *)
    zstep. rewrite (sx32w_small (fh_checksum h)) by (clear - RCK; lia).   (* [comment removed for export] *)
    zstep. zstep.                                        (* [comment removed for export] *)
    zstep. if_cases KC; zify_cond KC.                    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      dc_sh UD RDS 30112. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
      zstep. if_false.                                   (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      lazymatch goal with MIc : mem_inv bsegs m6 |- _ => rename MIc into MI6 end.
      gf_unhold.
      lazymatch type of H5C with rw_cells _ _ _ (_ :: _ :: _ :: C4 ?z :: _) => pose (vck := z) end.
      (* [comment removed for export] *)
      assert (DJ6 : forall X k, (X + k <= SPA + 8 \/ SPA + 16 <= X) -> (X + k <= DCTX + 30112 \/ DCTX + 30116 <= X) -> 0 <= k ->
                disjoint_from [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)] X k)
        by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; lia).
      pose proof (binv_w m4 m6 [(DCTX + 30112, DCTX + 30116)] [(SPA + 8, SPA + 16)] BI
                    ltac:(eapply munch_weaken; [| exact MUA]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia) WMA MI6
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI6.
      assert (WA6 : wapart [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; apply DJ6; [clear - Q2; lia| clear - Q3; lia| exact Hk]).
      pose proof (sinv_w m4 m6 _ SI AH MUA WMA WA6 AWA) as SI6.
      assert (STL6 : stk bsegs m6 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MUA| exact WMA| apply DJ6; [clear; lia| clear - S_DC G2 G3a G3b; lia| clear - G1 G2 G3a ATR; lia]]).
      assert (XB6 : rw_cells bsegs m6 (FF + 128) cs) by (eapply rw_cells_transport; [exact XB| exact MUA| exact WMA| rewrite XBS; apply DJ6; [clear - F3 G1 G2 G3a; lia| clear - F7; lia| clear; lia]]).
      pose proof (xs_keep_w _ m4 m6 _ XS eq_refl AH MUA WMA AWA) as XS6.
      assert (DSK6 : stk bsegs m6 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MUA| exact WMA| intros HC; specialize (DSL HC); apply DJ6; [clear - DSL G1 G2 G3a; lia| clear - D_DC HC; lia| clear - HC; lia]]).
      assert (BD6 : BDC m6 h PFX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
                        (Z_to_bv 64 PFX) (Z_to_bv 64 5) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                        xs (wupd ws H5_validateChecksum vck)).
      { split; [unfold dctx_ptrs in *; eapply rw_cells_transport; [exact PT| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia]|].
        split; [unfold dctx_h1 in *; eapply rw_cells_transport; [exact H1| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia]|].
        split; [eapply rw_cells_transport; [exact FPz| exact MUA| exact WMA| apply DJ6; unfold zfh_cells; cbn; [clear - SDA G3b| clear| clear]; lia]|].
        split; [unfold dctx_h3; exact H3|].
        split; [split; [eapply rw_cells_transport; [exact XSC| exact MUA| exact WMA| rewrite XSSZ; apply DJ6; [clear - SDA G3b| clear| clear]; lia]| exact XSSZ]|].
        split; [intros NZC; exfalso; exact (NZC KC)|].
        split; [split; [rewrite EWS; cbv beta iota delta [h5_cells h5_sizes mk_wcells wupd H5_validateChecksum]; subst vck; exact H5C| rewrite EWS; reflexivity]|].
        split. { rewrite EWS. clear - H5OK EWS. rewrite EWS in H5OK. unfold h5_frame_ok in *.
                 cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
                     H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression H5_dictID] in *. exact H5OK. }
        split; [rewrite EWS, KC; cbv beta iota delta [wnth wupd nth H5_validateChecksum Z.eqb]; subst vck; first [reflexivity | lazymatch goal with |- ?G => idtac "VCK-LEFT:" G; fail end]|].
        split; [rewrite EWS; cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_isFrameDecompression]; reflexivity|].
        split; [exists jhb, ovd, dcb, dce, (Z_to_bv 64 0); unfold dctx_tx in *; eapply rw_cells_transport; [exact TX| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia]|].
        split; [destruct OWN as [OWE OWX]; split; (eapply stk_transport_disjoint; [eassumption| exact MUA| exact WMA| apply DJ6; [clear - SDA G3b| clear| clear]; lia])|].
        eapply (tbl_frame TBL TBLL); [exact (tbl_init TBL TBLL m4 DCTX BHUF BREP)| exact MUA| exact MIh| exact MI6| intros x Hx; cbn [outside]; clear - Hx SDA G3b; repeat split; lia]. }
      clear MUA WMA.
      eapply (p_pcs m6 off sz tot hsz h PFX _ _ _ _ _ _ _ _ _ _ _ _ xs _ v16 v24 v32 v40 vfl j0 j288 cs);
        [exact BI6| exact SI6| exact STL6| exact FRA| exact XB6| exact XBS| exact XS6| exact DSK6| exact BD6| exact FOK| exact WIN| exact KA].
    - (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      dc_sh UD RDS 30108. zstep. zstep. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
      zstep. if_false.                                   (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      dc_sh UD RDS 30112. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
      zstep. rewrite (sx32w_small 0) by (clear; lia).    (* [comment removed for export] *)
      zstep. if_false.                                   (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      zstep. if_false.                                   (* [comment removed for export] *)
      zstep. zstep.                                      (* [comment removed for export] *)
      zstep.                                             (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
      lazymatch goal with MIc : mem_inv bsegs mA |- _ => rename MIc into MIA end.
      gf_unhold.
      lazymatch type of H5C with rw_cells _ _ _ (_ :: _ :: _ :: C4 ?z :: _) => pose (vck := z) end.
      (* [comment removed for export] *)
      assert (DJ6 : forall X k, (X + k <= SPA + 8 \/ SPA + 16 <= X) -> (X + k <= DCTX + 30112 \/ DCTX + 30116 <= X) -> 0 <= k ->
                disjoint_from [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)] X k)
        by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; lia).
      pose proof (binv_w m4 mA [(DCTX + 30112, DCTX + 30116)] [(SPA + 8, SPA + 16)] BI
                    ltac:(eapply munch_weaken; [| exact MUA]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia) WMA MIA
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BIA.
      assert (WA6 : wapart [(SPA + 8, SPA + 16); (DCTX + 30112, DCTX + 30116)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; apply DJ6; [clear - Q2; lia| clear - Q3; lia| exact Hk]).
      pose proof (sinv_w m4 mA _ SI AH MUA WMA WA6 AWA) as SIA.
      assert (STLA : stk bsegs mA lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MUA| exact WMA| apply DJ6; [clear; lia| clear - S_DC G2 G3a G3b; lia| clear - G1 G2 G3a ATR; lia]]).
      assert (XBA : rw_cells bsegs mA (FF + 128) cs) by (eapply rw_cells_transport; [exact XB| exact MUA| exact WMA| rewrite XBS; apply DJ6; [clear - F3 G1 G2 G3a; lia| clear - F7; lia| clear; lia]]).
      pose proof (xs_keep_w _ m4 mA _ XS eq_refl AH MUA WMA AWA) as XSA.
      assert (DSKA : stk bsegs mA DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MUA| exact WMA| intros HC; specialize (DSL HC); apply DJ6; [clear - DSL G1 G2 G3a; lia| clear - D_DC HC; lia| clear - HC; lia]]).
      ud_refresh UD0 UD MUA AWA DCr ATR.
      unfold dctx_ptrs in PT. unfold dctx_h1 in H1. unfold dctx_tx in TX. destruct OWN as [OWE OWX].
      eapply rw_cells_transport in PT; [| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia].
      eapply rw_cells_transport in H1; [| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia].
      eapply rw_cells_transport in FPz; [| exact MUA| exact WMA| apply DJ6; unfold zfh_cells; cbn; [clear - SDA G3b| clear| clear]; lia].
      eapply rw_cells_transport in XSC; [| exact MUA| exact WMA| rewrite XSSZ; apply DJ6; [clear - SDA G3b| clear| clear]; lia].
      eapply rw_cells_transport in TX; [| exact MUA| exact WMA| apply DJ6; cbn; [clear - SDA G3b| clear| clear]; lia].
      eapply stk_transport_disjoint in OWE; [| exact MUA| exact WMA| apply DJ6; [clear - SDA G3b| clear| clear]; lia].
      eapply stk_transport_disjoint in OWX; [| exact MUA| exact WMA| apply DJ6; [clear - SDA G3b| clear| clear]; lia].
      pose proof (tbl_frame TBL TBLL _ _ _ _ _ _ _ _ _ _ (tbl_init TBL TBLL m4 DCTX BHUF BREP) MUA MIh MIA
                    ltac:(intros x Hx; cbn [outside]; clear - Hx SDA G3b; repeat split; lia)) as TBA.
      pose proof BIA as (AHA & FFRA & MU0A & WM0A & _).
      assert (ARTA : art mA).
      { pose proof (AI_rtcells AI _ _ _ _ _ AHA) as (_ & A & B & C & D & E & F' & G' & _).
        unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
      assert (AHDA : ahull RNG mA DCTX 95992) by (eapply dm_ahull_wmono; [exact AH_dc| exact WM0A]).
      clear MUA WMA BI SI STL XB XS DSK AH.
      unfold zd_xxh_reset_stmtA, APZD_XXH_RESET in XXHRESET.
      eapply evtF_cut.
      { eapply (XXHRESET RNG) with (SPV := SPA) (lo := lo) (STA := DCTX + 30008) (cs0 := xs);
          first [ exact XSC | exact XSSZ | exact STLA | exact ARTA | exact MIA | reflexivity
                | lazymatch goal with
                  | |- 4096 <= _ => clear - D1; lia
                  | |- (DCTX + 30008) mod 8 = 0 => clear - DM8; Z.div_mod_to_equations; lia
                  | |- DCTX + 30008 + 88 <= 2 ^ 47 => clear - D2 AT2; lia
                  | |- lo <= SPA - _ => clear - G2 G3a; lia
                  | |- SPA < _ => clear - G3b G5; lia
                  | |- DCTX + 30008 + 88 <= lo \/ _ => clear - D2 G1; lia
                  | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact ABD| clear; lia| clear; lia] | split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear; lia]| split; [eapply rng_sub'; [exact RD| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - DM8; Z.div_mod_to_equations; lia]]]]
                  | |- ahull _ _ _ _ => eapply dm_ahull_sub; [exact AHDA| clear; lia| clear; lia]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; f_equal; lia
                  end
                | lazymatch goal with |- ?Gg => idtac "XXHRESET-LEFT:" Gg end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mB & -> & MUB & WMB & MIB & STLB & (j1 & j2 & XXB)).
      rd_retlit.
      (* [comment removed for export] *)
      assert (AWB : aappW [(DCTX + 30008, DCTX + 30008 + 88); (SPA - 2240, SPA)]).
      { pose proof (ablk_disj_band _ _ ABD) as DBD. unfold aappW, KLS, KLOW, KHIGH in *.
        apply Forall_cons; [cbn [fst snd]; clear - DBD; lia|]. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia| apply Forall_nil]. }
      assert (DJB : forall X k, (X + k <= DCTX + 30008 \/ DCTX + 30096 <= X) -> (X + k <= SPA - 2240 \/ SPA <= X) -> 0 <= k ->
                disjoint_from [(DCTX + 30008, DCTX + 30008 + 88); (SPA - 2240, SPA)] X k)
        by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; lia).
      pose proof (binv_w mA mB [(DCTX + 30008, DCTX + 30008 + 88)] [(SPA - 2240, SPA)] BIA MUB WMB MIB
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BIB.
      assert (WAB : wapart [(DCTX + 30008, DCTX + 30008 + 88); (SPA - 2240, SPA)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; apply DJB; [clear - Q3; lia| clear - Q1 G2 G3a; lia| exact Hk]).
      pose proof (sinv_w mA mB _ SIA AHA MUB WMB WAB AWB) as SIB.
      assert (FRAB := rw_cells_transport _ _ _ _ _ _ FRA MUB WMB ltac:(apply DJB; cbn; [clear - SDA G3b| clear| clear]; lia)).
      assert (XBB : rw_cells bsegs mB (FF + 128) cs) by (eapply rw_cells_transport; [exact XBA| exact MUB| exact WMB| rewrite XBS; apply DJB; [clear - F7; lia| clear - F3 G1 G2 G3a; lia| clear; lia]]).
      pose proof (xs_keep_w _ mA mB _ XSA eq_refl AHA MUB WMB AWB) as XSB.
      assert (DSKB : stk bsegs mB DST (DST + CAP)) by (eapply dsk_keep; [exact DSKA| exact MUB| exact WMB| intros HC; specialize (DSL HC); apply DJB; [clear - D_DC HC; lia| clear - DSL G1 G2 G3a; lia| clear - HC; lia]]).
      assert (BDB : BDC mB h PFX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
                        (Z_to_bv 64 PFX) (Z_to_bv 64 5) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                        (xxh_cells j1 0 j2) (wupd ws H5_validateChecksum vck)).
      { split; [unfold dctx_ptrs; eapply rw_cells_transport; [exact PT| exact MUB| exact WMB| apply DJB; cbn; [clear| clear - SDA G3b| clear]; lia]|].
        split; [unfold dctx_h1; eapply rw_cells_transport; [exact H1| exact MUB| exact WMB| apply DJB; cbn; [clear| clear - SDA G3b| clear]; lia]|].
        split; [eapply rw_cells_transport; [exact FPz| exact MUB| exact WMB| apply DJB; unfold zfh_cells; cbn; [clear| clear - SDA G3b| clear]; lia]|].
        split; [unfold dctx_h3; eapply rw_cells_transport; [exact H3| exact MUB| exact WMB| apply DJB; cbn; [clear| clear - SDA G3b| clear]; lia]|].
        split; [split; [exact XXB| reflexivity]|].
        split; [intros _; exists j1, 0, j2; split; [reflexivity| clear; lia]|].
        split; [split; [rewrite EWS; cbv beta iota delta [h5_cells h5_sizes mk_wcells wupd H5_validateChecksum]; subst vck;
                        eapply rw_cells_transport; [exact H5C| exact MUB| exact WMB| apply DJB; cbn; [clear| clear - SDA G3b| clear]; lia]| rewrite EWS; reflexivity]|].
        split. { rewrite EWS. clear - H5OK EWS. rewrite EWS in H5OK. unfold h5_frame_ok in *.
                 cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
                     H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression H5_dictID] in *. exact H5OK. }
        split; [rewrite EWS; replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC); cbv beta iota delta [wnth wupd nth H5_validateChecksum]; subst vck;
                first [reflexivity | lazymatch goal with |- ?G => idtac "VCK1-LEFT:" G; fail end]|].
        split; [rewrite EWS; cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_isFrameDecompression]; reflexivity|].
        split; [exists jhb, ovd, dcb, dce, (Z_to_bv 64 0); unfold dctx_tx; eapply rw_cells_transport; [exact TX| exact MUB| exact WMB| apply DJB; cbn; [clear| clear - S_DC G2 G3a G3b| clear]; lia]|].
        split; [split; (eapply stk_transport_disjoint; [eassumption| exact MUB| exact WMB| apply DJB; [clear| clear - S_DC G2 G3a G3b| clear]; lia])|].
        eapply (tbl_frame TBL TBLL); [exact TBA| exact MUB| exact MIA| exact MIB| intros x Hx; cbn [outside]; clear - Hx SDA G3b; repeat split; lia]. }
      fk_hold BIB. fk_hold SIB. fk_hold STLB. fk_hold XBB. fk_hold XSB. fk_hold DSKB. fk_hold BDB. fk_hold FRAB.
      clear PT H1 FPz H3 XSC TX OWE OWX H5C XXB TBA BIA SIA STLA XBA XSA DSKA AHA FFRA MU0A WM0A ARTA AHDA MUB WMB UD.
      zstep.                                             (* [comment removed for export] *)
      gf_unhold.
      eapply (p_pcs mB off sz tot hsz h PFX _ _ _ _ _ _ _ _ _ _ _ _ _ _ v16 v24 v32 v40 vfl j0 j288 cs);
        [exact BIB| exact SIB| exact STLB| exact FRAB| exact XBB| exact XBS| exact XSB| exact DSKB| exact BDB| exact FOK| exact WIN| exact KA].
  Qed.
End DM.
End CANSEC1.
