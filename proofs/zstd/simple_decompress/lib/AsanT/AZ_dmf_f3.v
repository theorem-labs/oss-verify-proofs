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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_block_iface AZ_blk_iface5 AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d AZ_dmf_e AZ_dmf_f.
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
  Notation BINV := (AZ_dmf_f.BINV AI L RNG st LB m0 SPV DCTX DST CAP FF).
  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 SHF) x22 (Z_to_bv 64 SHB) x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation DFR := (AZ_dmf_f.DFR DCTX DST FF).
  Notation DINV := (AZ_dmf_f.DINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG).
  (* [comment removed for export] *)
  Notation AINV := (AZ_dmf_f.AINV AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Notation LHst mm off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 :=
    (STpc 0x84a88 mm x1 (Z_to_bv 64 8) (Z_to_bv 64 (-120)) x7 x10 (Z_to_bv 64 5) x12 x13 x14 (Z_to_bv 64 25481893) (Z_to_bv 64 1) (Z_to_bv 64 4)
          (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31).

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

  Notation SINV := (AZ_dmf_f.SINV RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF FLG).
  Notation BDC := (AZ_dmf_f.BDC DCTX TBL).
  Notation FRAME_OK := (AZ_dmf_f.FRAME_OK CAP src size).
  Notation KA_T := (AZ_dmf_f.KA_T AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Notation dm_geom := (AZ_dmf_f.dm_geom AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).

  (* [comment removed for export] *)
  Hypothesis PGCB : forall m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384) ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (STpc 0x84fb8 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation PCSst mm off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 :=
    (STpc 0x84f70 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
          (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Ltac dc_sh UD RDS k :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (dm_sh_rd0s mm DCTX 95992 (DCTX + k) UD ltac:(clear; lia)
                  ltac:(match goal with D2 : DCTX mod 8 = 0 |- _ => clear - D2; Z.div_mod_to_equations; lia end)
                  ltac:(match goal with DCr : 6443008 <= DCTX /\ _ |- _ => clear - DCr; lia end)
                  ltac:(match goal with DCr : 6443008 <= DCTX /\ _, ATR : (_ <= ATOP <= _) |- _ => clear - DCr ATR; lia end)) as RDz;
    assert (RTz : rng RNG ((DCTX + k) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RDS|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; match goal with D2 : DCTX mod 8 = 0 |- _ => clear - D2; Z.div_mod_to_equations; lia end)
    end.

  (* [comment removed for export] *)
  Lemma p_pcs : forall m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384) ->
    rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) ->
    BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (PCSst m off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD FOK WIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & (LL1 & LL2 & FLF & FLD & FLS)).
    assert (DCr : 6443008 <= DCTX /\ DCTX + 95992 <= ATOP) by (clear - D1 D2; lia).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof R_dc as [RD RDS].
    pose proof RD8 as DM8.
    pose proof SI as (SAV & STG & (ja & XA) & (jc & XC) & SB & US & UD & UDS & GOT & ARO & AZS).
    pose proof BD as (PT & H1 & FP & H3 & XSC & XSK & H5 & H5OK & KVC & ISF & TX & OWN & TB).
    destruct H5 as [H5C H5L]. pose proof H5OK as (_ & _ & _ & K_MBS & _).
    destruct (h5_split44 ws H5L) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21
                                     & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & EWS).
    rewrite EWS in H5C, K_MBS.
    cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_maxBlockSizeParam] in H5C, K_MBS. unfold wz0 in K_MBS. subst w23.
    unfold DFR in FRA.
    fk_hold KA. fk_hold WIN. fk_hold PGCB. fk_hold FFR. fk_hold MU0. fk_hold EWS. fk_hold FOK. fk_hold H5OK. fk_hold XSK. fk_hold KVC. fk_hold ISF.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL. fk_hold LBH. fk_hold RFS. fk_hold RSTKT.
    fk_hold SAV. fk_hold STG. fk_hold XA. fk_hold XC. fk_hold SB. fk_hold US. fk_hold UDS. fk_hold GOT. fk_hold ARO. fk_hold AZS. fk_hold XB. fk_hold XS. fk_hold DSK. fk_hold STL.
    fk_hold PT. fk_hold H1. fk_hold FP. fk_hold H3. fk_hold XSC. fk_hold TX. fk_hold OWN. fk_hold TB. fk_hold SI. fk_hold BI. fk_hold BD.
    fk_hold FLF. fk_hold FLD. fk_hold FLS. fk_hold A4. fk_hold A5.
    dm_hold_sep.
    zstep.
    dc_sh UD RDS 30232. zstep. zstep. zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep.
    zstep. if_false.
    zstep. rewrite (sx32w_small 0) by (clear; lia).
    zstep. if_true.
    gf_unhold.
    eapply (PGCB m off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs);
      [exact BI| exact SI| exact STL| exact FRA| exact XB| exact XBS| exact XS| exact DSK| exact BD| exact FOK| exact WIN| exact KA].
  Qed.
End DM.
End CANSEC1.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
