(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit MemRange ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_block_iface AZ_blk_iface5 AZ_xxh_iface AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d AZ_dmf_e AZ_dmf_f AZ_dmf_h.
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
    fk_hold DNULL; fk_hold DNN; fk_hold B_ds; fk_hold R_ds; fk_hold B_sr; fk_hold B_dc; fk_hold G_ff; fk_hold G_flg.  (* [comment removed for export] *)
  Hypothesis PRES : forall m1 off sz tot res (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x20 = Z_to_bv 64 sz' /\ x26 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (STpc 0x84ee4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 res) x20 (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
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

  Notation SINV := (AZ_dmf_f.SINV RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF FLG).
  Notation wapart := (AZ_dmf_f.wapart SPA lo DCTX DST CAP FF).
  Notation BDC := (AZ_dmf_f.BDC DCTX TBL).
  Notation FRAME_OK := (AZ_dmf_f.FRAME_OK CAP src size).
  Notation KA_T := (AZ_dmf_f.KA_T AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Notation BFR mm tot v32 vfl j0 j384 :=
    (rw_cells bsegs mm SPA (DFR (Z_to_bv 64 FF) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384)).
  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Notation dm_geom := (AZ_dmf_f.dm_geom AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation dinv_of := (AZ_dmf_f.dinv_of AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG G_flg FFLAG).
  Notation sinv_w := (AZ_dmf_f.sinv_w AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST S_DC S_DS S_SR S_GT D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation binv_w := (AZ_dmf_f.binv_w AI fflag L RNG st LB m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds LBH FHL).
  Notation bdc_any := (AZ_dmf_f.bdc_any DCTX TBL).
  Notation bdc_w := (AZ_dmf_f.bdc_w DCTX TBL TBLL).
  Notation xs_keep_w := (AZ_dmf_f.xs_keep_w AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation dsk_keep := (AZ_dmf_f.dsk_keep DST CAP RC0).

  Notation binv_sh := (AZ_dmf_f.binv_sh AI fflag L RNG st LB m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds LBH FHL).
  Notation sinv_sh := (AZ_dmf_f.sinv_sh AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation binv_F := (AZ_dmf_f.binv_F AI fflag L RNG st LB m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation sinv_F := (AZ_dmf_f.sinv_F AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST S_SR S_GT D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation dm_inblk := (AZ_dmf_f.dm_inblk LB DCTX DST CAP SRC src B_dc B_sr B_ds).
  Notation dm_inblk_sub := (AZ_dmf_f.dm_inblk_sub).
  Notation bdc_w2 := (AZ_dmf_f.bdc_w2 DCTX TBL TBLL).
  Notation dm_dja := (AZ_dmf_f.dm_dja AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation frame_keep_F := (AZ_dmf_f.frame_keep_F AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation xs_keep_F := (AZ_dmf_f.xs_keep_F L LB DCTX DST CAP SRC src FF SHF G_ff).
  Notation xb_keep_F := (AZ_dmf_f.xb_keep_F LB FF).
  Notation dsk_keep_F := (AZ_dmf_f.dsk_keep_F AI L RNG st LB DCTX DST CAP SRC src FF RC0 B_dc B_sr B_ds FHL).
  Notation B_HEAD := (AZ_dmf_f.B_HEAD AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG TBL).
  Notation p_berr := (AZ_dmf_f.p_berr AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG RD0 RC0 DNULL DNN RDST S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds R_src R_dc R_ds R_ff LBH PRES0 FHL FFLAG SPT RSTKT AH_dc AH_sr AH_ds).
  Hypothesis GETCB : zd_getcblock_stmtA.
  Hypothesis DZ : CAP = 0 -> DST = 0.
  Hypothesis DBLOCK : zd_dblock_stmtA AI rng_fs TBL.
  Hypothesis XXHUPD : zd_xxh_update_stmtA2.
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
  Hypothesis MEMSET : zd_memsetZ_stmtA.

  (* [comment removed for export] *)
  Hypothesis PFEND : forall m off sz tot res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v32 vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x22 x24 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot v32 vfl j0 j384 -> rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat ->
    rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 -> 0 <= fh_fcs h < 2^64 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        (fh_fcs h <> ZD_CONTENTSIZE_UNKNOWN -> res = fh_fcs h) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evtF bsegs RNG POST (STpc 0x851cc m x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 (SRC + ipE)) x16 x17 (Z_to_bv 64 (DST + tot + res)) (Z_to_bv 64 remE) (Z_to_bv 64 sz)
                              x22 x24 (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  Notation BLK_OK := (AZ_dmf_h.BLK_OK DST CAP src).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac keep_byte_facts := repeat match goal with H : ?T |- _ => lazymatch T with (0 <= Znth _ _ < 256)%Z => fail | _ => clear H end end.
  Ltac lor2add_sideF := keep_byte_facts; first [ lia | split; lia | Z.div_mod_to_equations; lia ].
  Ltac lor2add1F x y :=
    first [ rewrite (lor_add_disj 8 x y) by lor2add_sideF | rewrite (lor_add_disj 16 x y) by lor2add_sideF
          | rewrite (lor_add_disj 24 x y) by lor2add_sideF | rewrite (lor_add_disj 32 x y) by lor2add_sideF
          | rewrite (lor_add_disj 40 x y) by lor2add_sideF | rewrite (lor_add_disj 48 x y) by lor2add_sideF
          | rewrite (lor_add_disj 56 x y) by lor2add_sideF ].
  Ltac lor2addF := match goal with |- context [Z.lor ?x ?y] => first [ lor2add1F x y | rewrite (Z.lor_comm x y); lor2add1F y x ] end.
  Ltac clear_hyps := repeat match goal with H : _ |- _ => clear H end.
  Ltac shl2mulF :=
    repeat match goal with
    | |- context [Z.shiftl ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftl_mul_pow2 x k) by (clear_hyps; lia);
          let v := eval vm_compute in (2^k) in change (2^k) with v
    end.
  Ltac zlbF SB OK IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        first [ assert (0 <= Znth i src < 256) by assumption | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
        zstep; cbv beta; rewrite (byte_lit8 (Znth i src)) by assumption; clear RD; shl2mulF; repeat lor2addF
    end.
  Ltac zsF := zstep; shl2mulF; repeat lor2addF.
  Ltac dm_hold_all :=
    repeat match goal with
    | H : rw_cells bsegs _ _ _ |- _ => fk_hold H
    | H : stk bsegs _ _ _ |- _ => fk_hold H
    | H : BINV _ |- _ => fk_hold H
    | H : DINV _ _ |- _ => fk_hold H
    | H : AINV _ _ _ _ |- _ => fk_hold H
    | H : unpoisoned _ DCTX _ |- _ => fk_hold H
    | H : unpoisoned _ DST _ |- _ => fk_hold H
    | H : aro_client _ _ |- _ => fk_hold H
    | H : dctx_any _ _ |- _ => fk_hold H
    | H : _ \/ _ |- _ => fk_hold H
    | H : _ -> _ |- _ => lazymatch type of H with fk_held _ => fail | _ => fk_hold H end
    | H : exists _, _ |- _ => fk_hold H
    end.
  (* [comment removed for export] *)
  Ltac dm_src_run SL off p k STOP :=
    gf_unhold; dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].
  Ltac dm_src_run0 SL off k STOP :=
    gf_unhold; dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off) k; KAApp (SRC + off) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].

  (* [comment removed for export] *)
  Ltac dm_hold_more :=
    repeat match goal with
    | H : AZ_dmf_f.SINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.BDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.KA_T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.FRAME_OK _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : BLK_OK _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.B_HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    end.
  Ltac art_of AH :=
    let X := fresh "ARTX" in pose proof (AI_rtcells AI _ _ _ _ _ AH) as X;
    destruct X as (_ & Xa & Xb & Xc & Xd & Xe & Xf & Xg & _);
    unfold art; split; [exact Xa|]; split; [exact Xb|]; split; [exact Xd|]; split; [exact Xf|]; split; [exact Xg| exact Xc].

  Ltac nrm_not_by tac := match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by tac end.

  (* [comment removed for export] *)
  Hypothesis PAFTER : forall m off sz tot hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) (bp_cells bp) ->
    rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp -> block_result (CAP - tot - o) cbs bp v -> 0 <= v -> KA_T sz ->
    (bp_last bp = 0 -> B_HEAD off sz tot hsz h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evtF bsegs RNG POST (STpc 0x85100 m x1 x5 x6 x7 (Z_to_bv 64 (DCTX + 30112)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + tot + o)) (Z_to_bv 64 v)
                              (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + (ipb + 3))) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (rem + -3)) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation DSPst pc mm off sz tot ipb rem o cbs bp rm x1 x5 x6 x7 x10 x12 x14 x16 x17 x19 x28 x29 x30 x31 :=
    (STpc pc mm x1 x5 x6 x7 x10 (Z_to_bv 64 (bp_type bp)) x12 (Z_to_bv 64 (FF + 128)) x14 (Z_to_bv 64 (DST + tot + o + rm)) x16 x17
          (Z_to_bv 64 (DST + tot + o)) x19 (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + (ipb + 3))) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (rem + -3)) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_raw : forall m off sz tot hsz h PFX ipb rem o cbs bp rm llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
      (x1 x5 x6 x7 x10 x12 x14 x16 x17 x19 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) (bp_cells bp) ->
    rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp -> bp_type bp = bt_raw -> KA_T sz ->
    (forall v, block_result (CAP - tot - o) cbs bp v -> 0 <= v -> bp_last bp = 0 -> B_HEAD off sz tot hsz h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evtF bsegs RNG POST (DSPst 0x85058 m off sz tot ipb rem o cbs bp rm x1 x5 x6 x7 x10 x12 x14 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX ipb rem o cbs bp rm llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
           x1 x5 x6 x7 x10 x12 x14 x16 x17 x19 x28 x29 x30 x31
           BI SI STL FRA XB XS DSK BD FOK BOK TRAW KA KB.
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH). pose proof BOK as (WIN & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & CNRLE). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in R3.
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; clear; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof R_src as [RSa RSb]. pose proof B_sr as [ABS _].
    assert (NZ : 0 < zlen src) by (clear - R9 RSZ ROFF NLEN; lia).
    pose proof SI as (_ & _ & _ & _ & SB & US & UD & UDS & _). pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    (* [comment removed for export] *)
    assert (ERR : forall code (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y26 y27 y28 y29 y30 y31 : word), 0 < code < ZE_maxCode ->
      evtF bsegs RNG POST (STpc 0x851a8 m y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 (ZERR code)) y20 y22 y24 (Z_to_bv 64 (-72)) y26 y27 y28 y29 y30 y31)).
    { intros code y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y26 y27 y28 y29 y30 y31 RCODE.
      eapply (p_berr m off sz tot (ZERR code) (Z_to_bv 64 (DST + CAP)) vfl j0 j384 (bp_cells bp));
        [exact BI| exact SI| exact STL| exact FRA| exact XB| reflexivity| exact XS| exact DSK| exact (bdc_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BD)
        | exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_maxCode in *; clear - RCODE; lia| apply zd_is_error_ZERR; exact RCODE| exact ACC| exact KA]. }
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold KB. fk_hold FFR. fk_hold MU0. fk_hold PRES. fk_hold PRES0. fk_hold PFEND. fk_hold PAFTER. fk_hold DBK. fk_hold WIN. fk_hold GFH. fk_hold GCB. fk_hold NSK.
    fk_hold FOK. fk_hold BOK. fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL. fk_hold SB. fk_hold US. fk_hold UD. fk_hold UDS. fk_hold DBLOCK. fk_hold XXHUPD. fk_hold MEMMOVE. fk_hold MEMSET. fk_hold GETCB. fk_hold ERR.
    dm_hold_sep.
    unfold DFR in FRA. unfold DSHO in XS.
    zstep. zstep.                                      (* [comment removed for export] *)
    replace (DST + CAP - (DST + tot + o)) with (CAP - tot - o) by (clear; lia).
    zstep. zstep. if_cases KR; zify_cond KR.           (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (ZERR ZE_dstSize_tooSmall)) by (apply Z_to_bv_eqm; reflexivity).
      gf_unhold. apply ERR. unfold ZE_dstSize_tooSmall, ZE_maxCode. clear; lia.
    - zstep. if_cases KN; zify_cond KN.                (* [comment removed for export] *)
      + (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ.              (* [comment removed for export] *)
        * zstep. zstep.
          replace (Z_to_bv 64 (-74)) with (Z_to_bv 64 (ZERR ZE_dstBuffer_null)) by (apply Z_to_bv_eqm; reflexivity).
          gf_unhold. apply ERR. unfold ZE_dstBuffer_null, ZE_maxCode. clear; lia.
        * zstep.                                         (* [comment removed for export] *)
          gf_unhold. eapply (PAFTER m off sz tot hsz h PFX ipb rem o cbs bp 0); try eassumption.
          -- unfold block_result. rewrite TRAW. cbn. clear - KZ KR RCBS; lia.
          -- clear; lia.
          -- intros KL. apply (KB 0); [unfold block_result; rewrite TRAW; cbn; clear - KZ KR RCBS; lia | clear; lia | exact KL].
      + (* [comment removed for export] *)
        assert (HC : 0 < CAP) by (pose proof DZ as DZ'; unfold fk_held in DZ'; clear - KN DZ' D0 RT RO RC0; assert (DST <> 0 \/ 0 < tot + o) by lia; lia).
        unfold fk_held in DSK, STL, SB, US, UDS, MEMMOVE, AH_sr, AH_ds, DSL. specialize (DSL HC). destruct (B_ds HC) as [ABS' _]. destruct (R_ds HC) as [RDS1 RDS2].
        destruct (stk_split bsegs m DST (DST + tot + o) (DST + CAP) DSK ltac:(clear - RT RO; lia)) as [SK1 SK23].
        destruct (stk_split bsegs m (DST + tot + o) (DST + tot + o + cbs) (DST + CAP) SK23 ltac:(clear - KR RCBS; lia)) as [SK2 SK3].
        clear DSK SK23.
        assert (RDSR : rdbl bsegs m (SRC + (ipb + 3)) (SRC + (ipb + 3) + cbs)).
        { eapply rdbl_sub; [apply (rdbl_of_bytes_at bsegs _ _ _ SB) | clear - RI1 ROFF RHS; lia | rewrite length_map; clear - KFIT RI2 RSZ NLEN; lia]. }
        assert (ART : art m) by (art_of AH).
        fk_hold SK1. fk_hold SK3.
        zstep. zstep. zstep. zstep.                    (* [comment removed for export] *)
        unfold zd_memmoveZ_stmtA in MEMMOVE.
        eapply evtF_cut.
        { eapply (MEMMOVE RNG (DST + tot + o) (SRC + (ipb + 3)) cbs SPA) with (lo := lo);
            first [ exact SK2 | exact RDSR | exact STL | exact ART | exact MI | reflexivity
                  | lazymatch goal with
                    | |- 0 <= cbs <= _ => clear - RCBS; lia
                    | |- lo <= SPA - _ => clear - G2 G3a; lia
                    | |- SPA < _ => clear - G3b G5; lia
                    | |- SRC + _ + cbs <= SPA - _ \/ SPA <= SRC + _ => unfold fk_held in S_SR; clear - S_SR G2 G3a G3b KFIT RI1 RI2 RSZ NLEN ROFF RHS; lia
                    | |- DST + tot + o + cbs <= lo \/ SPA <= DST + tot + o => unfold fk_held in S_DS; clear - S_DS G3b RT RO KR RCBS; lia
                    | |- app_blk (SRC + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS| clear - RI1 ROFF RHS; lia| clear - KFIT RI2 RSZ NLEN; lia]| clear - RCBS; lia]
                    | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS'| clear - RT RO; lia| clear - KR RCBS; lia]| clear - RCBS; lia]
                    | |- aro _ _ (SRC + _) _ => split; [eapply unpoisoned_sub; [exact US| clear - RI1 ROFF RHS; lia| clear - KFIT RI2 RSZ NLEN; lia]| split; [eapply rng_sub'; [exact RSa| clear - RI1 ROFF RHS KFIT RI2 RSZ NLEN; lia]| eapply rng_sub'; [exact RSb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RI1 ROFF RHS KFIT RI2 RSZ NLEN RCBS; Z.div_mod_to_equations; lia]]]
                    | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact (UDS HC)| clear - RT RO; lia| clear - KR RCBS; lia]| split; [eapply rng_sub'; [exact RDS1| clear - RT RO KR RCBS; lia]| eapply rng_sub'; [exact RDS2| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RT RO KR RCBS; Z.div_mod_to_equations; lia]]]
                    | |- ahull _ _ (SRC + _) _ => eapply dm_ahull_sub; [eapply dm_ahull_wmono; [exact (AH_sr NZ)| exact WM0]| clear - RI1 ROFF RHS; lia| clear - KFIT RI2 RSZ NLEN; lia]
                    | |- ahull _ _ _ _ => eapply dm_ahull_sub; [eapply dm_ahull_wmono; [exact (AH_ds HC)| exact WM0]| clear - RT RO; lia| clear - KR RCBS; lia]
                    | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]
                    end
                  | lazymatch goal with |- ?Gg => idtac "MEMMOVE-LEFT:" Gg end ]. }
        cbv beta. intros ms' PO.
        destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & -> & MU2 & WM2 & MI2 & STL2 & SK22).
        rd_retlit.
        (* [comment removed for export] *)
        unfold fk_held in BI, SI, XB, BD, SK1, SK3.
        pose proof (ablk_disj_band _ _ ABS') as DBS.
        assert (AW2 : aappW [(SPA - 2224, SPA); (DST + tot + o, DST + tot + o + cbs)]).
        { unfold aappW, KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBS RT RO KR RCBS; lia| apply Forall_nil]. }
        assert (WA2 : wapart [(SPA - 2224, SPA); (DST + tot + o, DST + tot + o + cbs)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; specialize (Q4 HC); cbn [disjoint_from]; clear - Hk Q1 Q4 G2 G3a RT RO KR RCBS; repeat split; lia).
        assert (MU2' : munch ([(DST + tot + o, DST + tot + o + cbs)] ++ [(SPA - 2224, SPA)]) m m2)
          by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; repeat split; lia).
        pose proof (binv_w m m2 _ _ BI MU2' WM2 MI2
                      ltac:(apply Forall_cons; [cbn [fst snd]; clear - HC RT RO KR RCBS; lia| apply Forall_nil]) ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI2.
        pose proof (sinv_w m m2 _ SI AH MU2 WM2 WA2 AW2) as SI2.
        assert (FRA2 : BFR m2 tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384) by (unfold DFR; eapply rw_cells_transport; [exact FRA| exact MU2| exact WM2| cbn; clear - DSL G1 G2 G3a RT RO KR RCBS; repeat split; lia]).
        assert (XB2 : rw_cells bsegs m2 (FF + 128) (bp_cells bp)) by (unfold bp_cells; eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| unfold fk_held in G_ff; pose proof G_ff as (_ & _ & _ & _ & _ & _ & _ & F8' & _); cbn; clear - F8' F3 G1 G2 G3a RT RO KR RCBS; repeat split; lia]).
        pose proof (xs_keep_w _ m m2 _ XS eq_refl AH MU2 WM2 AW2) as XS2.
        assert (SK12 : stk bsegs m2 DST (DST + tot + o)) by (eapply stk_transport_disjoint; [exact SK1| exact MU2| exact WM2| cbn; clear - DSL G1 G2 G3a RT RO; repeat split; lia]).
        assert (SK32 : stk bsegs m2 (DST + tot + o + cbs) (DST + CAP)) by (eapply stk_transport_disjoint; [exact SK3| exact MU2| exact WM2| cbn; clear - DSL G1 G2 G3a RT RO KR RCBS; repeat split; lia]).
        assert (DSK2 : stk bsegs m2 DST (DST + CAP)).
        { eapply stk_merge; [eapply stk_merge; [exact SK12 | exact SK22 | clear - RT RO RCBS; lia] | exact SK32 | clear - RT RO KR RCBS; lia]. }
        assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws) by (eapply bdc_w; [exact BD| exact MU2| exact WM2| exact MI| exact MI2| unfold fk_held in D_DC; cbn; clear - D_DC D2 G1 G2 G3a RT RO KR RCBS; repeat split; lia]).
        clear BI SI STL XB XS BD FRA MU2 MU2' WM2 MI AH ART SK1 SK3 SK12 SK22 SK32 RDSR.
        fk_hold BI2. fk_hold SI2. fk_hold STL2. fk_hold XB2. fk_hold DSK2. fk_hold BD2. fk_hold XS2.
        unfold DFR in FRA2.
        zstep. zstep. zstep.                           (* [comment removed for export] *)
        gf_unhold.
        eapply (PAFTER m2 off sz tot hsz h PFX ipb rem o cbs bp cbs); try eassumption.
        -- unfold block_result. rewrite TRAW. cbn. clear - KR RCBS; lia.
        -- clear - RCBS; lia.
        -- intros KL. apply (KB cbs); [unfold block_result; rewrite TRAW; cbn; clear - KR RCBS; lia | clear - RCBS; lia | exact KL].
  Qed.

End DM.
End CANSEC1.
