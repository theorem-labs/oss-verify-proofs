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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_block_iface AZ_blk_iface5 AZ_xxh_iface AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d AZ_dmf_e AZ_dmf_f.
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

  (* [comment removed for export] *)
  Definition BLK_OK (off sz tot hsz PFX ipb rem o cbs : Z) (bp : block_props) : Prop :=
    ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) /\
    off + hsz <= ipb /\ ipb + rem <= off + sz /\ 0 <= o <= CAP - tot /\
    get_cblock_size src ipb rem = Some (cbs, bp) /\ zd_is_error cbs = false /\ cbs <= rem - 3 /\
    (forall ip' rem' o', dblocks src (CAP - tot) ipb rem o ip' rem' o' -> dblocks src (CAP - tot) (off + hsz) (sz - hsz) 0 ip' rem' o').

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
  Lemma p_after2 : forall m off sz tot hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) (bp_cells bp) ->
    rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp -> block_result (CAP - tot - o) cbs bp v -> 0 <= v -> KA_T sz ->
    (bp_last bp = 0 -> B_HEAD off sz tot hsz h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evtF bsegs RNG POST (STpc 0x85128 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + tot + o)) (Z_to_bv 64 v)
                              (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + (ipb + 3))) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (rem + -3)) x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           BI SI STL FRA XB XS DSK BD FOK BOK BR RV KA KB.
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH). pose proof BOK as (WIN & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & CNRLE). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in R3.
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & RFCS & _ & _ & _ & RCK & _).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; clear; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    assert (RV2 : v <= CAP - tot - o).
    { unfold block_result in BR. clear - BR RCBS. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia. }
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof G_ff as (F1 & F2 & _ & F4 & _). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_src as [RSa RSb]. pose proof B_sr as [ABS _].
    assert (NZ : 0 < zlen src) by (clear - R9 RSZ ROFF NLEN; lia).
    pose proof SI as (_ & _ & _ & _ & SB & US & _). pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold KB. fk_hold FFR. fk_hold MU0. fk_hold PRES. fk_hold PRES0. fk_hold PFEND. fk_hold DBK. fk_hold WIN. fk_hold GFH. fk_hold GCB. fk_hold NSK.
    fk_hold FOK. fk_hold BOK. fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL. fk_hold SB. fk_hold US. fk_hold BR. fk_hold DBLOCK. fk_hold XXHUPD. fk_hold MEMMOVE. fk_hold MEMSET. fk_hold GETCB.
    dm_hold_sep.
    unfold DFR in FRA. unfold DSHO in XS.
    (* [comment removed for export] *)
    assert (CONT : forall (y19 : word),
      evtF bsegs RNG POST (STpc 0x8512c m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + tot + (o + v))) y19
                              (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + (ipb + 3))) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (rem + -3)) x28 x29 x30 x31)).
    { intros y19.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep.
      unfold fk_held in XB. unfold bp_cells in XB.
      zstep. rewrite sx32w_small by (clear - RBL; lia).
      fk_hold XB.
      zstep. zstep.
      replace (SRC + (ipb + 3) + cbs) with (SRC + (ipb + 3 + cbs)) by (clear; lia).
      replace (rem + -3 - cbs) with (rem - 3 - cbs) by (clear; lia).
      (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      pose proof (munch_refl [(SHF + 16, SHF + 18)] m) as MU2. pose proof (wmono_refl bsegs m) as WM2. pose proof MI as MIh. fk_hold MIh.
      zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      lazymatch goal with MIc : mem_inv bsegs m2 |- _ => rename MIc into MI2 end.
      change (rw_cells bsegs m2 SHF DSHC) in XS. rename XS into XS2. rename FRA into FRA2.
      unfold fk_held in BI, SI, STL, XB, DSK, BD, MIh.
      pose proof (binv_sh m m2 16 18 BI MU2 WM2 MI2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as BI2.
      pose proof (sinv_sh m m2 16 18 SI AH MU2 WM2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as SI2.
      assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| clear - G1 AT1; lia]]).
      assert (XB2 : rw_cells bsegs m2 (FF + 128) (bp_cells bp))
        by (unfold bp_cells; eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ F1) as X; cbn; clear - X; lia]]).
      assert (DSK2 : stk bsegs m2 DST (DST + CAP))
        by (eapply dsk_keep; [exact DSK| exact MU2| exact WM2| intros HC; eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X; lia]]).
      assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
        by (eapply bdc_w; [exact BD| exact MU2| exact WM2| exact MIh| exact MI2| eapply dm_dja; [exact AH| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 B_dc)) as X; clear - X; lia]]).
      pose proof BI2 as (AH2 & _).
      clear BI SI STL XB DSK BD MU2 WM2 MIh AH.
      fk_hold BI2. fk_hold SI2. fk_hold STL2. fk_hold XB2. fk_hold DSK2. fk_hold BD2.
      zstep. if_cases KL; zify_cond KL.
      - (* [comment removed for export] *)
        gf_unhold.
        eapply (PFEND m2 off sz tot (o + v) (ipb + 3 + cbs) (rem - 3 - cbs) h PFX); try eassumption; try reflexivity;
          try (change (2^64) with 18446744073709551616; clear - RFCS; lia);
          try (clear - RO RV RV2 RI1 RI2 KFIT R3 RCBS RSZ RHS RCK; lia).
        intros ipF remF CKC FCSC r DM.
        eapply (DM_frame src off sz (CAP - tot) tot r (o + v) ipF remF); [unfold ZD_FRAMEHEADERSIZE_PREFIX; clear - R9; lia | exact NSK | | exact DM].
        unfold dframe. split; [unfold ZD_FRAMEHEADERSIZE_MIN, ZD_blockHeaderSize; clear - R9; lia|]. cbv zeta. rewrite <- EHSZ.
        split; [unfold ZD_blockHeaderSize; clear - RH; lia|].
        exists h, (ipb + 3 + cbs), (rem - 3 - cbs). split; [exact GFH|].
        split. { apply DBK. apply (DB_last src (CAP - tot) ipb rem o cbs bp v GCB NEC); [unfold ZD_blockHeaderSize; clear - KFIT; lia | exact BR | exact KL]. }
        split; [exact FCSC|].
        destruct (fh_checksum h =? 0); [destruct CKC; split; assumption| destruct CKC as (C1 & C2 & C3); split; [exact C1|]; split; assumption].
      - (* [comment removed for export] *)
        unfold DSHC in XS2.
        pose proof (munch_refl [(SHF + 16, SHF + 18)] m2) as MU3. pose proof (wmono_refl bsegs m2) as WM3. pose proof MI2 as MI2h. fk_hold MI2h.
        zstep. zstep. zstep.                             (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        lazymatch goal with MIc : mem_inv bsegs m3 |- _ => rename MIc into MI3 end.
        change (rw_cells bsegs m3 SHF DSHO) in XS2. rename XS2 into XS3. rename FRA2 into FRA3.
        unfold fk_held in BI2, SI2, STL2, XB2, DSK2, BD2, MI2h.
        pose proof (binv_sh m2 m3 16 18 BI2 MU3 WM3 MI3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as BI3.
        pose proof (sinv_sh m2 m3 16 18 SI2 AH2 MU3 WM3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as SI3.
        assert (STL3 : stk bsegs m3 lo SPA) by (eapply stk_transport_disjoint; [exact STL2| exact MU3| exact WM3| eapply dm_dja; [exact AH2| clear; lia| clear; lia| clear; lia| clear - G1 AT1; lia]]).
        assert (XB3 : rw_cells bsegs m3 (FF + 128) (bp_cells bp))
          by (unfold bp_cells; eapply rw_cells_transport; [exact XB2| exact MU3| exact WM3| eapply dm_dja; [exact AH2| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ F1) as X; cbn; clear - X; lia]]).
        assert (DSK3 : stk bsegs m3 DST (DST + CAP))
          by (eapply dsk_keep; [exact DSK2| exact MU3| exact WM3| intros HC; eapply dm_dja; [exact AH2| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 (B_ds HC))) as X; clear - X; lia]]).
        assert (BD3 : BDC m3 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
          by (eapply bdc_w; [exact BD2| exact MU3| exact WM3| exact MI2h| exact MI3| eapply dm_dja; [exact AH2| clear; lia| clear; lia| clear; lia| pose proof (fk_ablk_lits _ _ (proj1 B_dc)) as X; clear - X; lia]]).
        pose proof BI3 as (AH3 & _).
        clear BI2 SI2 STL2 XB2 DSK2 BD2 MU3 WM3 MI2h AH2.
        fk_hold BI3. fk_hold XB3. fk_hold DSK3. fk_hold BD3.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        unfold fk_held in BI3, XB3, DSK3, BD3, GETCB.
        pose proof SI3 as (SAV3 & STG3 & XA3 & XC3 & SB3 & US3 & UD3 & UDS3 & GOT3 & ARO3 & AZS3).
        assert (ART3 : art m3) by (art_of AH3).
        assert (UB3 : unpoisoned m3 (FF + 128) (FF + 140)) by (apply dsho_unp; [rewrite <- F4; exact XS3| exact F8| exact FL| clear - F3 AT2; lia]).
        set (ip2 := ipb + 3 + cbs) in *. set (rem2 := rem - 3 - cbs) in *.
        unfold zd_getcblock_stmtA, APZD_GETCBLOCK in GETCB.
        eapply evtF_cut.
        { eapply (GETCB RNG) with (SPV := SPA) (lo := lo) (SRC := SRC) (BP := FF + 128) (src := src) (ip := ip2) (size := rem2) (cs0 := bp_cells bp);
          first [ exact SB3 | exact OK | exact XB3 | exact STL3 | exact MI3 | exact ART3 | reflexivity
                | lazymatch goal with
                  | |- 0 <= ip2 => clear - ROFF RHS RI1 RCBS; subst ip2; lia
                  | |- 0 <= rem2 => clear - KFIT R3; subst rem2; lia
                  | |- ip2 + rem2 <= _ => clear - RSZ NLEN RI2; subst ip2 rem2; lia
                  | |- 0 < SRC => clear - SL1; lia
                  | |- 0 < FF + 128 => clear - FL; lia
                  | |- (FF + 128) mod 4 = 0 => clear - F8; Z.div_mod_to_equations; lia
                  | |- lo <= SPA - _ => clear - G2 G3a; lia
                  | |- SPA < _ => clear - G3b G5; lia
                  | |- FF + 128 + 12 <= lo \/ _ => clear - F3 G1; lia
                  | |- SRC + _ <= lo \/ SPA <= SRC => clear - S_SR G3b; hlia
                  | |- areg _ _ SRC _ => intros _; split; [exact ABS| split; [exact US3| split; [exact RSa| exact RSb]]]
                  | |- areg _ _ (FF + 128) _ => intros _; split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia] | split; [replace (FF + 128 + 12) with (FF + 140) by (clear; lia); exact UB3| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| unfold shspan; rewrite F4, !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia]]]]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; subst ip2 rem2; f_equal; lia
                  end
                | lazymatch goal with |- ?Gg => idtac "GETCB-LEFT:" Gg end ]. }
        cbv beta. intros ms' PO.
        destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & cs4 & -> & MU4 & WM4 & MI4 & STL4 & XB4 & XBS4 & XBOK).
        rd_retlit.
        (* [comment removed for export] *)
        assert (AW4 : aappW [(FF + 128, FF + 128 + 12); (SPA - 16, SPA)]).
        { pose proof (ablk_disj_band _ _ F1) as FB. unfold aappW, KLS, KLOW, KHIGH in *.
          apply Forall_cons; [cbn [fst snd]; clear - FB; lia|]. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia| apply Forall_nil]. }
        assert (WA4 : wapart [(FF + 128, FF + 128 + 12); (SPA - 16, SPA)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; cbn [disjoint_from]; clear - Hk Q1 Q5 G2 G3a; repeat split; lia).
        pose proof (binv_w m3 m4 [] _ BI3 MU4 WM4 MI4 ltac:(constructor)
                      ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil]])) as BI4.
        pose proof (sinv_w m3 m4 _ SI3 AH3 MU4 WM4 WA4 AW4) as SI4.
        assert (FRA4 : BFR m4 tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384)
          by (unfold DFR; eapply rw_cells_transport; [exact FRA3| exact MU4| exact WM4| cbn; clear - F3 G1 G2 G3a; repeat split; lia]).
        pose proof (xs_keep_w _ m3 m4 _ XS3 eq_refl AH3 MU4 WM4 AW4) as XS4.
        assert (DSK4 : stk bsegs m4 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK3| exact MU4| exact WM4| intros HC; specialize (DSL HC); cbn; unfold fk_held in G_ff; pose proof G_ff as (_ & _ & _ & _ & _ & _ & _ & F8' & _); clear - DSL F8' HC G1 G2 G3a; repeat split; lia]).
        assert (BD4 : BDC m4 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws) by (eapply bdc_w; [exact BD3| exact MU4| exact WM4| exact MI3| exact MI4| unfold fk_held in G_ff; pose proof G_ff as (_ & _ & _ & _ & _ & _ & F7 & _); cbn; clear - F7 D2 G1 G2 G3a; repeat split; lia]).
        pose proof BI4 as (AH4 & _).
        clear SAV3 STG3 XA3 XC3 SB3 US3 UD3 UDS3 GOT3 ARO3 AZS3 ART3 UB3 FRA3 XS3 BI3 SI3 STL3 XB3 DSK3 BD3 MU4 WM4 MI3 AH3 AW4 WA4.
        (* [comment removed for export] *)
        assert (RRET : 0 <= cblock_ret (get_cblock_size src ip2 rem2) < 18446744073709551616).
        { clear - OK. unfold get_cblock_size.
          destruct (rem2 <? ZD_blockHeaderSize); cbn [cblock_ret].
          - unfold ZERR, ZE_srcSize_wrong. lia.
          - pose proof (cblock_props_range (le24 src ip2) (le24_range src OK ip2)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
            unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected.
            destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia. }
        unfold DFR in FRA4.
        fk_hold BI4. fk_hold SI4. fk_hold STL4. fk_hold XB4. fk_hold XS4. fk_hold DSK4. fk_hold BD4. fk_hold XBOK.
        zstep. zstep. zstep. zstep. zstep. if_cases KE; zify_cond KE.
        + (* [comment removed for export] *)
          destruct (get_cblock_size src ip2 rem2) as [[v2 bp2]|] eqn:G2c; cbn [cblock_ret] in *;
            [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; clear - KE; lia].
          unfold fk_held in XBOK, XB4. rewrite (XBOK v2 bp2 eq_refl) in XB4.
          gf_unhold. specialize (KB KL). unfold AZ_dmf_f.B_HEAD in KB.
          eapply KB; try eassumption.
          apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. clear - KE RRET. lia.
        + (* [comment removed for export] *)
          zstep.                                         (* [comment removed for export] *)
          gf_unhold.
          eapply (p_berr m4 off sz tot _ (Z_to_bv 64 (DST + CAP)) vfl j0 j384 cs4);
            [exact BI4| exact SI4| exact STL4| exact FRA4| exact XB4| exact XBS4| exact XS4| exact DSK4| exact (bdc_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BD4)
            | exact ROFF| exact RSZ| exact RT| exact RRET| | exact ACC| exact KA].
          apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. clear - KE RRET. lia. }
    fk_hold CONT.
    (* [comment removed for export] *)
    zstep. (let w := getreg 18 in replace w with (Z_to_bv 64 (DST + tot + (o + v))) by (apply Z_to_bv_eqm; f_equal; clear; lia)).
    unfold fk_held in CONT. apply CONT.
  Qed.

  (* [comment removed for export] *)
  Lemma p_after : forall m off sz tot hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384 ->
    rw_cells bsegs m (FF + 128) (bp_cells bp) ->
    rw_cells bsegs m SHF DSHO -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp -> block_result (CAP - tot - o) cbs bp v -> 0 <= v -> KA_T sz ->
    (bp_last bp = 0 -> B_HEAD off sz tot hsz h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evtF bsegs RNG POST (STpc 0x85100 m x1 x5 x6 x7 (Z_to_bv 64 (DCTX + 30112)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + tot + o)) (Z_to_bv 64 v)
                              (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + (ipb + 3))) (Z_to_bv 64 cbs) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (rem + -3)) x28 x29 x30 x31).
  Proof.
    intros m off sz tot hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
           BI SI STL FRA XB XS DSK BD FOK BOK BR RV KA KB.
    pose proof FOK as (ROFF & RSZ & RT & ACC & R9 & EHSZ & RH & NSK & GFH). pose proof BOK as (WIN & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & CNRLE). change (2^21) with 2097152 in *.
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & _ & _ & _ & _ & RCK & _).
    assert (RV2 : v <= CAP - tot - o).
    { unfold block_result in BR. clear - BR RCBS. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia. }
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof R_dc as [RD RDS]. pose proof B_dc as [ABD IBD].
    pose proof SI as (_ & _ & _ & _ & _ & _ & UD & UDS & _).
    pose proof BD as (_ & _ & _ & _ & XSC & XSI & [H5C H5L] & H5OK & K_VCK & _).
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold KB. fk_hold FFR. fk_hold MU0. fk_hold PRES. fk_hold PRES0. fk_hold PFEND. fk_hold DBK. fk_hold WIN. fk_hold GFH. fk_hold GCB. fk_hold NSK.
    fk_hold FOK. fk_hold BOK. fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL. fk_hold UDS. fk_hold BR. fk_hold DBLOCK. fk_hold XXHUPD. fk_hold MEMMOVE. fk_hold MEMSET. fk_hold GETCB. fk_hold XSC. fk_hold XSI. fk_hold H5C.
    dm_hold_sep.
    unfold DFR in FRA. unfold DSHO in XS.
    (* [comment removed for export] *)
    zstep. zstep.
    rewrite ?(Z.mod_small ((DCTX + 30112) ≫ 3 + SHB) 18446744073709551616) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - D1 D2 AT2; Z.div_mod_to_equations; lia).
    pose proof (dm_sh_rd0s m DCTX 95992 (DCTX + 30112) UD ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 AT2; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 30112) ≫ 3 + SHB) 1).
    { eapply rng_sub'; [exact RDS|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold fk_held in H5C. h5_open ws H5L. lazymatch type of K_VCK with ?x = _ => subst x end.
    assert (RV01 : 0 <= (if fh_checksum h =? 0 then 0 else 1) < 2) by (clear; destruct (fh_checksum h =? 0); lia).
    zstep. rewrite sx32w_small by (clear - RV01; lia).   (* [comment removed for export] *)
    fk_hold H5C.
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      gf_unhold. eapply (p_after2 m off sz tot hsz h PFX ipb rem o cbs bp v); try eassumption.
    - (* [comment removed for export] *)
      assert (ECK : fh_checksum h <> 0) by (intros E; rewrite E in KC; cbn in KC; clear - KC; lia).
      unfold fk_held in XSI, XSC. destruct (XSI ECK) as (j1 & msz & j2 & -> & RMSZ). destruct XSC as [XSC XSSZ].
      zstep. zstep. zstep. zstep.                      (* [comment removed for export] *)
      unfold fk_held in STL, DSK, UDS, XXHUPD, AH_dc, AH_ds.
      assert (ART : art m) by (art_of AH).
      assert (AHX : ahull RNG m (DCTX + 30008) 88) by (eapply dm_ahull_sub; [eapply dm_ahull_wmono; [exact AH_dc| exact WM0]| clear; lia| clear; lia]).
      assert (INP : ((DST + tot + o = 0 /\ Z_to_bv 64 v = Z_to_bv 64 0)
                     \/ (exists inb, bytes_at bsegs m (DST + tot + o) inb /\ Z_to_bv 64 v = Z_to_bv 64 (zlen inb) /\ 4096 <= DST + tot + o /\ DST + tot + o + zlen inb <= 2^47 /\
                         (DCTX + 30008 + 88 <= DST + tot + o \/ DST + tot + o + zlen inb <= DCTX + 30008) /\ (DST + tot + o + zlen inb <= lo \/ SPA <= DST + tot + o) /\
                         aregU RNG m (DST + tot + o) (zlen inb) /\ ahull RNG m (DST + tot + o) (zlen inb)))).
      { destruct (Z.eq_dec (DST + tot + o) 0) as [E0|E0].
        - left. split; [exact E0|]. pose proof (DNULL) as DN. unfold fk_held in DN. f_equal. clear - E0 DN D0 RT RO RV RV2. assert (DST = 0) by lia. specialize (DN H). lia.
        - right. assert (HC : 0 < CAP) by (pose proof DZ as DZ'; clear - E0 DZ' D0 RT RO RC0; assert (DST <> 0 \/ 0 < tot + o) by lia; lia).
          destruct (stk_split bsegs m DST (DST + tot + o) (DST + CAP) DSK ltac:(clear - RT RO; lia)) as [_ S2].
          destruct (stk_split bsegs m (DST + tot + o) (DST + tot + o + v) (DST + CAP) S2 ltac:(clear - RV RV2; lia)) as [S3 _].
          destruct (stk_bytes bsegs m _ _ S3 ltac:(clear - RV; lia)) as (inb & LINB & BINB).
          assert (EL : zlen inb = v) by (rewrite LINB; clear - RV; lia).
          exists inb. rewrite EL. specialize (DSL HC). destruct (B_ds HC) as [ABS' _]. destruct (R_ds HC) as [RDS1 RDS2].
          split; [exact BINB|]. split; [reflexivity|]. split; [clear - DSL RT RO; lia|]. split; [clear - DSL RT RO RV RV2 AT2; lia|].
          split; [unfold fk_held in D_DC; clear - D_DC RT RO RV RV2; lia|]. split; [unfold fk_held in S_DS; clear - S_DS RT RO RV RV2 G3b; lia|].
          split.
          + split; [eapply ablk_sub; [exact ABS'| clear - RT RO; lia| clear - RV RV2; lia]|].
            split; [eapply unpoisoned_sub; [exact (UDS HC)| clear - RT RO; lia| clear - RV RV2; lia]|].
            split; [eapply rng_sub'; [exact RDS1| clear - RT RO RV RV2; lia]|].
            eapply rng_sub'; [exact RDS2| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RT RO RV RV2; Z.div_mod_to_equations; lia].
          + eapply dm_ahull_sub; [eapply dm_ahull_wmono; [exact (AH_ds HC)| exact WM0]| clear - RT RO; lia| clear - RV RV2; lia]. }
      unfold zd_xxh_update_stmtA2, APZD_XXH_UPDATE in XXHUPD.
      eapply evtF_cut.
      { destruct INP as [[E0 EV]|(inb & BINB & EV & I1 & I2 & I3 & I4 & I5 & I6)];
          [ eapply (XXHUPD RNG) with (SPV := SPA) (lo := lo) (STA := DCTX + 30008) (IN := DST + tot + o) (inb := []) (msz := msz)
          | eapply (XXHUPD RNG) with (SPV := SPA) (lo := lo) (STA := DCTX + 30008) (IN := DST + tot + o) (inb := inb) (msz := msz) ];
          first [ exact RMSZ | exact RD8 | exact STL | exact ART | exact MI | exact AHX | reflexivity
                | lazymatch goal with
                  | |- xxh_state _ _ _ => exists j1, j2; exact XSC
                  | |- 4096 <= DCTX + _ => clear - D1; lia
                  | |- 4096 <= lo => clear - G1 AT1; lia
                  | |- (DCTX + 30008) mod 8 = 0 => clear - RD8; Z.div_mod_to_equations; lia
                  | |- DCTX + 30008 + 88 <= 2^47 => clear - D2 AT2; lia
                  | |- lo <= SPA - _ => clear - G2 G3a; lia
                  | |- SPA < _ => clear - G3b G5; lia
                  | |- DCTX + 30008 + 88 <= lo \/ _ => clear - D2 G1; lia
                  | |- _ \/ _ => first [left; split; [exact E0| exact EV] | right; split; [exact BINB| split; [exact EV| split; [exact I1| split; [exact I2| split; [exact I3| split; [exact I4| split; [exact I5| exact I6]]]]]]]]
                  | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact ABD| clear; lia| clear; lia]| split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear; lia]| split; [eapply rng_sub'; [exact RD| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; lia]]]]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]
                  end
                | lazymatch goal with |- ?Gg => idtac "XXHUPD-LEFT:" Gg end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & msz' & -> & MU2 & WM2 & MI2 & STL2 & XST2 & RMSZ2).
      rd_retlit.
      (* [comment removed for export] *)
      unfold fk_held in BI, SI, XB, BD.
      assert (AW2 : aappW [(DCTX + 30008, DCTX + 30008 + 88); (SPA - 2352, SPA)]).
      { pose proof (ablk_disj_band _ _ ABD) as DBD. unfold aappW, KLS, KLOW, KHIGH in *.
        apply Forall_cons; [cbn [fst snd]; clear - DBD; lia|]. apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia| apply Forall_nil]. }
      assert (WA2 : wapart [(DCTX + 30008, DCTX + 30008 + 88); (SPA - 2352, SPA)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; cbn [disjoint_from]; clear - Hk Q1 Q3 G2 G3a; repeat split; lia).
      pose proof (binv_w m m2 [(DCTX + 30008, DCTX + 30008 + 88)] [(SPA - 2352, SPA)] BI MU2 WM2 MI2
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]) ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI2.
      pose proof (sinv_w m m2 _ SI AH MU2 WM2 WA2 AW2) as SI2.
      assert (FRA2 : BFR m2 tot (Z_to_bv 64 (DST + CAP)) vfl j0 j384) by (unfold DFR; eapply rw_cells_transport; [exact FRA| exact MU2| exact WM2| cbn; clear - D2 G1 G2 G3a; repeat split; lia]).
      assert (XB2 : rw_cells bsegs m2 (FF + 128) (bp_cells bp)) by (unfold bp_cells; eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| unfold fk_held in G_ff; pose proof G_ff as (_ & _ & _ & _ & _ & _ & F7 & _); cbn; clear - F7 F3 G1 G2 G3a; repeat split; lia]).
      pose proof (xs_keep_w _ m m2 _ XS eq_refl AH MU2 WM2 AW2) as XS2.
      assert (DSK2 : stk bsegs m2 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MU2| exact WM2| intros HC; specialize (DSL HC); unfold fk_held in D_DC; cbn; clear - D_DC DSL HC G1 G2 G3a; repeat split; lia]).
      destruct XST2 as (j1' & j2' & XSC2).
      lazymatch type of BD with AZ_dmf_f.BDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?wsx =>
        assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe (xxh_cells j1' msz' j2') wsx) end.
      { eapply bdc_w2; [exact BD| exact MU2| exact WM2| exact MI| exact MI2| cbn; clear - G1 G2 G3a D2; repeat split; lia| cbn; clear - G1 G2 G3a D2; repeat split; lia| split; [exact XSC2| reflexivity]| intros _; exists j1', msz', j2'; split; [reflexivity| exact RMSZ2]]. }
      clear BI SI STL XB XS DSK BD FRA MU2 WM2 MI AH ART AHX INP XSC UD UDS.
      (* [comment removed for export] *)
      unfold DFR in FRA2.
      fk_hold BI2. fk_hold SI2. fk_hold STL2. fk_hold XB2. fk_hold XS2. fk_hold DSK2. fk_hold BD2.
      gf_unhold. eapply (p_after2 m2 off sz tot hsz h PFX ipb rem o cbs bp v); try eassumption.
  Qed.
End DM.
End CANSEC1.
