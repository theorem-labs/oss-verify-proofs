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

Lemma dm_h5_vck : forall ws v, length ws = 44%nat -> h5_frame_ok ws ->
  h5_frame_ok (wupd ws H5_validateChecksum v) /\ wnth (wupd ws H5_validateChecksum v) H5_validateChecksum = v
  /\ wnth (wupd ws H5_validateChecksum v) H5_isFrameDecompression = wnth ws H5_isFrameDecompression.
Proof.
  intros ws v L OK. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [| discriminate L].
  unfold h5_frame_ok in *.
  cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
      H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression] in *.
  split; [exact OK| split; reflexivity].
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
  Hypothesis DECODEFH : zd_decodefh_stmtA AI rng_fs.

  Notation SINV := (AZ_dmf_f.SINV RNG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF FLG).
  Notation wapart := (AZ_dmf_f.wapart SPA lo DCTX DST CAP FF).
  Notation BDC0 := (AZ_dmf_e.BDC0 DCTX).
  Notation BDC := (AZ_dmf_f.BDC DCTX TBL).
  Notation FRAME_OK := (AZ_dmf_f.FRAME_OK CAP src size).
  Notation KA_T := (AZ_dmf_f.KA_T AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP SRC src size FF SHF FLG).
  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Notation dm_geom := (AZ_dmf_f.dm_geom AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation dinv_of := (AZ_dmf_f.dinv_of AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG G_flg FFLAG).
  Notation sinv_of_dinv := (AZ_dmf_f.sinv_of_dinv AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG).
  Notation dm_inblk := (AZ_dmf_f.dm_inblk LB DCTX DST CAP SRC src B_dc B_sr B_ds).
  Notation dm_inblk_sub := (AZ_dmf_f.dm_inblk_sub).
  Notation sinv_F := (AZ_dmf_f.sinv_F AI fflag L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST S_SR S_GT D_SR SR_DC GT_DC GT_DS G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation binv_F := (AZ_dmf_f.binv_F AI fflag L RNG st LB m0 SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation frame_keep_F := (AZ_dmf_f.frame_keep_F AI fflag L RNG st LB SPV SPA lo DCTX DST CAP SRC src FF SHF FLG DNN RDST G_lo G_ff G_flg B_dc B_sr B_ds FHL).
  Notation xs_keep_F := (AZ_dmf_f.xs_keep_F L LB DCTX DST CAP SRC src FF SHF G_ff).
  Notation xb_keep_F := (AZ_dmf_f.xb_keep_F LB FF).
  Notation dsk_keep_F := (AZ_dmf_f.dsk_keep_F AI L RNG st LB DCTX DST CAP SRC src FF RC0 B_dc B_sr B_ds FHL).

  (* [comment removed for export] *)
  Notation PCSst mm off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 :=
    (STpc 0x84f70 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
          (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Hypothesis PPCS : forall m4 off sz tot hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v8 v16 v24 v32 vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    BINV m4 -> SINV m4 -> stk bsegs m4 lo SPA -> rw_cells bsegs m4 SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot)) j0 j384) ->
    rw_cells bsegs m4 (FF + 128) cs -> cells_size cs = 12%nat -> rw_cells bsegs m4 SHF DSHC -> stk bsegs m4 DST (DST + CAP) ->
    BDC m4 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot hsz h -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evtF bsegs RNG POST (PCSst m4 off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation GFHst mm off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 :=
    (STpc 0x84f58 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
          (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_gfh : forall m3 off sz tot hsz PFX fp xs ws jhb ovd dcb dce (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    DINV m3 tot -> BDC0 m3 PFX fp xs ws jhb ovd dcb dce -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    9 <= sz -> hsz = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX -> hsz + 3 <= sz -> is_skippable_magic (le32 src off) = false ->
    KA_T sz ->
    evtF bsegs RNG POST (GFHst m3 off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros m3 off sz tot hsz PFX fp xs ws jhb ovd dcb dce x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
           DI3 BD WIN ROFF RSZ RT ACC R9 EHSZ RH NSK KA.
    pose proof DI3 as (BI3 & SAV3 & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA3) & STL3 & STG3 & (ja & XA3) & (jb & XB3) & (jc & XC3) & XL3 & XS3 & SB3 & US3 & UD3 & UDS3 & DSK3 & GOT3 & ARO3 & DA3 & AZS3).
    pose proof (sinv_of_dinv _ _ DI3) as SI3. clear DA3 XL3 GOT3 AZS3 SAV3 STG3 XA3 XC3 DI3.
    pose proof BI3 as (AH3 & FFR3 & MU03 & WM03 & MI3).
    pose proof BD as (PT3 & H13 & FP3 & H33 & XSC3 & H53 & H5OK & ISF & TX3 & OWN3 & BHUF3 & BREP3). clear BD.
    pose proof H53 as [_ H5L].
    pose proof (dm_geom m3 AH3) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & (A1 & A2 & A8 & A4 & A5) & (D0 & D3) & (AT1 & AT2) & _).
    pose proof G_lo as (_ & _ & _ & G4 & _).
    pose proof G_ff as (F1 & F2 & _ & F4 & _ & _ & F7 & F8' & F9'). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_src as [RSa RSb]. pose proof R_dc as [RD RDS].
    pose proof B_dc as [ABD IBD]. pose proof B_sr as [ABS _].
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; clear; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    assert (NZ : 0 < zlen src) by (clear - R9 RSZ ROFF NLEN; lia).
    destruct (FHL _ _ _ _ _ AH3) as [FAB _].
    destruct (dm_inblk (FB2 FF) NZ) as (IS & ID & IDS).
    (* [comment removed for export] *)
    assert (ART3 : art m3).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH3) as (_ & A & B & C & D & E & F' & G' & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
    assert (AHD3 : ahull RNG m3 DCTX 95992) by (eapply dm_ahull_wmono; [exact AH_dc| exact WM03]).
    assert (LBH' : ablkLB (FB2 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB2 FF :: LB) 2) by (apply ashort_push; [eapply ashort_mono; [exact ASH| clear; lia]| clear; lia]).
    assert (AFP : afpre AI rng_fs L RNG st (FB2 FF :: LB) m3 lo SPA 2).
    { unfold afpre, astk. split; [exact AH3|]. split; [exact ASH'|]. split; [exact ART3|].
      split; [split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3b SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    fk_hold KA. fk_hold ACC. fk_hold WIN. fk_hold NSK. fk_hold PRES0. fk_hold PPCS. fk_hold FFR3. fk_hold MU03.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_dc. fk_hold R_ds. fk_hold F7. fk_hold F8'. fk_hold F9'. fk_hold DSL. fk_hold XS3. fk_hold XB3. fk_hold DSK3.
    fk_hold PT3. fk_hold H13. fk_hold TX3. fk_hold OWN3. fk_hold BHUF3. fk_hold BREP3.
    dm_hold_sep.
    unfold DFR in FRA3.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unfold zd_decodefh_stmtA, APZD_DECODEFH in DECODEFH.
    eapply evtF_cut.
    { eapply (DECODEFH L RNG st (FB2 FF :: LB)) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (SRC := SRC) (src := src) (off := off) (hsz := hsz);
        first [ exact FP3 | exact H33 | exact XSC3 | exact H53 | exact H5OK | exact RD0 | exact RD1 | exact SB3 | exact OK | exact ROFF | exact STL3
              | exact AFP | exact TP | exact ARO3 | exact RD8 | exact AHD3 | exact ID | exact MI3 | reflexivity
              | lazymatch goal with
                | |- 5 <= hsz => clear - RHS; lia
                | |- off + hsz <= _ => clear - RSZ RH NLEN; lia
                | |- 0 < SRC => clear - SL1; lia
                | |- lo <= SPA - _ => clear - G2 G3a; lia
                | |- 0 <= SPA < _ => clear - G1 G2 G3a G3b G5; lia
                | |- DCTX + _ <= lo \/ SPA <= DCTX => clear - D2 G1; lia
                | |- SRC + _ <= lo \/ SPA <= SRC => clear - S_SR G3b; hlia
                | |- SRC + _ <= DCTX \/ _ => clear - SR_DC; hlia
                | |- areg _ _ SRC _ => intros _; split; [exact ABS| split; [exact US3| split; [exact RSa| exact RSb]]]
                | |- areg _ _ DCTX _ => intros _; split; [exact ABD| split; [exact UD3| split; [exact RD| exact RDS]]]
                | |- 0 < _ -> ainimg _ SRC _ => intros _; left; exact IS
                | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; f_equal; lia
                end
              | lazymatch goal with |- ?Gg => idtac "DECODEFH-LEFT:" Gg end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & fp4 & pcs4 & xs4 & ws4 & -> & MUc & WMc & MI4 & STL4 & FFR4 & AH4 & FP4 & H34 & XSC4 & H54 & GFH4).
    rd_retlit.
    unfold fk_held in XS3, XB3, DSK3, PT3, H13, TX3, OWN3, BHUF3, BREP3.
    (* [comment removed for export] *)
    set (W4 := [(DCTX + 29928, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (SPA - 4608, SPA)]) in *.
    assert (AW4 : aappW W4).
    { subst W4. pose proof (ablk_disj_band _ _ ABD) as DBD. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - DBD; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBD; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - G1 G2 G3a AT1; lia| apply Forall_nil]. }
    assert (WA4 : wapart W4) by (subst W4; intros X k Hk Q1 Q2 Q3 Q4 Q5; cbn [disjoint_from]; clear - Hk Q1 Q3 G2 G3a; repeat split; lia).
    assert (DJ4 : forall X k, (X + k <= DCTX + 29928 \/ DCTX + 30116 <= X) -> (X + k <= SPA - 4608 \/ SPA <= X) -> disjoint_from W4 X k)
      by (subst W4; intros X k Q1 Q3; cbn [disjoint_from]; clear - Q1 Q3; repeat split; lia).
    apply (dm_ffr_pres_weaken _ W4) in FFR4; [| subst W4; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; repeat split; lia].
    pose proof (binv_F m3 m4 W4 BI3 MUc WMc MI4 AH4 FFR4
                  ltac:(subst W4; apply Forall_cons; [cbn [fst snd]; clear; lia|]; apply Forall_cons; [cbn [fst snd]; clear; lia|];
                        apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI4.
    pose proof (sinv_F m3 m4 W4 SI3 AH3 MUc WMc FFR4 WA4 AW4 NZ) as SI4.
    pose proof (frame_keep_F W4 m3 m4 _ FRA3 eq_refl AH3 MUc WMc ltac:(apply DJ4; clear - D2 G1 G2 G3a; lia)) as FRA4.
    pose proof (xs_keep_F W4 m3 m4 _ XS3 eq_refl FFR4) as XS4.
    pose proof (xb_keep_F W4 m3 m4 _ XB3 eq_refl FFR4 ltac:(apply DJ4; unfold fk_held in F7; clear - F7 F3 G1 G2 G3a; lia)) as XB4.
    pose proof (dsk_keep_F W4 m3 m4 DSK3 AH3 MUc WMc FFR4 ltac:(intros HC; apply DJ4; unfold fk_held in D_DC, DSL; specialize (DSL HC); clear - D_DC DSL HC G1 G2 G3a; lia) NZ) as DSK4.
    unfold dctx_ptrs in PT3. unfold dctx_h1 in H13. unfold dctx_tx in TX3. destruct OWN3 as [OWE3 OWX3].
    eapply (dm_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W4) in PT3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| cbn; clear; lia]| apply DJ4; cbn; clear - D2 G1 G2 G3a; lia| exact MUc| exact WMc| exact FFR4]. rename PT3 into PT4.
    eapply (dm_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W4) in H13; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| cbn; clear; lia]| apply DJ4; cbn; clear - D2 G1 G2 G3a; lia| exact MUc| exact WMc| exact FFR4]. rename H13 into H14.
    eapply (dm_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W4) in TX3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| cbn; clear; lia]| apply DJ4; cbn; clear - D2 G1 G2 G3a; lia| exact MUc| exact WMc| exact FFR4]. rename TX3 into TX4.
    eapply (dm_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W4) in OWE3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| clear; lia]| apply DJ4; clear - D2 G1 G2 G3a; lia| exact MUc| exact WMc| exact FFR4]. rename OWE3 into OWE4.
    eapply (dm_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W4) in OWX3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| clear; lia]| apply DJ4; clear - D2 G1 G2 G3a; lia| exact MUc| exact WMc| exact FFR4]. rename OWX3 into OWX4.
    eapply (dm_fcall_bytes_pres AI FHL _ _ _ _ _ _ _ W4) in BHUF3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| cbn; clear; lia]| apply DJ4; cbn; clear - D2 G1 G2 G3a; lia| exact MUc| exact FFR4]. rename BHUF3 into BHUF4.
    eapply (dm_fcall_bytes_pres AI FHL _ _ _ _ _ _ _ W4) in BREP3; [| exact AH3| eapply dm_inblk_sub; [exact ID| clear; lia| cbn; clear; lia]| apply DJ4; cbn; clear - D2 G1 G2 G3a; lia| exact MUc| exact FFR4]. rename BREP3 into BREP4.
    pose proof SI4 as (_ & _ & _ & _ & _ & _ & UD4 & _).
    clear FRA3 XS3 XB3 DSK3 SB3 US3 UD3 UDS3 ARO3 ART3 AHD3 AFP BI3 SI3 STL3 FP3 H33 XSC3 H53 AH3 MI3 WM03 MUc WMc FFR4 DJ4 WA4 AW4.
    (* [comment removed for export] *)
    assert (H5OK4 : h5_frame_ok ws4 /\ wnth ws4 H5_isFrameDecompression = Z_to_bv 64 1).
    { revert GFH4. destruct (get_frame_header src off hsz) as [hh|v]; intros GFH4.
      - destruct GFH4 as (_ & _ & -> & _). destruct (dm_h5_vck ws (Z_to_bv 64 (if fh_checksum hh =? 0 then 0 else 1)) H5L H5OK) as (A & _ & C).
        split; [exact A| rewrite C; exact ISF].
      - destruct GFH4 as (_ & _ & ->). split; [exact H5OK| exact ISF]. }
    assert (DI4 : DINV m4 tot).
    { eapply (dinv_of m4 tot); [exact BI4| exact SI4| exact STL4| exact FRA4| exact XB4| reflexivity| exact XS4| exact DSK4|].
      exists (Z_to_bv 64 (DCTX + 32)), (Z_to_bv 64 (DCTX + 6192)), (Z_to_bv 64 (DCTX + 4136)), (Z_to_bv 64 (DCTX + 10296)),
             (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), (Z_to_bv 64 5), fp4,
             pcs4, wz0, (Z_to_bv 64 3), wz0, wz0, wz0, xs4, ws4, jhb, ovd, dcb, dce, wz0.
      split; [exact PT4|]. split; [exact H14|]. split; [exact FP4|]. split; [exact H34|]. split; [exact XSC4|].
      split; [exact H54|]. split; [exact (proj1 H5OK4)|]. split; [exact TX4| split; [exact OWE4| exact OWX4]]. }
    set (dfh := decode_frame_header src off hsz) in *.
    assert (RRET : 0 <= dfh < 18446744073709551616).
    { unfold dfh, decode_frame_header. destruct (get_frame_header src off hsz) as [hh|v] eqn:G; cbv iota; [clear; lia|].
      pose proof (gfh_ret_pos src off hsz v ltac:(clear - RHS; lia) G) as RP.
      destruct (zd_is_error v); cbv iota; [clear - RP; lia| unfold ZERR, ZE_srcSize_wrong; clear; lia]. }
    fk_hold BI4. fk_hold SI4. fk_hold STL4. fk_hold XS4. fk_hold XB4. fk_hold DSK4. fk_hold PT4. fk_hold H14. fk_hold H34. fk_hold XSC4. fk_hold H54. fk_hold TX4. fk_hold OWE4. fk_hold OWX4.
    fk_hold BHUF4. fk_hold BREP4. fk_hold DI4. fk_hold GFH4. fk_hold FP4. fk_hold H5OK4.
    unfold DFR in FRA4.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      zstep. zstep.
      gf_unhold.
      eapply (PRES0 m4 off sz tot dfh); [exact DI4| exact ROFF| exact RSZ| exact RT| exact RRET| exact ACC| | exact KA].
      intros E. exfalso. apply zd_is_error_false_iff in E. change (2^64) with 18446744073709551616 in E. clear - E KE. lia.
    - gf_unhold.
      assert (NE : zd_is_error dfh = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - KE RRET; lia).
      assert (DOK : exists h, get_frame_header src off hsz = FH_ok h).
      { revert NE. unfold dfh, decode_frame_header. destruct (get_frame_header src off hsz) as [hh|v]; cbv iota; [intros _; exists hh; reflexivity|].
        destruct (zd_is_error v) eqn:EV; cbv iota; intros NE; [rewrite EV in NE; discriminate NE|].
        rewrite zd_is_error_ZERR in NE by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate NE. }
      destruct DOK as [h G]. rewrite G in GFH4. destruct GFH4 as (FPE & PCSE & WSE & XSK4).
      destruct (dm_h5_vck ws (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1)) H5L H5OK) as (_ & VCK & _).
      rewrite <- WSE in VCK. destruct FP4 as [FP4 _]. rewrite FPE in FP4.
      eapply (PPCS m4 off sz tot hsz h PFX);
        [exact BI4| exact SI4| exact STL4| exact FRA4| exact XB4| reflexivity| exact XS4| exact DSK4| | | exact WIN| exact KA].
      + split; [exact PT4|]. split; [exact H14|]. split; [exact FP4|]. split; [exact H34|]. split; [exact XSC4|].
        split; [intros NZC; apply Z.eqb_neq in NZC; rewrite NZC in XSK4; destruct XSK4 as (j1 & j2 & E); exists j1, 0, j2; split; [exact E| clear; lia]|].
        split; [exact H54|]. split; [exact (proj1 H5OK4)|]. split; [exact VCK|]. split; [exact (proj2 H5OK4)|].
        split; [exists jhb, ovd, dcb, dce, (Z_to_bv 64 0); exact TX4|]. split; [split; [exact OWE4| exact OWX4]|].
        exact (tbl_init TBL TBLL m4 DCTX BHUF4 BREP4).
      + split; [exact ROFF|]. split; [exact RSZ|]. split; [exact RT|]. split; [exact ACC|]. split; [exact R9|]. split; [exact EHSZ|]. split; [exact RH|].
        split; [exact NSK| exact G].
  Qed.
End DM.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
