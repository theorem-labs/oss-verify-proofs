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

  Hypothesis XXHDIG : zd_xxh_digest_stmtA.

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
  (* [comment removed for export] *)
  Ltac zlbX SB IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        zstep; clear RD
    end.
  Ltac dm_hold_more :=
    repeat match goal with
    | H : AZ_dmf_f.SINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.BDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : AZ_dmf_f.KA_T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    end.

  (* [comment removed for export] *)
  Lemma p_trc : forall m off sz tot res ipF remF v32 vfl j0 j384 cs (x1 x5 x6 x7 x10 x11 x13 x14 x16 x17 x18 x26 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot v32 vfl j0 j384 -> rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat ->
    rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) -> dctx_any m DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipF -> ipF + remF <= size -> 0 <= remF < sz ->
    (forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evtF bsegs RNG POST (STpc 0x852fc m x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (DCTX + 95984)) x13 x14 (Z_to_bv 64 (SRC + ipF)) x16 x17 x18 (Z_to_bv 64 res) (Z_to_bv 64 remF)
                              (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot res ipF remF v32 vfl j0 j384 cs x1 x5 x6 x7 x10 x11 x13 x14 x16 x17 x18 x26 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK DA ROFF RSZ RT ACC RRES RF1' RF2' RF3' STEP KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof R_dc as [RD RDS]. pose proof SI as (_ & _ & _ & _ & _ & _ & UD & _ & GOT & _).
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold DA. fk_hold ACC. fk_hold KA. fk_hold FFR. fk_hold MU0. fk_hold STEP. fk_hold PRES. fk_hold PRES0.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL.
    dm_hold_sep.
    unfold DFR in FRA.
    (* [comment removed for export] *)
    zstep. zstep.
    rewrite ?(Z.mod_small ((DCTX + 95984) ≫ 3 + SHB) 18446744073709551616) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - D1 D2 AT2; Z.div_mod_to_equations; lia).
    pose proof (dm_sh_rd0s m DCTX 95992 (DCTX + 95984) UD ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 AT2; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 95984) ≫ 3 + SHB) 1).
    { eapply rng_sub'; [exact RDS|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    zstep. clear RDz RTz.
    try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. try replace (uxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                   (* [comment removed for export] *)
    zstep. zstep.                                      (* [comment removed for export] *)
    zstep. if_true.                                    (* [comment removed for export] *)
    zstep. zstep. zstep.                               (* [comment removed for export] *)
    gf_unhold.
    assert (NE : zd_is_error res = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - RRES RT RC40; lia).
    eapply (PRES0 m off sz tot res); [| exact ROFF| exact RSZ| exact RT| change (2^64) with 18446744073709551616; clear - RRES RT RC40; lia| exact ACC| | exact KA].
    - eapply (dinv_of m tot); [exact BI| exact SI| exact STL| exact FRA| exact XB| exact XBS| exact XS| exact DSK| exact DA].
    - intros _. exists ipF, remF. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - RRES; lia|]. split; [exact RF1'|]. split; [exact RF2'|]. split; [exact RF3'| exact STEP].
  Qed.

  (* [comment removed for export] *)
  Lemma p_cksum : forall m off sz tot res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384 cs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x27 x28 x29 x30 x31 : word),
    BINV m -> SINV m -> stk bsegs m lo SPA -> BFR m tot (Z_to_bv 64 remE) vfl j0 j384 -> rw_cells bsegs m (FF + 128) cs -> cells_size cs = 12%nat ->
    rw_cells bsegs m SHF DSHC -> stk bsegs m DST (DST + CAP) -> BDC m h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evtF bsegs RNG POST (STpc 0x85218 m x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 (SRC + ipE)) x16 x17 x18 (Z_to_bv 64 res) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws vfl j0 j384 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD RCK ROFF RSZ RT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof R_dc as [RD RDS]. pose proof R_src as [RSa RSb]. pose proof B_dc as [ABD IBD]. pose proof B_sr as [ABS _].
    pose proof SI as (_ & _ & _ & _ & SB & US & UD & _).
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    pose proof BD as (_ & _ & FP & _ & [XSC XSSZ] & _ & [H5C H5L] & H5OK & _).
    pose proof H5OK as (_ & K_FIC & _).
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold FFR. fk_hold MU0. fk_hold FIN. fk_hold PRES. fk_hold PRES0. fk_hold XXHDIG.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL. fk_hold SB. fk_hold US. fk_hold XSC. fk_hold H5C.
    dm_hold_sep.
    unfold DFR in FRA. unfold zfh_cells in FP.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite ?(Z.mod_small ((DCTX + 29960) ≫ 3 + SHB) 18446744073709551616) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - D1 D2 AT2; Z.div_mod_to_equations; lia).
    pose proof (dm_sh_rd0s m DCTX 95992 (DCTX + 29960) UD ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 AT2; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 29960) ≫ 3 + SHB) 1).
    { eapply rng_sub'; [exact RDS|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. zstep. zstep. if_false.                     (* [comment removed for export] *)
    zstep. rewrite sx32w_small by (clear - RCK; lia).  (* [comment removed for export] *)
    zstep.                                             (* [comment removed for export] *)
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zstep. zstep.                                    (* [comment removed for export] *)
      gf_unhold.
      eapply (p_trc m off sz tot res ipE remE); try eassumption.
      + eapply bdc_any; exact BD.
      + apply FIN. rewrite KC. cbn [Z.eqb]. split; reflexivity.
    - zstep. zstep. zstep. if_cases K4; zify_cond K4.  (* [comment removed for export] *)
      + (* [comment removed for export] *)
        zstep. zstep.
        rewrite ?(Z.mod_small ((DCTX + 30108) ≫ 3 + SHB) 18446744073709551616) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - D1 D2 AT2; Z.div_mod_to_equations; lia).
        pose proof (dm_sh_rd0s m DCTX 95992 (DCTX + 30108) UD ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 AT2; lia)) as RDz.
        assert (RTz : rng RNG ((DCTX + 30108) ≫ 3 + SHB) 1).
        { eapply rng_sub'; [exact RDS|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
          unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
        zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
        zstep. if_false.                               (* [comment removed for export] *)
        unfold fk_held in H5C. h5_open ws H5L. unfold wz0 in K_FIC. lazymatch type of K_FIC with ?x = _ => subst x end.
        zstep. rewrite (sx32w_small 0) by (clear; lia).  (* [comment removed for export] *)
        fk_hold H5C.
        zstep. if_false.                               (* [comment removed for export] *)
        zstep. zstep. zstep.                           (* [comment removed for export] *)
        unfold fk_held in XSC. pose proof XSC as [[XWF XBA] _].
        assert (XLEN : zlen (cells_bytes xs) = 88) by (rewrite (cells_bytes_length _ XWF), XSSZ; reflexivity).
        unfold fk_held in STL, XXHDIG.
        assert (ART : art m).
        { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F' & G' & _).
          unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
        unfold zd_xxh_digest_stmtA, APZD_XXH_DIGEST in XXHDIG.
        eapply evtF_cut.
        { eapply (XXHDIG RNG) with (SPV := SPA) (lo := lo) (STA := DCTX + 30008);
            first [ exact XBA | exact XLEN | exact RD8 | exact STL | exact ART | exact MI | reflexivity
                  | lazymatch goal with
                    | |- 4096 <= _ => clear - D1; lia
                    | |- (DCTX + 30008) mod 8 = 0 => clear - RD8; Z.div_mod_to_equations; lia
                    | |- DCTX + 30008 + 88 <= _ => clear - D2 AT2; lia
                    | |- lo <= SPA - _ => clear - G2 G3a; lia
                    | |- SPA < _ => clear - G3b G5; lia
                    | |- DCTX + 30008 + 88 <= lo \/ _ => clear - D2 G1; lia
                    | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact ABD| clear; lia| clear; lia]| split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear; lia]| split; [eapply rng_sub'; [exact RD| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; lia]]]]
                    | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 AT1; lia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3b; lia]| exact RI]]
                    end
                  | lazymatch goal with |- ?Gg => idtac "XXHDIG-LEFT:" Gg end ]. }
        cbv beta. intros ms' PO.
        destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & -> & MU2 & WM2 & MI2 & STL2).
        rd_retlit.
        (* [comment removed for export] *)
        unfold fk_held in BI, SI, XB, DSK, BD.
        assert (AW2 : aappW [(SPA - 64, SPA)]) by (apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - G1 G2 G3a AT1; lia| apply Forall_nil]).
        assert (WA2 : wapart [(SPA - 64, SPA)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; cbn [disjoint_from]; clear - Hk Q1 G2 G3a; split; [lia| exact I]).
        pose proof (binv_w m m2 [] [(SPA - 64, SPA)] BI MU2 WM2 MI2 ltac:(constructor) ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI2.
        pose proof (sinv_w m m2 _ SI AH MU2 WM2 WA2 AW2) as SI2.
        assert (FRA2 : BFR m2 tot (Z_to_bv 64 remE) vfl j0 j384) by (unfold DFR; eapply rw_cells_transport; [exact FRA| exact MU2| exact WM2| cbn; clear; lia]).
        assert (XB2 : rw_cells bsegs m2 (FF + 128) cs) by (eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| rewrite XBS; cbn; clear - F3 G1 G2 G3a; lia]).
        pose proof (xs_keep_w _ m m2 _ XS eq_refl AH MU2 WM2 AW2) as XS2.
        assert (DSK2 : stk bsegs m2 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MU2| exact WM2| intros HC; specialize (DSL HC); cbn; clear - DSL G1 G2 G3a; lia]).
        assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs _) by (eapply bdc_w; [exact BD| exact MU2| exact WM2| exact MI| exact MI2| cbn; clear - D2 G1 G2 G3a; lia]).
        pose proof BI2 as (AH2 & _). pose proof SI2 as (_ & _ & _ & _ & SB2 & US2 & _).
        clear BI SI STL XB XS DSK BD FRA FP XBA XWF H5C XSC ART MU2 WM2 MI AH SB US UD.
        fk_hold BI2. fk_hold SI2. fk_hold STL2. fk_hold XB2. fk_hold DSK2. fk_hold BD2. fk_hold FRA2. fk_hold XS2.
        (* [comment removed for export] *)
        pose proof (fk_ablk_lits _ _ ABS) as SL.
        dm_src_run0 SL ipE 4 0x852b8.
        dm_hold_all. dm_hold_more. fk_hold PRES. fk_hold PRES0.
        assert (IB : 0 <= ipE + 0 /\ ipE + 4 <= zlen src /\ 0 <= SRC) by (clear - K4 RE1 RE2 ROFF NLEN SBL; lia).
        zlbX SB2 IB (ipE + 1). zlbX SB2 IB ipE. zlbX SB2 IB (ipE + 2). zlbX SB2 IB (ipE + 3).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        unfold fk_held in FRA2. unfold DFR in FRA2.
        zstep. zstep. zstep. if_cases KM; clear KM.
        * (* [comment removed for export] *)
          zstep. zstep.
          gf_unhold.
          replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
          eapply (PRES m2 off sz tot (ZERR ZE_checksum_wrong)); [| exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_checksum_wrong; clear; lia| exact ACC| | exact KA].
          -- eapply (dinv_of m2 tot); [exact BI2| exact SI2| exact STL2| exact FRA2| exact XB2| exact XBS| exact XS2| exact DSK2| eapply bdc_any; exact BD2].
          -- intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_checksum_wrong, ZE_maxCode; clear; lia). discriminate E.
        * (* [comment removed for export] *)
          zstep. replace (SRC + ipE + 4) with (SRC + (ipE + 4)) by (clear; lia).
          zstep. zstep. replace (remE + -4) with (remE - 4) by (clear; lia).
          gf_unhold.
          eapply (p_trc m2 off sz tot res (ipE + 4) (remE - 4)); try eassumption.
          -- eapply bdc_any; exact BD2.
          -- clear - RE1; lia.
          -- clear - RE2; lia.
          -- clear - RE3 K4; lia.
          -- apply FIN. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC). split; [clear - K4; lia|]. split; reflexivity.
      + (* [comment removed for export] *)
        zstep. zstep.                                  (* [comment removed for export] *)
        gf_unhold.
        replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (PRES m off sz tot (ZERR ZE_checksum_wrong)); [| exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_checksum_wrong; clear; lia| exact ACC| | exact KA].
        * eapply (dinv_of m tot); [exact BI| exact SI| exact STL| exact FRA| exact XB| exact XBS| exact XS| exact DSK| eapply bdc_any; exact BD].
        * intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_checksum_wrong, ZE_maxCode; clear; lia). discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma p_fend : forall m off sz tot res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v32 vfl j0 j384 cs
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
    evtF bsegs RNG POST (STpc 0x851cc m x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 (SRC + ipE)) x16 x17 (Z_to_bv 64 (DST + tot + res)) (Z_to_bv 64 remE) (Z_to_bv 64 sz) x22
                              x24 (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Proof.
    intros m off sz tot res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws v32 vfl j0 j384 cs
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x22 x24 x27 x28 x29 x30 x31
           BI SI STL FRA XB XBS XS DSK BD RCK RFCS ROFF RSZ RT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof BI as (AH & FFR & MU0 & WM0 & MI).
    pose proof (dm_geom m AH) as ((G1 & G2 & G3a & G3b & G5) & (FL & F3 & F8 & ESHF & GS1 & GS2) & (D1 & D2) & DSL & (SL1 & SL2) & _ & (D0 & D3) & (AT1 & AT2) & _).
    pose proof R_dc as [RD RDS].
    change (2^64) with 18446744073709551616 in RFCS.
    fk_hold BI. fk_hold SI. fk_hold STL. fk_hold XB. fk_hold DSK. fk_hold BD. fk_hold ACC. fk_hold KA. fk_hold FFR. fk_hold MU0. fk_hold FIN. fk_hold PRES. fk_hold PRES0. fk_hold XXHDIG.
    fk_hold AH_dc. fk_hold AH_sr. fk_hold AH_ds. fk_hold R_src. fk_hold R_ds. fk_hold DSL.
    dm_hold_sep.
    unfold DFR in FRA. unfold DSHC in XS.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPA + 32, SPA + 40)] m) as MU2. pose proof (wmono_refl bsegs m) as WM2. pose proof MI as MIh. fk_hold MIh.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with MIc : mem_inv bsegs m2 |- _ => rename MIc into MI2 end.
    change (rw_cells bsegs m2 SHF DSHC) in XS. rename XS into XS2. rename FRA into FRA2.
    unfold fk_held in BI, SI, STL, XB, DSK, BD, MIh.
    pose proof (binv_w m m2 [] [(SPA + 32, SPA + 40)] BI MU2 WM2 MI2 ltac:(constructor) ltac:(apply Forall_cons; [cbn [fst snd]; clear - G2 G3a G3b; lia| apply Forall_nil])) as BI2.
    assert (WA2 : wapart [(SPA + 32, SPA + 40)]) by (intros X k Hk Q1 Q2 Q3 Q4 Q5; cbn [disjoint_from]; clear - Hk Q2; split; [lia| exact I]).
    assert (AW2 : aappW [(SPA + 32, SPA + 40)]) by (apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - G1 G2 G3a AT1; lia| apply Forall_nil]).
    pose proof (sinv_w m m2 _ SI AH MU2 WM2 WA2 AW2) as SI2.
    assert (STL2 : stk bsegs m2 lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MU2| exact WM2| cbn; clear; lia]).
    assert (XB2 : rw_cells bsegs m2 (FF + 128) cs) by (eapply rw_cells_transport; [exact XB| exact MU2| exact WM2| rewrite XBS; cbn; clear - F3 G1 G2 G3a; lia]).
    assert (DSK2 : stk bsegs m2 DST (DST + CAP)) by (eapply dsk_keep; [exact DSK| exact MU2| exact WM2| intros HC; specialize (DSL HC); cbn; clear - DSL G1 G2 G3a; lia]).
    assert (BD2 : BDC m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws) by (eapply bdc_w; [exact BD| exact MU2| exact WM2| exact MIh| exact MI2| cbn; clear - D2 G1 G2 G3a; lia]).
    pose proof BI2 as (AH2 & _ & _ & _ & _). pose proof SI2 as (_ & _ & _ & _ & _ & _ & UD2 & _).
    clear BI SI STL XB DSK BD MU2 WM2 MIh AH WA2 AW2.
    pose proof BD2 as (_ & _ & FP2 & _). unfold zfh_cells in FP2.
    fk_hold BI2. fk_hold SI2. fk_hold STL2. fk_hold XB2. fk_hold DSK2. fk_hold BD2.
    (* [comment removed for export] *)
    zstep.
    zstep. zstep.
    rewrite ?(Z.mod_small ((DCTX + 29928) ≫ 3 + SHB) 18446744073709551616) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - D1 D2 AT2; Z.div_mod_to_equations; lia).
    pose proof (dm_sh_rd0s m2 DCTX 95992 (DCTX + 29928) UD2 ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - D1; lia) ltac:(clear - D2 AT2; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 29928) ≫ 3 + SHB) 1).
    { eapply rng_sub'; [exact RDS|]. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    zstep. clear RDz RTz.
    try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. try replace (uxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                   (* [comment removed for export] *)
    zstep.                                             (* [comment removed for export] *)
    zstep. zstep.                                      (* [comment removed for export] *)
    (let w := getreg 19 in replace w with (Z_to_bv 64 res) by (apply Z_to_bv_eqm; clear - RRES RT D0 D3; rewrite ?Z.mod_small; lia)).
    zstep. zstep. zstep.                               (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU.
    - gf_unhold. eapply (p_cksum m2 off sz tot res ipE remE h PFX); try eassumption.
      intros ipF remF CKC. apply FIN; [exact CKC|]. intros NE. exfalso. apply NE. unfold ZD_CONTENTSIZE_UNKNOWN. clear - KU RFCS. lia.
    - zstep. if_cases KEQ; zify_cond KEQ.
      + gf_unhold. eapply (p_cksum m2 off sz tot res ipE remE h PFX); try eassumption.
        intros ipF remF CKC. apply FIN; [exact CKC|]. intros _. clear - KEQ RFCS RRES RT RC40. lia.
      + zstep. zstep. zstep.                           (* [comment removed for export] *)
        gf_unhold.
        replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (ZERR ZE_corruption_detected)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (PRES m2 off sz tot (ZERR ZE_corruption_detected)); [| exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_corruption_detected; clear; lia| exact ACC| | exact KA].
        * eapply (dinv_of m2 tot); [exact BI2| exact SI2| exact STL2| exact FRA2| exact XB2| exact XBS| exact XS2| exact DSK2| eapply bdc_any; exact BD2].
        * intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_corruption_detected, ZE_maxCode; clear; lia). discriminate E.
  Qed.
End DM.
End CANSEC1.
