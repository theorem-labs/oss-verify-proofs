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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_libc_iface AZ_kx AZ_dmf_a AZ_dmf_b.
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
  Notation FRst mm off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 :=
    (STpc 0x84b90 mm x1 (Z_to_bv 64 8) (Z_to_bv 64 (-120)) x7 x10 (Z_to_bv 64 5) x12 x13 x14 (Z_to_bv 64 25481893) (Z_to_bv 64 1) (Z_to_bv 64 4)
          (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31).

  (* [comment removed for export] *)
  Definition BDC0 (m1 : amem) (PFX : Z) (fp : list cell) (xs : list cell) (ws : list word) (jhb : list byte) (ovd dcb dce : word) : Prop :=
    dctx_ptrs bsegs m1 DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
    /\ dctx_h1 bsegs m1 DCTX (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) (Z_to_bv 64 5)
    /\ dctx_fp bsegs m1 DCTX fp
    /\ dctx_h3 bsegs m1 DCTX (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
    /\ dctx_xs bsegs m1 DCTX xs
    /\ dctx_h5 bsegs m1 DCTX ws /\ h5_frame_ok ws /\ wnth ws H5_isFrameDecompression = Z_to_bv 64 1
    /\ dctx_tx bsegs m1 DCTX jhb ovd dcb dce (Z_to_bv 64 0)
    /\ dctx_owned bsegs m1 DCTX
    /\ bytes_at bsegs m1 (DCTX + 10296) (le4 (Z_to_bv 64 201326604))
    /\ bytes_at bsegs m1 (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)).

  Hypothesis DBEGIN : zd_dbegin_stmtA.
  Hypothesis CHECKCONT : zd_checkcont_stmtA.
  Hypothesis AH_dc : ahull RNG m0 DCTX 95992.

  (* [comment removed for export] *)
  Hypothesis PXD : forall m1 tot r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855a0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).
  Hypothesis DFRAME : forall m1 m2 tot tot' A B v8 v16 v24 v32 vfl j0 j384,
    DINV m1 tot -> SPA <= A -> A <= B -> B <= SPA + 408 -> munch [(A, B)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    rw_cells bsegs m2 SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot')) j0 j384) -> DINV m2 tot'.

  (* [comment removed for export] *)
  Notation HSZst mm off sz tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 :=
    (STpc 0x84df8 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25
          (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Hypothesis PHSZ : forall m3 off sz tot PFX fp xs ws jhb ovd dcb dce (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word),
    DINV m3 tot -> BDC0 m3 PFX fp xs ws jhb ovd dcb dce -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    0 <= off -> off + sz <= size -> 0 <= sz -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (4 <= sz -> is_skippable_magic (le32 src off) = false) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (HSZst m3 off sz tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Ltac hlia := unfold fk_held in *; lia.

  Lemma p_frame : forall m1 off sz tot (x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 : word),
    AINV m1 off sz tot ->
    (4 <= sz -> is_skippable_magic (le32 src off) = false) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (FRst m1 off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31).
  Proof.
    intros m1 off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 AIV NSK KA.
    pose proof AIV as (DI & ROFF & RSZ & RSZ0 & RT & ACC).
    pose proof DI as ((_ & _ & _ & _ & MI) & _ & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & _).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_dc as [RD RDS].
    pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9'). pose proof G_flg as (L0 & L1 & L2 & L3 & L4). pose proof B_dc as [ABD IBD].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DAL : 6443008 <= DCTX /\ DCTX + 95992 <= ATOP) by (pose proof (fk_ablk_lits _ _ ABD) as X; clear - X ATR; hlia).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite F4, shad_div; unfold ASHOFF; clear - FL ATR; Z.div_mod_to_equations; hlia).
    assert (SDA : DCTX + 95992 <= SPA \/ SPV <= DCTX) by (clear - S_DC G2 G3; hlia).
    assert (FLD : FLG + 1 <= DCTX \/ DCTX + 95992 <= FLG).
    { destruct IBD as (bb & Hb & Hb1 & Hb2). pose proof (L4 bb ltac:(right; exact Hb)) as X. clear - X Hb1 Hb2. lia. }
    assert (DCSH : DCTX + 95992 <= SHF \/ SHF + 32 <= DCTX) by (pose proof (fk_ablk_lits _ _ ABD) as LL; clear - LL GS ATR; hlia).
    unfold DFR in FRA.
    fk_hold DI. fk_hold AIV. fk_hold KA. fk_hold ACC. fk_hold NSK.
    fk_hold IBD. fk_hold L4. fk_hold F5. fk_hold F6. fk_hold RDS. fk_hold F4. fk_hold F2. fk_hold R_src. fk_hold R_dc. fk_hold R_ff. fk_hold LBH. fk_hold SDA. fk_hold FLD. fk_hold DCSH.
    dm_hold_sep.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPA + 320, SPA + 328)] m1) as MU2. pose proof (wmono_refl bsegs m1) as WM2.
    zstep.
    zstep. zstep. zstep. if_true.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    unfold fk_held in DI.
    lazymatch goal with MIc : mem_inv bsegs m1' |- _ =>
      pose proof (DFRAME m1 m1' tot tot (SPA + 320) (SPA + 328) _ _ _ _ _ _ _ DI ltac:(clear; hlia) ltac:(clear; hlia) ltac:(clear; hlia) MU2 WM2 MIc FRA) as DI1 end.
    clear MU2 WM2 DI. rename DI1 into DI. clear MI.
    clear FRA.
    pose proof DI as ((AH1 & FFR1 & MU1 & WM1 & MI) & SAV & FRAX & STL & STG & (ja & XA) & (jb & XB) & (jc & XC) & XL & XS & SB1 & US & UD & UDS & DSK & GOT & ARO & DA & AZS).
    clear FRAX.
    (* [comment removed for export] *)
    pose proof DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                      PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & OWN).
    (* [comment removed for export] *)
    pose proof DI as (_ & _ & (w8 & w16 & w24 & w32 & wfl & i0 & i384 & FRA) & _). unfold DFR in FRA.
    fk_hold DA. fk_hold SAV. fk_hold STG. fk_hold XA. fk_hold XB. fk_hold XC. fk_hold XL. fk_hold XS. fk_hold SB1. fk_hold US. fk_hold UDS. fk_hold DSK. fk_hold ARO. fk_hold AZS.
    fk_hold PT. fk_hold H1. fk_hold FPC. fk_hold H3. fk_hold XSC. fk_hold H5C. fk_hold TX. fk_hold OWN. fk_hold GOT. fk_hold FFR1. fk_hold MU1.
    zstep. zstep. zstep. zstep.
    unfold fk_held in DA, SAV, STG, XA, XB, XC, XL, XS, SB1, US, UDS, DSK, ARO, AZS. unfold fk_held in PT, H1, FPC, H3, XSC, H5C, TX, OWN, GOT, FFR1, MU1.
    assert (ART1 : art m1').
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & A & B & C & D & E & F' & G' & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
    assert (AHD1 : ahull RNG m1' DCTX 95992) by (eapply dm_ahull_wmono; [exact AH_dc| exact WM1]).
    unfold zd_dbegin_stmtA, APZD_DBEGIN in DBEGIN.
    eapply evtF_cut.
    { eapply (DBEGIN RNG) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (gend := wz0) (ws := ws);
        first [ exact PT | exact H1 | exact H3 | split; [exact H5C| exact H5L] | exact H5OK | exact TX | exact OWN | exact GOT | exact RD0 | exact RD1 | exact RD8
              | exact STL | exact ART1 | exact AHD1 | exact ARO | exact MI | reflexivity
              | lazymatch goal with
                | |- lo <= SPA - _ => clear - G2 G3; hlia
                | |- 0 <= SPA < _ => clear - G1 G2 G3 G5 ATR; hlia
                | |- SPA < _ => clear - G3 G5; hlia
                | |- DCTX + 95992 <= lo \/ SPA <= DCTX => clear - S_DC G3; hlia
                | |- 819152 + 16 <= lo \/ SPA <= 819152 => clear - S_GT G3; hlia
                | |- 819152 + 16 <= DCTX \/ _ => exact GT_DC
                | |- areg _ _ DCTX _ => intros _; split; [exact ABD| split; [exact UD| split; [exact RD| exact RDS]]]
                | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 ATR; hlia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; hlia]| exact RI]]
                end
              | lazymatch goal with |- ?Gg => idtac "DBEGIN-LEFT:" Gg end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MUc & WMc & MI2 & ST2 & PT2 & H12 & H32 & H52 & TX2 & OWN2 & BHUF & BREP).
    rd_retlit.
    clear PT H1 H3 H5C TX OWN ART1 AHD1.
    (* [comment removed for export] *)
    assert (DJc : forall X k, (X + k <= DCTX \/ DCTX + 95992 <= X) -> (X + k <= SPA - 2400 \/ SPA <= X) -> 0 <= k ->
              disjoint_from [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                             (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPA - 2400, SPA)] X k)
      by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; hlia).
    assert (AAW : aappW [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                         (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPA - 2400, SPA)]).
    { unfold aappW, KLOW, KHIGH. pose proof (ablk_disj_band _ _ ABD) as DBD. unfold KLS, KHIGH in DBD. clear - DBD G1 G2 G3 ATR.
      repeat (apply Forall_cons; [cbn [fst snd]; hlia|]). apply Forall_nil. }
    assert (DSHc : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 ->
              disjoint_from [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                             (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPA - 2400, SPA)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. apply aappW_shadow_disjoint; [exact AAW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - A B C ATR; Z.div_mod_to_equations; hlia. }
    assert (D0 : 0 <= DST /\ DST + CAP < 2^64)
      by (split; [destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; hlia| pose proof (DNN Hd) as X; clear - X; hlia] | clear - RDST; hlia]).
    pose proof (bytes_at_bound _ _ _ _ SB1) as SBL. rewrite length_map in SBL.
    assert (SAV2 : rw_cells bsegs m2 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact SAV| exact MUc| exact WMc| apply DJc; cbn; [clear - S_DC G2 G3| clear - G3| clear]; hlia]).
    assert (FRA2 : rw_cells bsegs m2 SPA (DFR w8 w16 w24 w32 wfl (Z_to_bv 64 (DST + tot)) i0 i384))
      by (unfold DFR; eapply rw_cells_transport; [exact FRA| exact MUc| exact WMc| apply DJc; cbn; [clear - S_DC G2 G3| clear| clear]; hlia]).
    assert (STG2 : stk bsegs m2 (SPA + 408) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG| exact MUc| exact WMc| apply DJc; [clear - S_DC G2 G3| clear| clear - G3]; hlia]).
    assert (XA2 : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 133203); C8 (Z_to_bv 64 542544); CB 104 ja])
      by (eapply rw_cells_transport; [exact XA| exact MUc| exact WMc| apply DJc; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XB2 : rw_cells bsegs m2 (FF + 128) [CB 12 jb])
      by (eapply rw_cells_transport; [exact XB| exact MUc| exact WMc| apply DJc; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XC2 : rw_cells bsegs m2 (FF + 140) [CB 108 jc; C8 (Z_to_bv 64 FLG)])
      by (eapply rw_cells_transport; [exact XC| exact MUc| exact WMc| apply DJc; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XL2 : rw_cells bsegs m2 FLG [C1 (Z_to_bv 8 1)])
      by (eapply rw_cells_transport; [exact XL| exact MUc| exact WMc| apply DJc; cbn; [clear - FLD| clear - L2 G1 G2 G3| clear]; hlia]).
    assert (XS2 : rw_cells bsegs m2 SHF DSHC)
      by (eapply rw_cells_transport; [exact XS| exact MUc| exact WMc| apply DJc; cbn; [clear - DCSH| clear - GS G1 G2 G3 ATR| clear]; hlia]).
    assert (SB2 : bytes_at bsegs m2 SRC (map (Z_to_bv 8) src))
      by (eapply bytes_at_transport; [exact SB1| exact MUc| rewrite length_map; apply DJc; [clear - SR_DC| clear - S_SR G2 G3| clear - SBL]; hlia]).
    assert (US2 : unpoisoned m2 SRC (SRC + zlen src)) by (eapply unpoisoned_munch; [exact US| exact MUc| apply DSHc; clear - RS0 RS1; hlia]).
    assert (UD2 : unpoisoned m2 DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MUc| apply DSHc; clear - RD0 RD1; hlia]).
    assert (UDS2 : 0 < CAP -> unpoisoned m2 DST (DST + CAP)) by (intros HC; eapply unpoisoned_munch; [exact (UDS HC)| exact MUc| apply DSHc; clear - D0 HC RDST; hlia]).
    assert (DSK2 : stk bsegs m2 DST (DST + CAP)).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - eapply stk_transport_disjoint; [exact DSK| exact MUc| exact WMc| apply DJc; [clear - D_DC| clear - S_DS G2 G3| clear - HC]; hlia].
      - replace (DST + CAP) with DST by (clear - HC RC0; hlia). apply dm_stk_empty; [clear - D0; hlia| clear - RDST RC0; hlia]. }
    assert (GOT2 : rw_cells bsegs m2 819152 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact GOT| exact MUc| exact WMc| apply DJc; cbn; [clear - GT_DC| clear - S_GT G1 G2 G3 ATR| clear]; hlia]).
    assert (ARO2 : aro_client RNG m2) by (eapply aro_client_transport; [exact ARO| exact MUc| exact WMc| exact AAW]).
    assert (AZS2 : azstk RNG m2 lo SPV) by (eapply azstk_transport; [exact AZS| exact MUc| exact WMc| exact AAW| clear - G2; hlia]).
    assert (FPC2 : rw_cells bsegs m2 (DCTX + 29928) fp)
      by (eapply rw_cells_transport; [exact FPC| exact MUc| exact WMc| rewrite FPSZ; cbn [disjoint_from]; clear - S_DC G2 G3; repeat split; hlia]).
    assert (XSC2 : rw_cells bsegs m2 (DCTX + 30008) xs)
      by (eapply rw_cells_transport; [exact XSC| exact MUc| exact WMc| rewrite XSSZ; cbn [disjoint_from]; clear - S_DC G2 G3; repeat split; hlia]).
    assert (AH2 : AHEAP AI L RNG st (FB2 FF :: LB) m2).
    { eapply (AI_frame AI); [exact AH1| exact MUc| exact WMc|].
      assert (IB : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> aclient_range CI (FB2 FF :: LB) (ATOP + 4096) X k).
      { intros X k A B. apply fk_acr_inblk. destruct IBD as (bb & Hb & Hb1 & Hb2). exists bb. split; [right; exact Hb| clear - A B Hb1 Hb2; hlia]. }
      repeat (apply Forall_cons; [cbn [fst snd]; first [apply IB; clear; hlia | left; left; clear - G1 G2 G3 G5; hlia]|]). apply Forall_nil. }
    assert (FFR2 : ffr_pres WR LB m0 m2).
    { eapply ffr_pres_trans; [exact FFR1|].
      eapply dm_ffr_pres_weaken.
      - eapply (fk_ffr_fin AI L RNG st LB m1' m1' m2 2 FF 256 SHF 0
                 [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                  (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992)] [(SPA - 2400, SPA)]);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; hlia | exact F4 | clear; hlia | clear; hlia
          | constructor; [cbn [fst snd]; split; [clear; hlia | left; clear - G1 G2 G3 G5; hlia] | constructor]
          | repeat (apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear; hlia]| clear; hlia]|]); apply Forall_nil
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; hlia
          | exact WMc ].
      - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
    assert (MU2 : munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] ++ fake_area L) m0 m2).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx. clear - Hx G2 G3. repeat split; hlia. }
    assert (WM2 : wmono bsegs m0 m2) by (eapply wmono_trans; [exact WM1| exact WMc]).
    clear SAV FRA STG XA XB XC XL XS SB1 US UD UDS DSK GOT ARO AZS AH1 FFR1 MU1 WM1 MI DA DJc DSHc MUc WMc FPC XSC.
    (* [comment removed for export] *)
    unfold DFR in FRA2.
    fk_hold SAV2. fk_hold STG2. fk_hold XA2. fk_hold XB2. fk_hold XC2. fk_hold XL2. fk_hold XS2. fk_hold SB2. fk_hold US2. fk_hold UDS2. fk_hold DSK2. fk_hold GOT2. fk_hold ARO2. fk_hold AZS2.
    fk_hold PT2. fk_hold H32. fk_hold H52. fk_hold TX2. fk_hold OWN2. fk_hold BHUF. fk_hold BREP. fk_hold FFR2. fk_hold MU2. fk_hold FPC2. fk_hold XSC2.
    zstep. zstep. if_true.
    zstep. zstep. zstep. zstep.
    unfold fk_held in SAV2, STG2, XA2, XB2, XC2, XL2, XS2, SB2, US2, UDS2, DSK2, GOT2, ARO2, AZS2. unfold fk_held in PT2, H32, H52, TX2, OWN2, BHUF, BREP, FFR2, MU2, FPC2, XSC2.
    assert (ART2 : art m2).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH2) as (_ & A & B & C & D & E & F' & G' & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
    unfold zd_checkcont_stmtA, APZD_CHECKCONT in CHECKCONT.
    eapply evtF_cut.
    { eapply (CHECKCONT RNG) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (DST := DST + tot) (dsize := CAP - tot);
        first [ exact H12 | exact RD0 | exact RD1 | exact RD8 | exact ST2 | exact ART2 | exact MI2 | reflexivity
              | lazymatch goal with
                | |- lo <= SPA - _ => clear - G2 G3; hlia
                | |- 0 < DCTX => clear - RD0; hlia
                | |- 0 <= DST + tot < _ => clear - D0 RT RDST RC40; hlia
                | |- 0 <= CAP - tot < _ => clear - RT RC40; hlia
                | |- SPA < _ => clear - G3 G5; hlia
                | |- DCTX + 95992 <= lo \/ SPA <= DCTX => clear - S_DC G3; hlia
                | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact ABD| clear; hlia| clear; hlia]| split; [eapply unpoisoned_sub; [exact UD2| clear; hlia| clear; hlia]| split; [eapply rng_sub'; [exact RD| clear; hlia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; hlia]]]]
                | |- astk _ _ _ => split; [unfold KHIGH; clear - G1 ATR; hlia| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; hlia]| exact RI]]
                | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; rewrite ?Z.mod_small; clear - RT RC40; hlia
                end
              | lazymatch goal with |- ?Gg => idtac "CHECKCONT-LEFT:" Gg end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & -> & MUd & WMd & MI3 & ST3 & H13).
    rd_retlit.
    set (PFX := if (DST + tot =? 0) || (CAP - tot =? 0) then 0 else DST + tot).
    assert (H1x : dctx_h1 bsegs m3 DCTX (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) (Z_to_bv 64 5)).
    { unfold PFX. unfold wz0 in H13. destruct ((DST + tot =? 0) || (CAP - tot =? 0)); exact H13. }
    assert (WIN : (PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot).
    { unfold PFX. destruct (Z.eqb_spec (DST + tot) 0) as [E1|E1]; destruct (Z.eqb_spec (CAP - tot) 0) as [E2|E2]; cbn [orb]; try (right; reflexivity); try (left; split; [reflexivity| exact E2]).
      pose proof (DNULL) as DN. clear - E1 E2 DN D0 RT. left. split; [reflexivity|]. assert (DST = 0) by lia. specialize (DN H). lia. }
    clearbody PFX. clear H13 H12 ART2.
    (* [comment removed for export] *)
    assert (DJd : forall X k, (X + k <= DCTX + 29888 \/ DCTX + 29920 <= X) -> (X + k <= SPA - 16 \/ SPA <= X) -> 0 <= k ->
              disjoint_from [(DCTX + 29888, DCTX + 29920); (SPA - 16, SPA)] X k)
      by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; hlia).
    assert (AAWd : aappW [(DCTX + 29888, DCTX + 29920); (SPA - 16, SPA)]).
    { unfold aappW, KLOW, KHIGH. pose proof (ablk_disj_band _ _ ABD) as DBD. unfold KLS, KHIGH in DBD. clear - DBD G1 G2 G3 ATR.
      repeat (apply Forall_cons; [cbn [fst snd]; hlia|]). apply Forall_nil. }
    assert (DSHd : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(DCTX + 29888, DCTX + 29920); (SPA - 16, SPA)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. apply aappW_shadow_disjoint; [exact AAWd| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - A B C ATR; Z.div_mod_to_equations; hlia. }
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply rw_cells_transport; [exact SAV2| exact MUd| exact WMd| apply DJd; cbn; [clear - S_DC G2 G3| clear - G3| clear]; hlia]).
    assert (FRA3 : rw_cells bsegs m3 SPA (DFR w8 w16 w24 w32 wfl (Z_to_bv 64 (DST + tot)) i0 i384))
      by (unfold DFR; eapply rw_cells_transport; [exact FRA2| exact MUd| exact WMd| apply DJd; cbn; [clear - S_DC G2 G3| clear| clear]; hlia]).
    assert (STG3 : stk bsegs m3 (SPA + 408) (SPV + -104)) by (eapply stk_transport_disjoint; [exact STG2| exact MUd| exact WMd| apply DJd; [clear - S_DC G2 G3| clear| clear - G3]; hlia]).
    assert (XA3 : rw_cells bsegs m3 FF [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 133203); C8 (Z_to_bv 64 542544); CB 104 ja])
      by (eapply rw_cells_transport; [exact XA2| exact MUd| exact WMd| apply DJd; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XB3 : rw_cells bsegs m3 (FF + 128) [CB 12 jb])
      by (eapply rw_cells_transport; [exact XB2| exact MUd| exact WMd| apply DJd; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XC3 : rw_cells bsegs m3 (FF + 140) [CB 108 jc; C8 (Z_to_bv 64 FLG)])
      by (eapply rw_cells_transport; [exact XC2| exact MUd| exact WMd| apply DJd; cbn; [clear - F7| clear - F3 G1 G2 G3| clear]; hlia]).
    assert (XL3 : rw_cells bsegs m3 FLG [C1 (Z_to_bv 8 1)])
      by (eapply rw_cells_transport; [exact XL2| exact MUd| exact WMd| apply DJd; cbn; [clear - FLD| clear - L2 G1 G2 G3| clear]; hlia]).
    assert (XS3 : rw_cells bsegs m3 SHF DSHC)
      by (eapply rw_cells_transport; [exact XS2| exact MUd| exact WMd| apply DJd; cbn; [clear - DCSH| clear - GS G1 G2 G3 ATR| clear]; hlia]).
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src))
      by (eapply bytes_at_transport; [exact SB2| exact MUd| rewrite length_map; apply DJd; [clear - SR_DC| clear - S_SR G2 G3| clear - SBL]; hlia]).
    assert (US3 : unpoisoned m3 SRC (SRC + zlen src)) by (eapply unpoisoned_munch; [exact US2| exact MUd| apply DSHd; clear - RS0 RS1; hlia]).
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD2| exact MUd| apply DSHd; clear - RD0 RD1; hlia]).
    assert (UDS3 : 0 < CAP -> unpoisoned m3 DST (DST + CAP)) by (intros HC; eapply unpoisoned_munch; [exact (UDS2 HC)| exact MUd| apply DSHd; clear - D0 HC RDST; hlia]).
    assert (DSK3 : stk bsegs m3 DST (DST + CAP)).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - eapply stk_transport_disjoint; [exact DSK2| exact MUd| exact WMd| apply DJd; [clear - D_DC| clear - S_DS G2 G3| clear - HC]; hlia].
      - replace (DST + CAP) with DST by (clear - HC RC0; hlia). apply dm_stk_empty; [clear - D0; hlia| clear - RDST RC0; hlia]. }
    assert (GOT3 : rw_cells bsegs m3 819152 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact GOT2| exact MUd| exact WMd| apply DJd; cbn; [clear - GT_DC| clear - S_GT G1 G2 G3 ATR| clear]; hlia]).
    assert (ARO3 : aro_client RNG m3) by (eapply aro_client_transport; [exact ARO2| exact MUd| exact WMd| exact AAWd]).
    assert (AZS3 : azstk RNG m3 lo SPV) by (eapply azstk_transport; [exact AZS2| exact MUd| exact WMd| exact AAWd| clear - G2; hlia]).
    assert (PT3 : dctx_ptrs bsegs m3 DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296)))
      by (unfold dctx_ptrs in *; eapply rw_cells_transport; [exact PT2| exact MUd| exact WMd| apply DJd; cbn; [clear| clear - S_DC G2 G3| clear]; hlia]).
    assert (FP3 : dctx_fp bsegs m3 DCTX fp)
      by (split; [eapply rw_cells_transport; [exact FPC2| exact MUd| exact WMd| rewrite FPSZ; apply DJd; [clear| clear - S_DC G2 G3| clear]; hlia]| exact FPSZ]).
    assert (H33 : dctx_h3 bsegs m3 DCTX wz0 wz0 (Z_to_bv 64 3) wz0 wz0 wz0)
      by (unfold dctx_h3 in *; eapply rw_cells_transport; [exact H32| exact MUd| exact WMd| apply DJd; cbn; [clear| clear - S_DC G2 G3| clear]; hlia]).
    assert (XSC3 : dctx_xs bsegs m3 DCTX xs)
      by (split; [eapply rw_cells_transport; [exact XSC2| exact MUd| exact WMd| rewrite XSSZ; apply DJd; [clear| clear - S_DC G2 G3| clear]; hlia]| exact XSSZ]).
    assert (H53 : dctx_h5 bsegs m3 DCTX (wupd (wupd ws H5_isFrameDecompression (Z_to_bv 64 1)) H5_dictID wz0)).
    { destruct H52 as [H5C2 H5L2]. split; [| exact H5L2]. eapply rw_cells_transport; [exact H5C2| exact MUd| exact WMd|].
      rewrite (h5_cells_size _ H5L2). apply DJd; [clear| clear - S_DC G2 G3| clear]; hlia. }
    assert (TX3 : dctx_tx bsegs m3 DCTX jhb ovd dcb dce wz0)
      by (unfold dctx_tx in *; eapply rw_cells_transport; [exact TX2| exact MUd| exact WMd| apply DJd; cbn; [clear| clear - S_DC G2 G3| clear]; hlia]).
    assert (OWN3 : dctx_owned bsegs m3 DCTX).
    { destruct OWN2 as [OWE OWX]. split; (eapply stk_transport_disjoint; [eassumption| exact MUd| exact WMd| apply DJd; [clear| clear - S_DC G2 G3| clear]; hlia]). }
    assert (BHUF3 : bytes_at bsegs m3 (DCTX + 10296) (le4 (Z_to_bv 64 201326604)))
      by (eapply bytes_at_transport; [exact BHUF| exact MUd| apply DJd; cbn; [clear| clear - S_DC G2 G3| clear]; hlia]).
    assert (BREP3 : bytes_at bsegs m3 (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)))
      by (eapply bytes_at_transport; [exact BREP| exact MUd| apply DJd; cbn; [clear| clear - S_DC G2 G3| clear]; hlia]).
    assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MUd| exact WMd|].
      constructor; [cbn [fst snd]; apply fk_acr_inblk; destruct IBD as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| clear - Hb1 Hb2; hlia]|].
      constructor; [cbn [fst snd]; left; left; clear - G1 G2 G3 G5; hlia| constructor]. }
    assert (FFR3 : ffr_pres WR LB m0 m3).
    { eapply ffr_pres_trans; [exact FFR2|].
      eapply dm_ffr_pres_weaken.
      - eapply (fk_ffr_fin AI L RNG st LB m2 m2 m3 2 FF 256 SHF 0 [(DCTX + 29888, DCTX + 29920)] [(SPA - 16, SPA)]);
          [ exact AH2 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; hlia | exact F4 | clear; hlia | clear; hlia
          | constructor; [cbn [fst snd]; split; [clear; hlia | left; clear - G1 G2 G3 G5; hlia] | constructor]
          | constructor; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear; hlia]| clear; hlia]| constructor]
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUd]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; hlia
          | exact WMd ].
      - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
    assert (MU3 : munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - 7184, SPV)] ++ fake_area L) m0 m3).
    { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MUd]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx. clear - Hx G2 G3. repeat split; hlia. }
    assert (WM3 : wmono bsegs m0 m3) by (eapply wmono_trans; [exact WM2| exact WMd]).
    clear SAV2 FRA2 STG2 XA2 XB2 XC2 XL2 XS2 SB2 US2 UD2 UDS2 DSK2 GOT2 ARO2 AZS2 AH2 FFR2 MU2 WM2 MI2 PT2 H32 H52 TX2 OWN2 BHUF BREP FPC2 XSC2 DJd DSHd MUd WMd ST2.
    (* [comment removed for export] *)
    destruct (dm_h5_begin ws H5L H5OK) as [H5OK3 ISF3].
    lazymatch type of H53 with dctx_h5 _ _ _ ?w => set (ws3 := w) in * end.
    assert (DI3 : DINV m3 tot).
    { split; [split; [exact AH3| split; [exact FFR3| split; [exact MU3| split; [exact WM3| exact MI3]]]]|].
      split; [exact SAV3|]. split; [do 7 eexists; exact FRA3|]. split; [exact ST3|]. split; [exact STG3|].
      split; [exists ja; exact XA3|]. split; [exists jb; exact XB3|]. split; [exists jc; exact XC3|]. split; [exact XL3|]. split; [exact XS3|].
      split; [exact SB3|]. split; [exact US3|]. split; [exact UD3|]. split; [exact UDS3|]. split; [exact DSK3|]. split; [exact GOT3|]. split; [exact ARO3|].
      split; [| exact AZS3].
      exists (Z_to_bv 64 (DCTX + 32)), (Z_to_bv 64 (DCTX + 6192)), (Z_to_bv 64 (DCTX + 4136)), (Z_to_bv 64 (DCTX + 10296)),
             (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), (Z_to_bv 64 5), fp,
             wz0, wz0, (Z_to_bv 64 3), wz0, wz0, wz0, xs, ws3, jhb, ovd, dcb, dce, wz0.
      split; [exact PT3|]. split; [exact H1x|]. split; [exact FP3|]. split; [exact H33|]. split; [exact XSC3|].
      split; [exact H53|]. split; [exact H5OK3|]. split; [exact TX3| exact OWN3]. }
    assert (BD3 : BDC0 m3 PFX fp xs ws3 jhb ovd dcb dce).
    { split; [exact PT3|]. split; [exact H1x|]. split; [exact FP3|]. split; [exact H33|]. split; [exact XSC3|].
      split; [exact H53|]. split; [exact H5OK3|]. split; [exact ISF3|]. split; [exact TX3|]. split; [exact OWN3|]. split; [exact BHUF3| exact BREP3]. }
    clear SAV3 STG3 XA3 XB3 XC3 XL3 XS3 SB3 US3 UD3 UDS3 DSK3 GOT3 ARO3 AZS3 PT3 H1x FP3 H33 XSC3 H53 H5OK3 ISF3 TX3 OWN3 BHUF3 BREP3 AH3 FFR3 MU3 WM3.
    fk_hold DI3. fk_hold BD3. unfold DFR in FRA3.
    unfold fk_held in ACC, KA, NSK, WIN.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold fk_held in DI3, BD3.
    eapply (PHSZ m3 off sz tot PFX fp xs ws3 jhb ovd dcb dce);
      [exact DI3| exact BD3| exact WIN| exact ROFF| exact RSZ| exact RSZ0| exact RT| exact ACC| exact NSK| exact KA].
  Qed.
End DM.
End CANSEC1.
