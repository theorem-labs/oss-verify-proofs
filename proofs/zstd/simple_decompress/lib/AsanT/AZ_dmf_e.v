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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_libc_iface AZ_kx AZ_getfh_a AZ_dmf_a AZ_dmf_b AZ_dmf_d.
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
  Notation GFHst mm off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 :=
    (STpc 0x84f58 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 hsz) (Z_to_bv 64 sz) (Z_to_bv 64 DCTX)
          (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  Hypothesis PGFH : forall m3 off sz tot hsz PFX fp xs ws jhb ovd dcb dce (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
    DINV m3 tot -> BDC0 m3 PFX fp xs ws jhb ovd dcb dce -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    9 <= sz -> hsz = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX -> hsz + 3 <= sz -> is_skippable_magic (le32 src off) = false ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (GFHst m3 off sz tot hsz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Notation HSZst mm off sz tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 :=
    (STpc 0x84df8 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot))
          x25 (Z_to_bv 64 (SRC + off)) x27 x28 x29 x30 x31).
  (* [comment removed for export] *)
  Ltac gf_unhold := unfold fk_held in *.
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
    dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].
  Ltac dm_src_run0 SL off k STOP :=
    gf_unhold; dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off) k; KAApp (SRC + off) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].

  (* [comment removed for export] *)
  Ltac tbl_sh mm T UT RT k Rk :=
    rewrite ?(Z.mod_small (T + k * 8) 18446744073709551616) by (clear - Rk; lia);
    pose proof (dm_sh_rd0s mm T 32 (T + k * 8) UT ltac:(clear - Rk; lia) ltac:(clear - Rk; Z.div_mod_to_equations; lia) ltac:(clear; lia) ltac:(clear; lia)) as RDt;
    assert (RTt : rng RNG ((T + k * 8) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RT|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; clear - Rk; Z.div_mod_to_equations; lia).

  (* [comment removed for export] *)
  Lemma p_hsz : forall m3 off sz tot PFX fp xs ws jhb ovd dcb dce (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word),
    DINV m3 tot -> BDC0 m3 PFX fp xs ws jhb ovd dcb dce -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    0 <= off -> off + sz <= size -> 0 <= sz -> 0 <= tot <= CAP ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (4 <= sz -> is_skippable_magic (le32 src off) = false) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (HSZst m3 off sz tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31).
  Proof.
    intros m3 off sz tot PFX fp xs ws jhb ovd dcb dce x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31
           DI3 BD WIN ROFF RSZ RSZ0 RT ACC NSK KA.
    pose proof DI3 as ((AH3 & FFR3 & MU3 & WM3 & MI3) & SAV3 & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA3) & ST3 & STG3 & (ja & XA3) & (jb & XB3) & (jc & XC3) & XL3 & XS3 & SB3 & US3 & UD3 & UDS3 & DSK3 & GOT3 & ARO3 & DA3 & AZS3).
    pose proof BD as (PT3 & H1x & FP3 & H33 & XSC3 & H53 & H5OK & ISF & TX3 & OWN3 & BHUF3 & BREP3).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_dc as [RD RDS].
    pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9'). pose proof G_flg as (L0 & L1 & L2 & L3 & L4). pose proof B_dc as [ABD IBD].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DAL : 6443008 <= DCTX /\ DCTX + 95992 <= ATOP) by (pose proof (fk_ablk_lits _ _ ABD) as X; clear - X ATR; lia).
    assert (RSZ2 : 0 <= sz < 18446744073709551616) by (clear - RSZ0 RSZ ROFF N40 NLEN; lia).
    clear DA3.
    fk_hold DI3. fk_hold BD. fk_hold KA. fk_hold ACC. fk_hold NSK. fk_hold WIN.
    fk_hold IBD. fk_hold L4. fk_hold F5. fk_hold F6. fk_hold RDS. fk_hold F4. fk_hold F2. fk_hold R_src. fk_hold R_dc. fk_hold R_ff. fk_hold LBH.
    fk_hold AH3. fk_hold FFR3. fk_hold MU3. fk_hold PGFH. fk_hold PRES0.
    dm_hold_sep.
    destruct H53 as [H5C H5L].
    assert (H53 : dctx_h5 bsegs m3 DCTX ws) by (split; [exact H5C| exact H5L]). clear H5C.
    (* [comment removed for export] *)
    unfold DFR in FRA3.
    pose proof H5OK as (K_FMT & _). h5_open ws H5L. lazymatch type of K_FMT with ?x = _ => subst x end. lazymatch type of ISF with ?x = _ => subst x end.
    cbv beta iota delta [wupd H5_isFrameDecompression H5_dictID] in H53. destruct H53 as [H5C3 H5L3]. unfold wz0 in H5C3. cbv beta iota delta [h5_cells h5_sizes mk_wcells] in H5C3.
    fk_hold SAV3. fk_hold STG3. fk_hold XA3. fk_hold XB3. fk_hold XC3. fk_hold XL3. fk_hold XS3. fk_hold SB3. fk_hold US3. fk_hold UDS3. fk_hold DSK3. fk_hold GOT3. fk_hold ARO3. fk_hold AZS3.
    fk_hold PT3. fk_hold H1x. fk_hold FP3. fk_hold H33. fk_hold XSC3. fk_hold TX3. fk_hold OWN3. fk_hold BHUF3. fk_hold BREP3. fk_hold FFR3. fk_hold MU3. fk_hold WIN. fk_hold H5C3.
    zstep.                                           (* [comment removed for export] *)
    pose proof (dm_sh_rd0 m3 DCTX 95992 (DCTX + 30104) UD3 ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - DAL; lia) ltac:(clear - DAL ATR; lia)) as RDz.
    assert (RTz : rng RNG (SHB + (DCTX + 30104) / 8) 1).
    { unfold fk_held in RDS. eapply rng_sub'; [exact RDS|]. unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
    fk_hold UD3.
    zstep.                                           (* [comment removed for export] *)
    clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                                 (* [comment removed for export] *)
    zstep.                                           (* [comment removed for export] *)
    unfold fk_held in H5C3.
    zstep. rewrite (sx32w_small 0) by (clear; lia).  (* [comment removed for export] *)
    fk_hold H5C3.
    zstep. if_true.                                  (* [comment removed for export] *)
    zstep. zstep.                                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    clear DI3. assert (DI3 : DINV m3 tot).
    { unfold fk_held in *.
      split; [split; [exact AH3| split; [exact FFR3| split; [exact MU3| split; [exact WM3| exact MI3]]]]|].
      split; [exact SAV3|]. split; [do 7 eexists; exact FRA3|]. split; [exact ST3|]. split; [exact STG3|].
      split; [exists ja; exact XA3|]. split; [exists jb; exact XB3|]. split; [exists jc; exact XC3|]. split; [exact XL3|]. split; [exact XS3|].
      split; [exact SB3|]. split; [exact US3|]. split; [exact UD3|]. split; [exact UDS3|]. split; [exact DSK3|]. split; [exact GOT3|]. split; [exact ARO3|].
      split; [| exact AZS3].
      lazymatch type of H5C3 with rw_cells _ _ _ (h5_cells ?l) =>
        exists (Z_to_bv 64 (DCTX + 32)), (Z_to_bv 64 (DCTX + 6192)), (Z_to_bv 64 (DCTX + 4136)), (Z_to_bv 64 (DCTX + 10296)),
               (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), (Z_to_bv 64 5), fp,
               wz0, wz0, (Z_to_bv 64 3), wz0, wz0, wz0, xs, l, jhb, ovd, dcb, dce, wz0
      | _ => exists (Z_to_bv 64 (DCTX + 32)), (Z_to_bv 64 (DCTX + 6192)), (Z_to_bv 64 (DCTX + 4136)), (Z_to_bv 64 (DCTX + 10296)),
               (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), (Z_to_bv 64 5), fp,
               wz0, wz0, (Z_to_bv 64 3), wz0, wz0, wz0, xs;
             lazymatch type of H5L3 with length ?l = _ => exists l, jhb, ovd, dcb, dce, wz0 end
      end.
      split; [exact PT3|]. split; [exact H1x|]. split; [exact FP3|]. split; [exact H33|]. split; [exact XSC3|].
      split; [split; [first [exact H5C3 | cbv beta iota delta [h5_cells h5_sizes mk_wcells]; cbv beta iota delta [h5_cells h5_sizes mk_wcells] in H5C3; exact H5C3]| exact H5L3]|].
      split; [| split; [exact TX3| exact OWN3]].
      clear - H5OK. unfold h5_frame_ok in *.
      cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
          H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression H5_dictID] in *. exact H5OK. }
    zstep. if_cases K9; zify_cond K9.               (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep.                                        (* [comment removed for export] *)
      unfold fk_held in ACC. unfold fk_held in KA. unfold fk_held in PRES0.
      (let w := getreg 19 in replace w with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) at 1 by (apply Z_to_bv_eqm; reflexivity)).
      eapply (PRES0 m3 off sz tot (ZERR ZE_srcSize_wrong)); [exact DI3| exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_srcSize_wrong; clear; lia| exact ACC| | exact KA].
      intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
    - (* [comment removed for export] *)
      pose proof B_sr as [S1 _]. unfold fk_held in S1. pose proof (fk_ablk_lits _ _ S1) as SL.
      unfold fk_held in R_src. pose proof R_src as (RSa & RSb). fk_hold R_src.
      unfold fk_held in SB3. pose proof (bytes_at_bound _ _ _ _ SB3) as DB3. rewrite length_map in DB3.
      unfold fk_held in ARO3.
      assert (AT1 : aro RNG m3 136800 32) by (aro_cl ARO3). assert (AT2 : aro RNG m3 136864 32) by (aro_cl ARO3).
      destruct AT1 as (UT1 & _ & RT2). destruct AT2 as (UT2 & _ & RT4). fk_hold ARO3.
      unfold fk_held in US3.
      zsF. zsF. if_true. zsF.                       (* [comment removed for export] *)
      zsF. zsF.                                     (* [comment removed for export] *)
      try replace (SRC + off + 5 + -1) with (SRC + off + 4) by (clear; lia).
      (* [comment removed for export] *)
      dm_src_run SL off 4 1 0x84e58.
      dm_hold_all. fk_hold PRES0. fk_hold PGFH. fk_hold KA. fk_hold AH3. fk_hold FFR3. fk_hold MU3. fk_hold ACC. fk_hold NSK.
      assert (IB : 0 <= off + 4 /\ off + 5 <= zlen src /\ 0 <= SRC) by (gf_unhold; clear - K9 RSZ ROFF NLEN DB3; lia).
      zlbF SB3 OK IB (off + 4).
      set (fhd := Znth (off + 4) src) in *.
      pose proof (fhd_dictIDSizeCode_range fhd) as RDC. assert (RF : 0 <= fhd < 256) by assumption. pose proof (fhd_fcsID_range fhd RF) as RFC.
      (* [comment removed for export] *)
      zsF. zsF. zsF. zsF.
      replace (Z.land fhd 3) with (fhd_dictIDSizeCode fhd) by (unfold fhd_dictIDSizeCode; change 3 with (Z.ones 2); rewrite Z.land_ones by (clear - RF; lia); reflexivity).
      (* [comment removed for export] *)
      zsF.
      unfold fk_held in UT1, UT2. tbl_sh m3 136800 UT1 RT2 (fhd_dictIDSizeCode fhd) RDC.
      zsF. zsF. zsF. clear RDt RTt. zsF. if_false.
      (* [comment removed for export] *)
      zsF.
      replace (fhd ≫ 6) with (fhd_fcsID fhd) by (unfold fhd_fcsID; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
      zsF. zsF. zsF. zsF.
      (* [comment removed for export] *)
      tbl_sh m3 136864 UT2 RT4 (fhd_fcsID fhd) RFC.
      zsF. zsF. zsF. clear RDt RTt. zsF. if_false.
      zsF.                                          (* [comment removed for export] *)
      assert (RDD := tblA_did_rd m3 (fhd_dictIDSizeCode fhd) MI3 RDC). zsF. clear RDD.
      assert (RDF := tblA_fcs_rd m3 (fhd_fcsID fhd) MI3 RFC). zsF. clear RDF.
      do 9 zsF.
      let w := getreg 19 in first [ replace w with (Z_to_bv 64 (fhd_header_size fhd))
        by (f_equal; unfold fhd_header_size, ZD_FRAMEHEADERSIZE_PREFIX, fhd_singleSegment, fhd_dictIDSizeCode, fhd_fcsID, did_fieldSize, fcs_fieldSize; clear - RF; byte_brute fhd)
        | idtac "HSZ=" w; fail ].
      pose proof (fhd_header_size_range fhd) as RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
      assert (EHSZ : fhd_header_size fhd = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX).
      { subst fhd. rewrite frame_header_size_ge5 by (unfold ZD_FRAMEHEADERSIZE_PREFIX; clear - K9; lia). reflexivity. }
      set (hsz := fhd_header_size fhd) in *. clearbody hsz.
      zsF. if_cases KH; zify_cond KH; [exfalso; clear - KH RHS; lia|].   (* [comment removed for export] *)
      zsF. zsF. if_cases KS; zify_cond KS.                               (* [comment removed for export] *)
      + (* [comment removed for export] *)
        gf_unhold.
        lazymatch type of H5C3 with rw_cells _ _ _ ?cs =>
        lazymatch type of H5L3 with length ?l = _ =>
          eapply (PGFH m3 off sz tot hsz PFX fp xs l jhb ovd dcb dce)
        end end.
        * exact DI3.
        * split; [exact PT3|]. split; [exact H1x|]. split; [exact FP3|]. split; [exact H33|]. split; [exact XSC3|].
          split; [split; [cbv beta iota delta [h5_cells h5_sizes mk_wcells]; exact H5C3| exact H5L3]|].
          split. { clear - H5OK. unfold h5_frame_ok in *.
                   cbv beta iota delta [wnth wupd nth H5_validateChecksum H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree
                       H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff H5_isFrameDecompression H5_dictID] in *. exact H5OK. }
          split; [cbv beta iota delta [wnth nth H5_isFrameDecompression]; reflexivity|]. split; [exact TX3|]. split; [exact OWN3|]. split; [exact BHUF3| exact BREP3].
        * exact WIN.
        * exact ROFF. * exact RSZ. * exact RT. * exact ACC.
        * clear - K9; lia. * exact EHSZ. * clear - KS; lia.
        * apply NSK. clear - K9; lia.
        * exact KA.
      + (* [comment removed for export] *)
        zsF.                                        (* [comment removed for export] *)
        (let w := getreg 19 in replace w with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) at 1 by (apply Z_to_bv_eqm; reflexivity)).
        gf_unhold.
        eapply (PRES0 m3 off sz tot (ZERR ZE_srcSize_wrong)); [exact DI3| exact ROFF| exact RSZ| exact RT| unfold ZERR, ZE_srcSize_wrong; clear; lia| exact ACC| | exact KA].
        intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
  Qed.
End DM.
End CANSEC1.
