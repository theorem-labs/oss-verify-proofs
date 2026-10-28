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
  Hypothesis PXD : forall m1 tot r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855a0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).
  Hypothesis PX72 : forall m1 tot (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot ->
    evtF bsegs RNG POST (STpc 0x85588 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31).
  Hypothesis PEXIT : forall m1 sz tot (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x27 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= sz < 2^64 -> 0 <= tot <= CAP -> (sz = 0 -> decompress_ok src size CAP tot) ->
    evtF bsegs RNG POST (STpc 0x85584 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) x22 x24 x25 x26 x27
                              (Z_to_bv 64 DST) x29 x30 x31).

  (* [comment removed for export] *)
  Notation FRst mm off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 :=
    (STpc 0x84b90 mm x1 (Z_to_bv 64 8) (Z_to_bv 64 (-120)) x7 x10 (Z_to_bv 64 5) x12 x13 x14 (Z_to_bv 64 25481893) (Z_to_bv 64 1) (Z_to_bv 64 4)
          (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31).

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
    gf_unhold; dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].
  Ltac dm_src_run0 SL off k STOP :=
    gf_unhold; dm_hold_all; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off) k; KAApp (SRC + off) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; gf_unhold ].

  (* [comment removed for export] *)
  Lemma p_head : forall m1 off sz tot (x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 : word),
    AINV m1 off sz tot ->
    (forall off' sz' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m1 off' sz' tot ->
        evtF bsegs RNG POST (LHst m1 off' sz' tot y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    (forall (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), (4 <= sz -> is_skippable_magic (le32 src off) = false) ->
        evtF bsegs RNG POST (FRst m1 off sz tot y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (LHst m1 off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31).
  Proof.
    intros m1 off sz tot x1 x7 x10 x12 x13 x14 x19 x25 x27 x29 x31 AIV KS KF.
    pose proof AIV as (DI & ROFF & RSZ & RSZ0 & RT & ACC).
    pose proof DI as ((AH1 & FFR1 & MU1 & WM1 & MI) & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & STL & STG & (ja & XA) & (jb & XB) & (jc & XC) & XL & XS & SB1 & US & UD & UDS & DSK & GOT & ARO & DA & AZS).
    pose proof B_sr as [S1 _]. pose proof R_src as (RSa & RSb).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ S1) as SL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (SRr : 6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47) by (clear - SL ATR; lia).
    assert (RSZ2 : 0 <= sz < 18446744073709551616) by (clear - RSZ0 RSZ ROFF N40 NLEN; lia).
    clear AH1 FFR1 MU1 WM1.
    zsF. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      gf_unhold. apply KF. intros C. exfalso. clear - C K4. lia. }
    (* [comment removed for export] *)
    dm_src_run0 SL off 4 0x84ab0.
    dm_hold_all. assert (IB : 0 <= off + 0 /\ off + 4 <= zlen src /\ 0 <= SRC) by (gf_unhold; clear - K4 RSZ ROFF NLEN DB; lia).
    zlbF SB1 OK IB (off + 1). zlbF SB1 OK IB off. zlbF SB1 OK IB (off + 2). zlbF SB1 OK IB (off + 3).
    do 7 zsF.
    match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; clear; lia) end.
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^4) with 16.
    zsF. if_cases KSK; zify_cond KSK.
    { (* [comment removed for export] *)
      gf_unhold. apply KF. intros _. unfold is_skippable_magic. apply Z.eqb_neq. exact KSK. }
    assert (SKM : is_skippable_magic (le32 src off) = true) by (unfold is_skippable_magic; apply Z.eqb_eq; exact KSK).
    zsF. if_cases K8; zify_cond K8.
    { (* [comment removed for export] *)
      gf_unhold. eapply (PX72 m1 tot). exact DI. }
    (* [comment removed for export] *)
    try clear KXE KXA KXRD KXK KXMI.
    dm_src_run SL off 4 4 0x84b0c.
    try clear KXMI. dm_hold_all.
    assert (IB2 : 0 <= off + 4 /\ off + 8 <= zlen src /\ 0 <= SRC) by (gf_unhold; clear - K8 RSZ ROFF NLEN DB; lia).
    zlbF SB1 OK IB2 (off + 5). zlbF SB1 OK IB2 (off + 4). zlbF SB1 OK IB2 (off + 6). zlbF SB1 OK IB2 (off + 7).
    do 7 zsF.                                            (* [comment removed for export] *)
    let w := getreg 25 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
      by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by (clear; lia); replace (off + 4 + 2) with (off + 6) by (clear; lia);
          replace (off + 4 + 3) with (off + 7) by (clear; lia); clear; lia).
    pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
    set (s32 := le32 src (off + 4)) in *.
    assert (RSK : read_skippable_frame_size src off sz =
                  if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if sz <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
    { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. unfold fk_held in K8. replace (sz <? 8) with false by (symmetry; apply Z.ltb_ge; clear - K8; lia).
      cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; clear - RS; lia)) as WI.
      unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
    clearbody s32.
    zsF. zsF. if_cases KU; zify_cond KU.                (* [comment removed for export] *)
    { (* [comment removed for export] *)
      zsF.
      replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 (ZERR ZE_frameParameter_unsupported)) by (apply Z_to_bv_eqm; reflexivity).
      gf_unhold. eapply (PXD m1 tot (ZERR ZE_frameParameter_unsupported)); [exact DI| unfold ZERR, ZE_frameParameter_unsupported; clear; lia| ].
      intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_frameParameter_unsupported, ZE_maxCode; clear; lia). discriminate E. }
    zsF. zsF. if_cases KFIT; zify_cond KFIT.            (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (RSV : read_skippable_frame_size src off sz = 8 + s32).
      { rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; clear - KU; lia).
        replace (sz <? 8 + s32) with false by (symmetry; apply Z.ltb_ge; clear - KFIT; lia). reflexivity. }
      unfold fk_held in ACC.
      assert (ACC2 : forall r, dmulti src (off + (s32 + 8)) (sz - (s32 + 8)) (CAP - tot) tot r -> decompress_ok src size CAP r).
      { intros r D. apply ACC. eapply (DM_skip src off sz (CAP - tot) tot r); [unfold ZD_FRAMEHEADERSIZE_PREFIX; clear - K8; lia | exact SKM | |].
        - rewrite RSV. apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. clear - RS; lia.
        - rewrite RSV. replace (off + (8 + s32)) with (off + (s32 + 8)) by (clear; lia). replace (sz - (8 + s32)) with (sz - (s32 + 8)) by (clear; lia). exact D. }
      gf_unhold.
      assert (AI2 : AINV m1 (off + (s32 + 8)) (sz - (s32 + 8)) tot).
      { split; [exact DI|]. split; [clear - ROFF RS; lia|]. split; [clear - RSZ KFIT; lia|]. split; [clear - KFIT; lia|]. split; [exact RT| exact ACC2]. }
      dm_hold_all. unfold fk_held in RSZ2.
      zsF. if_cases KE; zify_cond KE; [exfalso; clear - KE RS; lia|].   (* [comment removed for export] *)
      zsF. zsF. replace (SRC + off + (s32 + 8)) with (SRC + (off + (s32 + 8))) by (clear; lia).
      zsF. if_cases K5; zify_cond K5.                    (* [comment removed for export] *)
      + gf_unhold. eapply (KS (off + (s32 + 8)) (sz - (s32 + 8))); [clear - RS; lia | exact AI2].
      + zsF. gf_unhold. eapply (PEXIT m1 (sz - (s32 + 8)) tot); [exact DI| clear - KFIT RSZ2 RS; lia| exact RT|].
        intros E0. apply ACC2. rewrite E0. apply DM_end.
    - (* [comment removed for export] *)
      unfold fk_held in RSZ2.
      zsF. zsF. if_cases KE; zify_cond KE; [| exfalso; clear - KE; lia].
      replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
      gf_unhold. eapply (PXD m1 tot (ZERR ZE_srcSize_wrong)); [exact DI| unfold ZERR, ZE_srcSize_wrong; clear; lia| ].
      intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
  Qed.
End DM.
End CANSEC1.
