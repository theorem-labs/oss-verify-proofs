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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_libc_iface AZ_kx AZ_dmf_a.
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

(* [comment removed for export] *)
Definition DSHC : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF2;
   C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Definition DSHO : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF2;
   C1 B00; C1 B04; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].

(* [comment removed for export] *)
Lemma dm_sh_rd0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (SHB + p / 8)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.shiftr_div_pow2 in RD by lia. change (2^3) with 8 in RD.
  replace (p / 8 + 2147450880) with (2147450880 + p / 8) in RD by lia. exact RD.
Qed.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Lemma dm_ffr_pres_tl : forall W b LB (m m' : amem), ffr_pres W (b :: LB) m m' -> ffr_pres W LB m m'.
Proof.
  intros W b LB m m' H. unfold ffr_pres in *. eapply magree_mono; [exact H|].
  intros a [[(cls & A & n & Hin & Ha) HO]|(a' & (cls & A & n & Hin & Ha) & ->)].
  - left. split; [exists cls, A, n; split; [right; exact Hin| exact Ha]| exact HO].
  - right. exists a'. split; [exists cls, A, n; split; [right; exact Hin| exact Ha]| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma dm_dctx_any_transport : forall DCTX W' (m1 m2 : amem), dctx_any m1 DCTX -> munch W' m1 m2 -> wmono bsegs m1 m2 ->
  disjoint_from W' DCTX 95992 -> dctx_any m2 DCTX.
Proof.
  intros DCTX W' m1 m2 (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                   PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) MU WM DJ.
  assert (TR : forall A cs, rw_cells bsegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m2 A cs).
  { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ | lia | lia]. }
  assert (TS : forall a b, stk bsegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk bsegs m2 a b).
  { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply dm_disjoint_from_sub; [exact DJ | lia | lia]. }
  unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
  exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
  split; [apply TR; [exact PT | lia | cbn; lia]|].
  split; [apply TR; [exact H1 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
  split; [apply TR; [exact H3 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
  split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
  split; [exact H5OK|].
  split; [apply TR; [exact TX | lia | cbn; lia]|].
  split; apply TS; try assumption; lia.
Qed.

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

  Hypothesis ERRCODE : zd_errcode_stmtA.

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
  Hypothesis PTAIL : forall m1 r jA w0 shb (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 408 jA] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 408) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    dctx_any m1 DCTX -> stk bsegs m1 DST (DST + CAP) ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855b4 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 FF) x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).

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

  Lemma dfr_forget : forall (m : amem) v8 v16 v24 v32 vfl vdst j0 j384,
    rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl vdst j0 j384) ->
    exists jA jB, rw_cells bsegs m SPA [CB 344 jA; C8 (Z_to_bv 64 FF); CB 56 jB].
  Proof.
    intros m v8 v16 v24 v32 vfl vdst j0 j384 H. unfold DFR in H.
    apply (rw_cells_merge bsegs _ _ [] [CB 8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _;
      C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] _) in H.
    cbn [app cells_size csize Nat.add] in H.
    apply (rw_cells_merge bsegs _ _ [CB 344 _; C8 (Z_to_bv 64 FF)] [C8 _; C8 _; C8 _; C8 _; CB 16 _; C8 _] []) in H.
    cbn [app cells_size csize Nat.add] in H. do 2 eexists. exact H.
  Qed.
  Lemma dfr_blob : forall (m : amem) v8 v16 v24 v32 vfl vdst j0 j384,
    rw_cells bsegs m SPA (DFR v8 v16 v24 v32 vfl vdst j0 j384) -> exists jA, rw_cells bsegs m SPA [CB 408 jA].
  Proof.
    intros m v8 v16 v24 v32 vfl vdst j0 j384 H. destruct (rw_cells_forget _ _ _ _ H) as [jA H']. exists jA. exact H'.
  Qed.

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
  Lemma binv_ff : forall m m' i j, BINV m -> munch [(FF + i, FF + j)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    0 <= i -> i <= j -> j <= 256 -> BINV m'.
  Proof.
    intros m m' i j (AH & FFR & MU0 & WM0 & MI) MU WM MI' Hi Hij Hj.
    pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & _).
    split.
    { eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [cbn [fst snd]| constructor].
      eapply fk_acr_frame; [left; reflexivity| clear - Hi; lia| clear - Hij Hj; lia]. }
    split.
    { eapply ffr_pres_trans; [exact FFR|]. apply dm_ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m m m' 2 FF 256 SHF 0 [] [(FF + i, FF + j)]);
        [ exact AH | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | | constructor | apply ffr_pres_refl | | exact WM ].
      - constructor; [cbn [fst snd]| constructor]. split; [clear - Hij; lia|]. right. split.
        + intros b Hb. pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH b Hb) as HB. clear - HB Hi Hj. lia.
        + exists FF, (FF + 256). split; [exact F1| clear - Hi Hj; lia].
      - cbn [app]. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx.
      clear - Hx F5 F6 Hi Hj. lia. }
    split; [exact (wmono_trans _ _ _ _ WM0 WM)| exact MI'].
  Qed.

  (* [comment removed for export] *)
  Lemma p_stub : forall m1 r jA jB w0 shb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 344 jA; C8 (Z_to_bv 64 FF); CB 56 jB] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 408) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    dctx_any m1 DCTX -> stk bsegs m1 DST (DST + CAP) ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855a0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 r jA jB w0 shb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31
           BI SAV FRA STL STG XM XP XL XS DA1 DSK1 RR RM.
    pose proof BI as (AH1 & _ & _ & _ & MI).
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9').
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4). pose proof R_ff as (RF1 & RF2 & RF3). pose proof B_dc as [ABD IBD].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia).
    assert (FFSH : FF + 256 <= SHF \/ SHF + 32 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL GS ATR; lia).
    assert (F0' : 6443008 <= FF) by (pose proof (fk_ablk_lits _ _ F1) as FL; clear - FL; lia).
    pose proof (munch_refl [(FF + 0, FF + 8)] m1) as MU2. pose proof (wmono_refl bsegs m1) as WM2.
    fk_hold BI. fk_hold DA1. fk_hold DSK1. fk_hold RM. fk_hold AH1.
    fk_hold F1. fk_hold F2. fk_hold F4. fk_hold F5. fk_hold F6. fk_hold F7. fk_hold F8'. fk_hold F9'. fk_hold L0. fk_hold L1. fk_hold L3. fk_hold L4.
    fk_hold LBH. fk_hold IBD. fk_hold ABD. fk_hold ESHF. fk_hold G4. fk_hold G6.
    dm_hold_sep. fk_hold R_src. fk_hold R_dc. fk_hold RD0. fk_hold RD1. fk_hold RD8. fk_hold RS0. fk_hold RS1. fk_hold RC0. fk_hold RC40. fk_hold RDST.
    fk_hold OK. fk_hold N0. fk_hold NLEN. fk_hold N40.
    assert (KONT : forall m2 (y10 : word), munch [(FF + 0, FF + 8)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
      rw_cells bsegs m2 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs m2 SPA [CB 344 jA; C8 (Z_to_bv 64 FF); CB 56 jB] -> stk bsegs m2 lo SPA -> stk bsegs m2 (SPA + 408) (SPV + -104) ->
      rw_cells bsegs m2 FF [C8 (Z_to_bv 64 MAGIC_RETIRED)] -> rw_cells bsegs m2 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m2 FLG [C1 (Z_to_bv 8 1)] ->
      rw_cells bsegs m2 SHF [CB 32 shb] ->
      evtF bsegs RNG POST (STpc 0x855b4 m2 x1 x5 x6 x7 y10 (Z_to_bv 64 FF) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31)).
    { intros m2 y10 MU WM MI2 SAV2 FRA2 STL2 STG2 XM2 XP2 XL2 XS2. unfold fk_held in *.
      destruct (rw_cells_forget _ _ _ _ FRA2) as [jX FRA3]. cbn [cells_size csize Nat.add] in FRA3.
      eapply (PTAIL m2 r jX _ shb); try eassumption.
      - eapply (binv_ff m1 m2 0 8); [exact BI| exact MU| exact WM| exact MI2| clear; lia| clear; lia| clear; lia].
      - eapply dm_dctx_any_transport; [exact DA1| exact MU| exact WM|]. cbn [disjoint_from]. clear - F7. split; [lia| exact I].
      - destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
        + eapply stk_transport_disjoint; [exact DSK1| exact MU| exact WM|]. cbn [disjoint_from]. clear - F8' HC. split; [lia| exact I].
        + replace (DST + CAP) with DST by (clear - HC RC0; lia). apply dm_stk_empty; [| clear - RDST RC0; lia].
          destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia]. }
    fk_hold KONT.
    all: zstep; zstep.                                    (* [comment removed for export] *)
    all: try (let w := getreg 10 in replace w with (Z_to_bv 64 MAGIC_RETIRED) by (apply Z_to_bv_eqm; reflexivity)).
    all: zstep.                                           (* [comment removed for export] *)
    all: zstep.                                           (* [comment removed for export] *)
    all: zstep.                                           (* [comment removed for export] *)
    all: (if_cases K; zify_cond K); first [exfalso; clear - K F0' F3 ATR; lia | clear K].   (* [comment removed for export] *)
    all: unfold fk_held in KONT; eapply KONT; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma p_xD : forall m1 tot r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evtF bsegs RNG POST (STpc 0x855a0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 tot r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x27 x28 x29 x30 x31
           (BI & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & STL & STG & (ja & XA) & (jb & XB) & (jc & XC) & XL & XS & SB & US & UD & UDS & DSK & GOT & ARO & DA & AZS)
           RR RM.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add] in XS'.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 108 jc] [C8 (Z_to_bv 64 FLG)]) XC) as [_ XP]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XP.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 248) in XP by (clear; lia) end.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XA) as [XM _].
    destruct (dfr_forget m1 v8 v16 v24 v32 vfl _ j0 j384 FRA) as (jA & jB & FRA').
    eapply (p_stub m1 r jA jB _ shb); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma p_exit : forall m1 sz tot (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x27 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= sz < 2^64 -> 0 <= tot <= CAP -> (sz = 0 -> decompress_ok src size CAP tot) ->
    evtF bsegs RNG POST (STpc 0x85584 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 (Z_to_bv 64 sz) x22 x24 x25 x26 x27
                              (Z_to_bv 64 DST) x29 x30 x31).
  Proof.
    intros m1 sz tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x27 x29 x30 x31 DI RSZ RT ACC.
    pose proof DI as (BI & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & STL & STG & REST).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6).
    assert (D0 : 0 <= DST /\ DST + tot < 2^64)
      by (split; [destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia] | clear - RDST RT; lia]).
    fk_hold DI. fk_hold BI. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold REST. fk_hold ACC.
    dm_hold_sep. fk_hold R_src. fk_hold R_dc.
    unfold DFR in FRA.
    zstep. if_cases K; zify_cond K.
    - zstep. zstep.                                      (* [comment removed for export] *)
      (let w := getreg 25 in replace w with (Z_to_bv 64 tot) by (apply Z_to_bv_eqm; rewrite ?Zminus_mod_idemp_l, ?Z.mod_small; clear - D0 RT; lia)).
      zstep.
      unfold fk_held in *.
      eapply (p_xD m1 tot tot); [exact DI| clear - RT RC40; lia | intros _; apply ACC; clear - K; lia].
    - zstep.                                             (* [comment removed for export] *)
      zstep.
      replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
      unfold fk_held in *.
      eapply (p_xD m1 tot (ZERR ZE_srcSize_wrong)); [exact DI| unfold ZERR, ZE_srcSize_wrong; clear; lia| ].
      intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma p_x72 : forall m1 tot (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot ->
    evtF bsegs RNG POST (STpc 0x85588 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 DI.
    pose proof DI as (BI & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & REST).
    fk_hold DI. fk_hold BI. fk_hold SAV. fk_hold REST. dm_hold_sep.
    zstep.                                               (* [comment removed for export] *)
    zstep.
    replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
    unfold fk_held in *.
    eapply (p_xD m1 tot (ZERR ZE_srcSize_wrong)); [exact DI| unfold ZERR, ZE_srcSize_wrong; clear; lia| ].
    intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_frame : forall m1 m2 tot tot' A B v8 v16 v24 v32 vfl j0 j384,
    DINV m1 tot -> SPA <= A -> A <= B -> B <= SPA + 408 -> munch [(A, B)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    rw_cells bsegs m2 SPA (DFR v8 v16 v24 v32 vfl (Z_to_bv 64 (DST + tot')) j0 j384) -> DINV m2 tot'.
  Proof.
    intros m1 m2 tot tot' A B v8 v16 v24 v32 vfl j0 j384
           ((AH1 & FFR1 & MU1 & WM1 & _) & SAV & _ & STL & STG & (ja & XA) & (jb & XB) & (jc & XC) & XL & XS & SB & US & UD & UDS & DSK & GOT & ARO & DA & AZS)
           LA LAB LB' MU WM MI FRA.
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9'). pose proof G_flg as (L0 & L1 & L2 & L3 & L4).
    pose proof B_dc as [ABD IBD]. pose proof B_sr as [ABS _].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (GS : SHB + 805376 <= SHF /\ SHF + 32 <= 17594333495296)
      by (pose proof (fk_ablk_lits _ _ F1) as FL; rewrite F4, shad_div; unfold ASHOFF; clear - FL ATR; Z.div_mod_to_equations; lia).
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    assert (DJ : forall X k, (X + k <= SPA \/ SPA + 408 <= X) -> disjoint_from [(A, B)] X k) by (intros X k H; cbn; clear - H LA LB'; lia).
    split.
    { split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WM)| exact MI]]]].
      - eapply (AI_frame AI); [exact AH1| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. left. left. clear - G1 G2 LA LAB LB' G3 G5. lia.
      - eapply ffr_pres_trans; [exact FFR1|]. apply dm_ffr_pres_mono_nil1. apply (dm_ffr_pres_tl _ (FB2 FF)). eapply (fk_ffr_stack AI); [exact AH1| exact MU| exact WM|].
        constructor; [cbn [fst]; clear - G1 G2 G3 LA; lia| constructor].
      - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside app]; intros x Hx. clear - Hx LA LB' G2 G3. lia. }
    split; [eapply rw_cells_transport; [exact SAV| exact MU| exact WM| apply DJ; cbn; clear - G3; lia]|].
    split; [do 7 eexists; exact FRA|].
    split; [eapply stk_transport_disjoint; [exact STL| exact MU| exact WM| apply DJ; cbn; clear; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MU| exact WM| apply DJ; cbn; clear; lia]|].
    split; [exists ja; eapply rw_cells_transport; [exact XA| exact MU| exact WM| apply DJ; cbn; clear - F3 G1 G2 G3; lia]|].
    split; [exists jb; eapply rw_cells_transport; [exact XB| exact MU| exact WM| apply DJ; cbn; clear - F3 G1 G2 G3; lia]|].
    split; [exists jc; eapply rw_cells_transport; [exact XC| exact MU| exact WM| apply DJ; cbn; clear - F3 G1 G2 G3; lia]|].
    split; [eapply rw_cells_transport; [exact XL| exact MU| exact WM| apply DJ; cbn; clear - L2 G1 G2 G3; lia]|].
    split; [eapply rw_cells_transport; [exact XS| exact MU| exact WM| apply DJ; cbn; clear - GS ATR G1 G2 G3; lia]|].
    split; [eapply bytes_at_transport; [exact SB| exact MU| rewrite length_map; apply DJ; clear - S_SR G2 G3; lia]|].
    assert (DSH : forall X n, 0 <= X -> X + n <= 2^47 -> disjoint_from [(A, B)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n H0 H1. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. clear - H0 H1 G1 G2 G3 LA ATR. split; [| exact I]. Z.div_mod_to_equations. lia. }
    split; [eapply unpoisoned_munch; [exact US| exact MU| apply DSH; clear - RS0 RS1; lia]|].
    split; [eapply unpoisoned_munch; [exact UD| exact MU| apply DSH; clear - RD0 RD1; lia]|].
    assert (D0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia]).
    split; [intros HC; eapply unpoisoned_munch; [exact (UDS HC)| exact MU| apply DSH; clear - D0 HC RDST; lia]|].
    split.
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC].
      - eapply stk_transport_disjoint; [exact DSK| exact MU| exact WM| apply DJ; cbn; clear - S_DS G2 G3; lia].
      - replace (DST + CAP) with DST by (clear - HC RC0; lia). apply dm_stk_empty; [| clear - RDST RC0; lia].
        destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia]. }
    split; [eapply rw_cells_transport; [exact GOT| exact MU| exact WM| apply DJ; cbn; clear - S_GT G1 G2 G3 ATR; lia]|].
    split; [eapply aro_client_transport; [exact ARO| exact MU| exact WM| constructor; [cbn [fst snd]; right; unfold KHIGH; clear - G1 G2 G3 LA ATR; lia| constructor]]|].
    split; [eapply dm_dctx_any_transport; [exact DA| exact MU| exact WM| apply DJ; cbn; clear - S_DC G2 G3; lia]|].
    eapply azstk_transport; [exact AZS| exact MU| exact WM| constructor; [cbn [fst snd]; right; unfold KHIGH; clear - G1 G2 G3 LA ATR; lia| constructor]| clear - G2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma p_top : forall m1 off sz tot (x1 x5 x7 x12 x13 x14 x15 x16 x17 x19 x25 x27 x29 x31 : word),
    AINV m1 off sz tot ->
    (forall (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), evtF bsegs RNG POST (LHst m1 off sz tot y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (STpc 0x84a70 m1 x1 x5 (Z_to_bv 64 (-120)) x7 (Z_to_bv 64 1) (Z_to_bv 64 5) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19
                              (Z_to_bv 64 sz) (Z_to_bv 64 DCTX) (Z_to_bv 64 (CAP - tot)) x25 (Z_to_bv 64 (SRC + off)) x27 (Z_to_bv 64 DST) x29 (Z_to_bv 64 0) x31).
  Proof.
    intros m1 off sz tot x1 x5 x7 x12 x13 x14 x15 x16 x17 x19 x25 x27 x29 x31 AIV KA.
    pose proof AIV as (DI & ROFF & RSZ & RSZ0 & RT & ACC).
    pose proof DI as (BI & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & STL & STG & XA3 & XB3 & XC3 & XL & XS & SB & US & UD & UDS & DSK & GOT & ARO & DA & AZS).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof R_dc as [RD RDS].
    (* [comment removed for export] *)
    unfold DFR in FRA.
    fk_hold BI. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XA3. fk_hold XB3. fk_hold XC3. fk_hold XL. fk_hold XS. fk_hold SB.
    fk_hold US. fk_hold UD. fk_hold UDS. fk_hold DSK. fk_hold GOT. fk_hold ARO. fk_hold DA. fk_hold ACC. fk_hold KA. fk_hold DI. fk_hold AIV.
    fk_hold RDS. fk_hold R_src. fk_hold R_ff. fk_hold LBH.
    dm_hold_sep.
    zstep.                                               (* [comment removed for export] *)
    zstep. if_false.                                     (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    zstep. zstep.                                        (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    unfold fk_held in KA. apply KA.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma p_res : forall m1 off sz tot res (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x20 = Z_to_bv 64 sz' /\ x26 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (STpc 0x84ee4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 res) x20 (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31
           DI ROFF RSZ RT RRES ACC SUCC KA.
    pose proof DI as ((_ & _ & _ & _ & MI) & _).
    pose proof DI as (BI & SAV & (v8 & v16 & v24 & v32 & vfl & j0 & j384 & FRA) & STL & STG & XA3 & XB3 & XC3 & XL & XS & SB & US & UD & UDS & DSK & GOT & ARO & DA & AZS).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof R_ff as (RF1 & RF2 & RF3). pose proof R_dc as [RD RDS].
    pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8' & F9'). pose proof B_dc as [ABD IBD].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DAL : 6443008 <= DCTX /\ DCTX + 95992 <= ATOP) by (pose proof (fk_ablk_lits _ _ ABD) as X; clear - X ATR; lia).
    assert (SDA : DCTX + 95992 <= SPA \/ SPV <= DCTX) by (clear - S_DC G2 G3; lia).
    assert (D0 : 0 <= DST /\ DST + CAP < 2^47)
      by (split; [destruct (Z.eq_dec DST 0) as [->|Hd]; [clear; lia| pose proof (DNN Hd) as X; clear - X; lia] | exact RDST]).
    pose proof DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                      PT & H1 & FP & H3 & XSC & [H5C H5L] & H5OK & TX & OWN).
    pose proof H5OK as (K_FMT & _).
    h5_open ws H5L. lazymatch type of K_FMT with ?x = _ => subst x end. unfold wz0 in H5C.
    apply (rw_cells_merge bsegs _ _ [C8 b; C4 (Z_to_bv 64 0)] [C4 b1; C4 b2; C4 b3; C8 b4; C8 b5; C8 b6; C8 b7; C8 b8; C8 b9; C8 b10; C4 b11; C4 b12; C8 b13; C8 b14; C4 b15;
      C4 b16; C4 b17; C4 b18; C8 b19; C4 b20; C4 b21; C4 b22; C4 b23; C8 b24; C8 b25; C8 b26; C8 b27; C8 b28; C8 b29; C8 b30; C8 b31; C8 b32; C4 b33; C4 b34;
      C4 b35; C4 b36; C8 b37; C8 b38; C8 b39; C8 b40; C8 b41; C4 b42] []) in H5C.
    cbn [app cells_size csize Nat.add] in H5C.
    clear PT H1 FP H3 XSC TX OWN.
    unfold DFR in FRA.
    (* [comment removed for export] *)
    fk_hold BI. fk_hold SAV. fk_hold STL. fk_hold STG. fk_hold XA3. fk_hold XB3. fk_hold XC3. fk_hold XL. fk_hold XS. fk_hold SB.
    fk_hold US. fk_hold UD. fk_hold UDS. fk_hold DSK. fk_hold GOT. fk_hold ARO. fk_hold DA. fk_hold ACC. fk_hold SUCC. fk_hold KA. fk_hold DI.
    fk_hold IBD. fk_hold F5. fk_hold F6. fk_hold RDS. fk_hold F4. fk_hold F2. fk_hold R_src. fk_hold R_dc. fk_hold R_ff. fk_hold LBH. fk_hold SDA.
    dm_hold_sep.
    zstep.                                               (* [comment removed for export] *)
    zstep.                                               (* [comment removed for export] *)
    unfold zd_errcode_stmtA, APZD_ERRCODE in ERRCODE. change (2^64) with 18446744073709551616 in RRES.
    eapply evtF_cut; [eapply (ERRCODE RNG); [exact RRES| reflexivity]|]. cbv beta. intros ms' (a1' & ->). rd_retlit.
    zstep. zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. if_cases KP.                                  (* [comment removed for export] *)
    - clear KP. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
      unfold fk_held in *.
      eapply (p_xD m1 tot (ZERR ZE_srcSize_wrong)); [exact DI| unfold ZERR, ZE_srcSize_wrong; clear; lia| ].
      intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). discriminate E.
    - clear KP. zstep. zstep. if_cases KE; zify_cond KE.  (* [comment removed for export] *)
      + zstep. zstep.                                    (* [comment removed for export] *)
        unfold fk_held in *.
        eapply (p_xD m1 tot res); [exact DI| change (2^64) with 18446744073709551616; exact RRES| ].
        intros E. apply zd_is_error_false_iff in E. change (2^64) with 18446744073709551616 in E. exfalso. clear - E KE. lia.
      + (* [comment removed for export] *)
        assert (NE : zd_is_error res = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - KE RRES; lia).
        unfold fk_held in SUCC. destruct (SUCC NE) as (off' & sz' & -> & -> & RRC & RO1 & RO2 & RSZ' & STEP).
        zstep.                                           (* [comment removed for export] *)
        unfold fk_held in UD.
        pose proof (dm_sh_rd0 m1 DCTX 95992 (DCTX + 30104) UD ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - DAL; lia) ltac:(clear - DAL ATR; lia)) as RDz.
        assert (RTz : rng RNG (SHB + (DCTX + 30104) / 8) 1).
        { unfold fk_held in RDS. eapply rng_sub'; [exact RDS|]. unfold shspan. rewrite shad_div. unfold ASHOFF. clear - RD8. Z.div_mod_to_equations. lia. }
        fk_hold UD.
        zstep.                                           (* [comment removed for export] *)
        clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
        zstep. if_false.                                 (* [comment removed for export] *)
        zstep.                                           (* [comment removed for export] *)
        zstep. rewrite (sx32w_small 0) by (clear; lia).  (* [comment removed for export] *)
        clear H5C.
        zstep. zstep. if_true.                           (* [comment removed for export] *)
        zstep. zstep.                                    (* [comment removed for export] *)
        zstep. zstep.                                    (* [comment removed for export] *)
        replace (DST + tot + res) with (DST + (tot + res)) by (clear; lia).
        pose proof (munch_refl [(SPA + 368, SPA + 376)] m1) as MU2. pose proof (wmono_refl bsegs m1) as WM2.
        zstep.                                           (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
        zstep.
        try (let w := getreg 24 in replace w with (Z_to_bv 64 (CAP - (tot + res))) by (apply Z_to_bv_eqm; rewrite ?Zminus_mod_idemp_l, ?Z.mod_small; clear - RT RRC RC40 RRES; lia)).
        zstep. zstep.
        unfold fk_held in DI. lazymatch goal with MIc : mem_inv bsegs m2 |- _ => pose proof (dinv_frame m1 m2 tot (tot + res) (SPA + 368) (SPA + 376) _ _ _ _ _ _ _ DI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) MU2 WM2 MIc FRA) as DI2 end.
        unfold fk_held in ACC.
        assert (ACC2 : forall r, dmulti src off' sz' (CAP - (tot + res)) (tot + res) r -> decompress_ok src size CAP r).
        { intros r D. apply ACC. apply STEP. replace (CAP - tot - res) with (CAP - (tot + res)) by (clear; lia). exact D. }
        assert (AI2 : AINV m2 off' sz' (tot + res)).
        { split; [exact DI2|]. split; [clear - RO1 ROFF; lia|]. split; [exact RO2|]. split; [clear - RSZ'; lia|]. split; [clear - RT RRC RRES; lia| exact ACC2]. }
        assert (RSZ2 : 0 <= sz' < 18446744073709551616) by (clear - RSZ' RSZ ROFF N40 NLEN; lia).
        zstep. if_cases KS; zify_cond KS.
        * unfold fk_held in KA.
          eapply (p_top m2 off' sz' (tot + res)); [exact AI2|]. intros. eapply KA; [clear - RSZ'; lia| exact AI2].
        * zstep. eapply (p_exit m2 sz' (tot + res)); [exact DI2| exact RSZ2| clear - RT RRC RRES; lia|].
          intros E0. apply ACC2. rewrite E0. apply DM_end.
  Qed.

  (* [comment removed for export] *)
  Lemma p_res0 : forall m1 off sz tot res (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word),
    DINV m1 tot -> 0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x20 = Z_to_bv 64 sz' /\ x26 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31 : word), sz' < sz -> AINV m' off' sz' tot' ->
        evtF bsegs RNG POST (LHst m' off' sz' tot' y1 y7 y10 y12 y13 y14 y19 y25 y27 y29 y31)) ->
    evtF bsegs RNG POST (STpc 0x84ee4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 res) x20 (Z_to_bv 64 DCTX)
                              (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 (-72)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31
           DI ROFF RSZ RT RRES ACC SUCC KA.
    (* [comment removed for export] *)
    eapply (p_res m1 off sz tot res); eassumption.
  Qed.
End DM.
End CANSEC1.
