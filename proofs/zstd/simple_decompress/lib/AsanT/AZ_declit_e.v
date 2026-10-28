(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx AZ_declit_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
      | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
      | H : rw_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
      | H : ro_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
      | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
      | _ => (* [comment removed for export] *)
          let A' := eval lazy in A in
          lazymatch A' with
          | Z0 => idtac | Zpos _ => idtac
          | _ => fail 0 "kx_rd_at: no chunk hypothesis justifies the region at" A
          end;
          apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
      end
  end.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dl_src_byte1 : forall (m : amem) SRC (src : list Z) i,
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> 0 <= i < zlen src -> bytes_at bsegs m (SRC + i) [Z_to_bv 8 (Znth i src)].
Proof.
  intros m SRC src i SB Hi.
  assert (NTH1 : forall (l : list Z) (n : nat) (d : Z), (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l d]).
  { clear. induction l as [|c l IH]; intros [|n] d Hn; cbn in *; try lia; [reflexivity | apply IH; lia]. }
  pose proof (zd_src_skipn bsegs m SRC src i SB ltac:(lia)) as B.
  rewrite <- (firstn_skipn 1 (skipn (Z.to_nat i) src)) in B. rewrite map_app in B.
  apply (proj1 (bytes_at_app bsegs m (SRC + i) _ _)) in B. destruct B as [B _].
  rewrite (NTH1 src (Z.to_nat i) 0) in B by lia. exact B.
Qed.

(* [comment removed for export] *)
Lemma dl_byte_range : forall (src : list Z) i, Forall (fun c => 0 <= c < 256) src -> 0 <= i < zlen src -> 0 <= Znth i src < 256.
Proof.
  intros src i FBY Hi. rewrite Forall_forall in FBY. apply FBY. unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
Qed.

Section DL.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
            (SPV lo DCTX DST CAP B0 B1 LSRC : Z) (src : list Z) (h : frame_header) (llt mlt oft pcs dsz bt stg fe : word) (ws : list word).

  Hypothesis CTX : AZ_declit_a.DLCTX AI rng_fs L RNG st LB tp m0 SPV lo DCTX DST CAP B0 B1 LSRC src h ws.

  Notation FOOT := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                    (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV - 6096, SPV)].
  Notation FFR6 := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                    (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940)].
  Notation POST := (zd_declit_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP B0 B1 LSRC (zlen src)
                                    llt mlt oft pcs dsz bt stg fe ws lo m0).
  Notation DSAVED := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 SHB) xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation DLB := (AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe).
  Ltac dl_open C :=
    pose proof C as ((DCL & DCH & DCA & SLEN & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH)
                     & (OFFD & OFFB & OFFSRC & BD & BSRC & SRCD) & (FBY & BSM & ISF)
                     & (AFP & TP & ARD & AHD & AID & ARS & AHS & AIS & ADST));
    pose proof AFP as (AH0 & ASH & ART0 & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
  Ltac open_dlb I := unfold AZ_declit_a.DLB in I; destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS);
                     unfold dctx_ptrs in PTRS; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  Notation dl_ret := (AZ_declit_a.dl_ret AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Notation dl_e20 := (AZ_declit_a.dl_e20 AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Ltac hlia := unfold fk_held in *; lia.

  (* [comment removed for export] *)
  Hypothesis PRAW : forall m1 hufv lev wsv litSize lhSize (xra x5 x7 xa6 xs2 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    1 <= lhSize <= 3 -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> (DST = 0 -> litSize = 0) ->
    evtF bsegs RNG POST (ST 0x878b4 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           xa6 (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) xs2 (Z_to_bv 64 lhSize) xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma dl_rchk : forall m1 hufv lev wsv litSize lhSize xra x7 xa6 xs2 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    1 <= lhSize <= 3 -> 0 <= litSize < 2^32 -> (DST = 0 -> litSize = 0) ->
    evtF bsegs RNG POST (ST 0x878ac m1 xra (Z_to_bv 64 (2^64 - 70)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           xa6 (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) xs2 (Z_to_bv 64 lhSize) xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LSR DNL. dl_open CTX.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID ARS AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    zstep. if_cases KB; zify_cond KB.                          (* [comment removed for export] *)
    { eapply (dl_e20 m1 hufv lev wsv); [exact I| exact KEEP]. }
    zstep. if_cases KC; zify_cond KC.                          (* [comment removed for export] *)
    { eapply (dl_ret m1 hufv lev wsv (2^64 - 70)); [exact I| clear; lia| exact KEEP| left; reflexivity]. }
    eapply (PRAW m1 hufv lev wsv litSize lhSize); [exact I| exact ISFv| exact KEEP| exact HW| exact LHR| clear - LSR KB KC CAP0 BSM; lia| exact DNL].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_rz : forall m1 hufv lev wsv litSize lhSize xra x7 xa6 xs2 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    1 <= lhSize <= 3 -> 0 <= litSize < 2^32 -> DST = 0 ->
    evtF bsegs RNG POST (ST 0x878a8 m1 xra (Z_to_bv 64 (2^64 - 70)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           xa6 (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) xs2 (Z_to_bv 64 lhSize) xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LSR D0. dl_open CTX.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID ARS AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    zstep. if_cases KZ; zify_cond KZ.                          (* [comment removed for export] *)
    { eapply (dl_ret m1 hufv lev wsv (2^64 - 70)); [exact I| clear; lia| exact KEEP| left; reflexivity]. }
    eapply (dl_rchk m1 hufv lev wsv litSize lhSize); [exact I| exact ISFv| exact KEEP| exact HW| exact LHR| exact LSR| intros _; clear - KZ LSR; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_raw2 : forall m1 hufv lev wsv lhlv xra x7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    2 <= zlen src -> 0 <= lhlv < 2^64 ->
    evtF bsegs RNG POST (ST 0x87624 m1 xra (Z_to_bv 64 (SHB + LSRC / 8)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 (Znth 0 src))
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 lhlv) (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW S2 LHLR. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (NZ : 0 < zlen src) by (clear - S2; lia).
    pose proof (US NZ) as USv. pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    (* [comment removed for export] *)
    clear PTRS EHUF EWK FP H3 H5 XB BUF STK FRA MU WM AH FFR UD UB ARO AZS US.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    zstep. zstep. if_cases KA; zify_cond KA.                   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      fk_hold DLI. fk_hold KEEP. fk_hold HW. fk_hold DNULL. fk_hold DNN. fk_hold ARS.
      kx_autoFA [KAUnp LSRC 2; KAApp LSRC 2; KAShp (SHB + LSRC / 8) LSRC] [0x878a8; 0x878ac] 40%nat
                [KZRange LSRC 6443008 (2^47 - 131072)] [(LSRC, 2)] [(LSRC, 2)].
      all: kx_read_ranges.
      all: try kx_mem.
      all: kx_abs.
      all: repeat match goal with |- context [bv_unsigned (ev ?E ?j)] => let c := fresh "c" in set (c := bv_unsigned (ev E j)) in *; clearbody c end.
      all: repeat match goal with |- context [ev ?E ?j] => let w := fresh "kw" in set (w := ev E j) in *; clearbody w end.
      all: clear KXA KXRD KXK KXMI; clear KXE.
      all: match goal with |- context [Z_to_bv 64 (?e mod 2 ^ 64 / 16)] => rewrite (Z.mod_small e (2^64)) by (clear - KXRR KXRR0; lia) end.
      all: unfold fk_held in DLI, KEEP, HW, DNN.
      { (* [comment removed for export] *)
        assert (D0 : DST = 0) by (first [exact KXBR | clear - KXBR DNN B0D DCB CAP0 B1H; destruct (Z.eq_dec DST 0) as [Hd|Hd]; [exact Hd| exfalso; rewrite Z.mod_small in KXBR by lia; lia]]).
        eapply (dl_rz m1 hufv lev wsv _ 2); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| clear - KXRR KXRR0; Z.div_mod_to_equations; lia| exact D0]. }
      assert (D1 : DST <> 0) by (intros D0; apply KXBR; rewrite D0; reflexivity).
      eapply (dl_rchk m1 hufv lev wsv _ 2); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| clear - KXRR KXRR0; Z.div_mod_to_equations; lia| intros D0; exfalso; exact (D1 D0)].
    - zstep. zstep. if_cases KB; zify_cond KB.                 (* [comment removed for export] *)
      + (* [comment removed for export] *)
        pose proof (dl_byte_range src 0 FBY ltac:(clear - S2; lia)) as B0R.
        zstep. zstep. zstep.                                   (* [comment removed for export] *)
        replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (2^64 - 70)) by (apply Z_to_bv_eqm; reflexivity).
        unfold fk_held in DLI, KEEP, HW, DNN.
        zstep; if_cases KD; zify_cond KD.                      (* [comment removed for export] *)
        * eapply (dl_rchk m1 hufv lev wsv _ 1); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| rewrite Z.shiftr_div_pow2 by (clear; lia); clear - B0R; Z.div_mod_to_equations; lia| intros D0; exfalso; clear - KD D0; lia].
        * eapply (dl_rz m1 hufv lev wsv _ 1); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| rewrite Z.shiftr_div_pow2 by (clear; lia); clear - B0R; Z.div_mod_to_equations; lia| clear - KD DNN B0D DCB CAP0 B1H; lia].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KS; zify_cond KS.              (* [comment removed for export] *)
        { unfold fk_held in DLI, KEEP. eapply (dl_e20 m1 hufv lev wsv); [exact DLI| exact KEEP]. }
        assert (S3 : 3 <= zlen src) by (clear - S2 KS; lia). clear KS.
        kx_autoFA [KAUnp LSRC 3; KAApp LSRC 3; KAShp (SHB + LSRC / 8) LSRC] [0x878a8; 0x878ac] 60%nat
                  [KZRange LSRC 6443008 (2^47 - 131072)] [(LSRC, 3)] [(LSRC, 3)].
        all: kx_read_ranges.
        all: try kx_mem.
        all: kx_abs.
        all: repeat match goal with |- context [bv_unsigned (ev ?E ?j)] => let c := fresh "c" in set (c := bv_unsigned (ev E j)) in *; clearbody c end.
        all: repeat match goal with |- context [ev ?E ?j] => let w := fresh "kw" in set (w := ev E j) in *; clearbody w end.
        all: clear KXA KXRD KXK KXMI; clear KXE.
        all: match goal with |- context [Z_to_bv 64 (?e mod 2 ^ 64 / 16)] => rewrite (Z.mod_small e (2^64)) by (clear - KXRR KXRR0 KXRR1; lia) end.
        all: unfold fk_held in DLI, KEEP, HW, DNN.
        { (* [comment removed for export] *)
          assert (D0 : DST = 0) by (first [exact KXBR | clear - KXBR DNN B0D DCB CAP0 B1H; destruct (Z.eq_dec DST 0) as [Hd|Hd]; [exact Hd| exfalso; rewrite Z.mod_small in KXBR by lia; lia]]).
          eapply (dl_rz m1 hufv lev wsv _ 3); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| clear - KXRR KXRR0 KXRR1; Z.div_mod_to_equations; lia| exact D0]. }
        assert (D1 : DST <> 0) by (intros D0; apply KXBR; rewrite D0; reflexivity).
        eapply (dl_rchk m1 hufv lev wsv _ 3); [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia| clear - KXRR KXRR0 KXRR1; Z.div_mod_to_equations; lia| intros D0; exfalso; exact (D1 D0)].
  Qed.

End DL.
End CANSEC1.
