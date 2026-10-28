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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
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

  Ltac cells_words cs :=
    lazymatch cs with
    | nil => constr:(@nil word)
    | C8 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    | C4 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    end.
  (* [comment removed for export] *)
  Ltac dl_chk mm p UDx RDSx DG :=
    let RDz := fresh "RDz" in let RTz := fresh "RTz" in
    pose proof (dl_sh_rd0s mm DCTX 95992 p UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
    pose proof (dl_sh_rng1 RNG DCTX p RDSx (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz;
    zstep; clear RDz RTz;
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity; try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity;
    zstep; if_false.
  (* [comment removed for export] *)
  Ltac dl_kx_gen :=
    repeat match goal with |- context [bv_unsigned (ev ?E ?j)] => let c := fresh "c" in set (c := bv_unsigned (ev E j)) in *; clearbody c end;
    repeat match goal with |- context [ev ?E ?j] => let w := fresh "kw" in set (w := ev E j) in *; clearbody w end.


  (* [comment removed for export] *)
  Hypothesis PCMP : forall m1 hufv lev wsv litSize litCSize lhSize four ty dha (xra x5 x7 x17 xs8 xs10 x28 x29 x30 x31 : word),
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> (DST = 0 -> litSize = 0) ->
    (four = 0 \/ (four = 1 /\ 6 <= litSize)) -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) ->
    evtF bsegs RNG POST (ST 0x87a90 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) x17 (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty)
                           (Z_to_bv 64 (lhSize + litCSize)) xs8 dha xs10 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma dl_cchk : forall m1 hufv lev wsv litSize litCSize lhSize four ty dha xra x7 x17 xs7 xs8 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    3 <= lhSize <= 5 -> 0 <= litCSize < 2^32 -> 0 <= litSize < 2^32 -> (DST = 0 -> litSize = 0) ->
    (four = 0 \/ four = 1) -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) ->
    evtF bsegs RNG POST (ST 0x87a6c m1 xra (Z_to_bv 64 (2^64 - 70)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) x17 (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty)
                           xs7 xs8 dha xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LCR LSR DNL FOUR TY. dl_open CTX.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID ARS AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    zstep; if_cases KB; zify_cond KB.                          (* [comment removed for export] *)
    { eapply (dl_e20 m1 hufv lev wsv); [exact I| exact KEEP]. }
    zstep. zstep.                                              (* [comment removed for export] *)
    set (a7v := Z.land four (Z.b2z (litSize <? 6))).
    assert (A7 : a7v = (if (four =? 1) && (litSize <? 6) then 1 else 0)%bool).
    { subst a7v. destruct FOUR as [-> | ->]; destruct (litSize <? 6); reflexivity. }
    clearbody a7v.
    zstep; if_cases KF; zify_cond KF.                          (* [comment removed for export] *)
    2:{ (* [comment removed for export] *)
        zstep. zstep. replace (Z_to_bv 64 (-24)) with (Z_to_bv 64 (2^64 - 24)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (dl_ret m1 hufv lev wsv (2^64 - 24)); [exact I| clear; lia| exact KEEP| left; reflexivity]. }
    assert (FOUR6 : four = 0 \/ (four = 1 /\ 6 <= litSize)).
    { destruct FOUR as [F0|F1]; [left; exact F0| right; split; [exact F1|]]. subst four. cbn [Z.eqb Pos.eqb andb] in A7.
      destruct (Z.ltb_spec litSize 6); [exfalso; clear - A7 KF; lia| assumption]. }
    clear A7 KF.
    zstep. zstep; if_cases KS; zify_cond KS.                   (* [comment removed for export] *)
    { eapply (dl_e20 m1 hufv lev wsv); [exact I| exact KEEP]. }
    zstep; if_cases KC; zify_cond KC.                          (* [comment removed for export] *)
    { eapply (dl_ret m1 hufv lev wsv (2^64 - 70)); [exact I| clear; lia| exact KEEP| left; reflexivity]. }
    eapply (PCMP m1 hufv lev wsv litSize litCSize lhSize four ty dha);
      [exact I| exact ISFv| exact KEEP| exact HW| exact LHR| clear - LCR; lia| clear - KS LHR LCR; lia| clear - LSR KB KC CAP0 BSM; lia| exact DNL| exact FOUR6| exact TY].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_cz : forall m1 hufv lev wsv litSize litCSize lhSize four ty dha xra x7 x17 xs7 xs8 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    3 <= lhSize <= 5 -> 0 <= litCSize < 2^32 -> 0 <= litSize < 2^32 -> DST = 0 ->
    (four = 0 \/ four = 1) -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) ->
    evtF bsegs RNG POST (ST 0x87a68 m1 xra (Z_to_bv 64 (2^64 - 70)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) x17 (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty)
                           xs7 xs8 dha xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LCR LSR D0 FOUR TY. dl_open CTX.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID ARS AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    zstep; if_cases KZ; zify_cond KZ.                          (* [comment removed for export] *)
    { eapply (dl_ret m1 hufv lev wsv (2^64 - 70)); [exact I| clear; lia| exact KEEP| left; reflexivity]. }
    eapply (dl_cchk m1 hufv lev wsv litSize litCSize lhSize four ty dha);
      [exact I| exact ISFv| exact KEEP| exact HW| exact LHR| exact LCR| exact LSR| intros _; clear - KZ LSR; lia| exact FOUR| exact TY].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_comp1 : forall m1 hufv lev wsv ty ews xra x5 x7 x17 xs2 xs3 xs4 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    5 <= zlen src -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) -> ews = Z.min (fh_bsmax h) CAP ->
    evtF bsegs RNG POST (ST 0x87700 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 (Znth 0 src))
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 ews) x17 xs2 xs3 xs4 (Z_to_bv 64 ty) xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW S5 TY EWS. subst ews. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (NZ : 0 < zlen src) by (clear - S5; lia).
    pose proof (US NZ) as USv. pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    pose proof (proj2 H5) as L5. destruct H5 as [H5C _]. h5_open wsv L5.
    set (sb0 := Znth 0 src) in *.
    assert (B0R : 0 <= sb0 < 256) by (subst sb0; rewrite Forall_forall in FBY; apply FBY; unfold Znth; apply nth_In; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (clear; lia); clear - S5; lia).
    (* [comment removed for export] *)
    clear PTRS EHUF EWK FP H3 XB BUF STK FRA MU WM AH FFR UB ARO AZS US.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    fk_hold DLI. fk_hold KEEP. fk_hold HW. fk_hold DNULL. fk_hold DNN. fk_hold ARS. fk_hold TY.
    kx_autoFLAx [KAUnp LSRC 5; KAApp LSRC 5; KAUnp DCTX 95992] [0x87a68; 0x87a6c] 80%nat
              [KZRange LSRC 6443008 (2^47 - 131072); KZRange DCTX 6443008 (2^47 - 95992); KZAlign DCTX 8; KZRange sb0 0 255]
              [(LSRC, 5); (DCTX + 30096, 276)] [(LSRC, 5); (DCTX + 30096, 276)].
    all: kx_read_ranges.
    all: try kx_mem.
    (* [comment removed for export] *)
    all: repeat match goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SLTU ?a ?b))] =>
           let f := fresh "bit" in let F := fresh "BIT" in
           set (f := bv_unsigned (edenot E (EAlu ALU_SLTU a b))) in *;
           assert (F : f = 0 \/ f = 1) by (subst f; cbn [edenot]; rewrite u_sltu64; destruct (_ <? _); [right| left]; reflexivity);
           clearbody f end.
    all: kx_abs.
    all: dl_kx_gen.
    all: repeat match goal with H : context [ev ?E _] |- _ => clear H end.
    all: clear KXA KXRD KXK KXMI; clear KXE.
    all: unfold fk_held in DLI, KEEP, HW, DNN, TY.
    all: repeat match goal with |- context [?e mod 2 ^ 64] =>
           rewrite (Z.mod_small e (2^64)) by (repeat match goal with H : 0 <= _ <= 255 |- _ => revert H end; clear; intros; lia) end.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x87a68) _ _ _ _) =>
             assert (D0 : DST = 0) by (match goal with H : DST mod 2 ^ 64 = 0 |- _ =>
               clear - H DNN B0D DCB CAP0 B1H; destruct (Z.eq_dec DST 0) as [Hd|Hd]; [exact Hd| exfalso; rewrite (Z.mod_small DST (2^64)) in H by lia; lia] end);
             eapply (dl_cz m1 hufv lev _ _ _ _ _ ty);
               [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia
               | repeat match goal with H : 0 <= _ <= 255 |- _ => revert H end; clear; intros; Z.div_mod_to_equations; lia
               | repeat match goal with H : 0 <= _ <= 255 |- _ => revert H end; clear; intros; Z.div_mod_to_equations; lia
               | exact D0| first [assumption| right; reflexivity]| exact TY]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x87a6c) _ _ _ _) =>
             assert (D1 : DST <> 0) by (match goal with H : DST mod 2 ^ 64 <> 0 |- _ => intros D0; apply H; rewrite D0; reflexivity end);
             eapply (dl_cchk m1 hufv lev _ _ _ _ _ ty);
               [exact DLI| exact ISFv| exact KEEP| exact HW| clear; lia
               | repeat match goal with H : 0 <= _ <= 255 |- _ => revert H end; clear; intros; Z.div_mod_to_equations; lia
               | repeat match goal with H : 0 <= _ <= 255 |- _ => revert H end; clear; intros; Z.div_mod_to_equations; lia
               | intros D0; exfalso; exact (D1 D0)| first [assumption| right; reflexivity]| exact TY]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma dl_sx32_nz_mod : forall w : word, bv_unsigned (Mem.sx32 w) <> 0 -> bv_unsigned w mod 4294967296 <> 0.
  Proof.
    intros w H E. apply H. unfold Mem.sx32. rewrite unsigned_lit_wrap, swrap32_eq.
    pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    clear - E R. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_comp : forall m1 hufv lev wsv ty xra x7 xa6 xa7 xs2 xs3 xs4 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    2 <= zlen src -> (ty = 2 \/ ty = 3) ->
    evtF bsegs RNG POST (ST 0x876ac m1 xra (Z_to_bv 64 (SHB + LSRC / 8)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 (Znth 0 src))
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 ty) xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW S2 TYB. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (NZ : 0 < zlen src) by (clear - S2; lia).
    pose proof (US NZ) as USv. pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    clear PTRS EHUF EWK FP H5 XB BUF STK FRA MU WM AH FFR UB ARO AZS US.
    clear AFP AH0 ASH ART0 KHI RSTK RI RFS BOT SPT SP16 RSTKT LBH ARD AHD AID AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    fk_hold DLI. fk_hold KEEP. fk_hold DNULL. fk_hold DNN. fk_hold ARS.
    (* [comment removed for export] *)
    zstep. zstep; if_cases K2; zify_cond K2;                   (* [comment removed for export] *)
      [ assert (TY : ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) by (left; exact K2)
      | zstep; zstep; zstep; dl_chk m1 (DCTX + 30000) UD RDS DG;  (* [comment removed for export] *)
        zstep;                                                 (* [comment removed for export] *)
        zstep; if_cases K3; zify_cond K3;                      (* [comment removed for export] *)
        [ zstep; zstep; replace (Z_to_bv 64 (-30)) with (Z_to_bv 64 (2^64 - 30)) by (apply Z_to_bv_eqm; reflexivity);
          unfold fk_held in DLI, KEEP; eapply (dl_ret m1 hufv lev wsv (2^64 - 30)); [exact DLI| clear; lia| exact KEEP| left; reflexivity]
        | assert (TY : ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) by (right; split; [clear - TYB K2; lia| apply dl_sx32_nz_mod; exact K3]) ] ].
    all: clear H3 TYB; fk_hold TY.
    all: zstep; zstep; if_cases KS; zify_cond KS;              (* [comment removed for export] *)
      [ unfold fk_held in DLI, KEEP; eapply (dl_e20 m1 hufv lev wsv); [exact DLI| exact KEEP] |].
    (* [comment removed for export] *)
    all: kx_autoFLAx [KAUnp LSRC 4; KAApp LSRC 4; KAShp (SHB + LSRC / 8) LSRC] [0x876f4] 40%nat
              [KZRange LSRC 6443008 (2^47 - 131072)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_mem.
    all: kx_abs.
    all: dl_kx_gen.
    all: repeat match goal with H : context [ev ?E _] |- _ => clear H end.
    all: clear KXA KXRD KXK KXMI; clear KXE.
    all: unfold fk_held in DLI, KEEP, TY, DNN, DNULL; assert (CAPH : CAP < 2^47) by (clear - DNN DNULL B0D DCB B1H CAP0; lia).
    all: zstep; zstep; if_cases KM; zify_cond KM; [| zstep];   (* [comment removed for export] *)
      eapply (dl_hdr_comp1 m1 hufv lev wsv ty); (exact DLI || exact ISFv || exact KEEP || exact HW || exact KS || exact TY || (clear - KM; lia)).
  Qed.
End DL.
End CANSEC1.
