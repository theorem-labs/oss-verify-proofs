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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

Lemma dl_ffr_pres_mono_nil1 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.
Lemma dl_stk_empty : forall (m : amem) A, 0 <= A -> A <= 2^64 -> stk bsegs m A A.
Proof. intros m A H0 H1. split; [exact H0|]. split; [exact H1|]. intros a Ha. lia. Qed.
Lemma dl_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
Qed.

(* [comment removed for export] *)
Lemma dl_sh_rd0s : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
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
Lemma dl_sh_rng1 : forall RNG DCTX p, rng RNG (shad DCTX) (shspan DCTX 95992) -> DCTX mod 8 = 0 -> DCTX <= p -> p + 8 <= DCTX + 95992 ->
  rng RNG (Z.shiftr p 3 + SHB) 1.
Proof.
  intros RNG DCTX p R A H1 H2. eapply rng_sub'; [exact R|]. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  unfold shspan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Lemma dl_ffr_pres_weaken : forall W W' LB (m m' : amem), ffr_pres W LB m m' -> sub_fp W W' -> ffr_pres W' LB m m'.
Proof.
  intros W W' LB m m' H HS. unfold ffr_pres in *. eapply magree_mono; [exact H|].
  intros a [[HF HO]|HX]; [left; split; [exact HF| apply HS; exact HO]| right; exact HX].
Qed.
Lemma dl_outside_In : forall W a x y, outside W a -> In (x, y) W -> ~ (x <= a < y).
Proof.
  induction W as [|[u v] W IH]; intros a x y OUT HI; cbn in *; [destruct HI|].
  destruct OUT as [O1 O2]. destruct HI as [E|HI]; [injection E; intros -> ->; lia| exact (IH _ _ _ O2 HI)].
Qed.
(* [comment removed for export] *)
Lemma dl_ffr_pres_appw : forall AI L RNG st LB (m m5 : amem) (W Wr Wa : list (Z * Z)),
  AHEAP AI L RNG st LB m -> ablkLB LB ->
  Forall (fun iv => fst iv <= snd iv /\ ATOP <= fst iv /\ snd iv <= 2^47) Wa ->
  Forall (fun iv => (exists A Bq, ablk A Bq /\ A <= fst iv /\ snd iv <= Bq) /\ fst iv <= snd iv /\ In iv W) Wr ->
  munch (Wr ++ Wa) m m5 -> wmono bsegs m m5 -> ffr_pres W LB m m5.
Proof.
  intros AI L RNG st LB m m5 W Wr Wa AH LBH HWa HWr MU WM.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
  intros a [((cls & FA & fn & Hin & Ha) & OUT)|(a' & (cls & FA & fn & Hin & Ha') & ->)].
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    rewrite fk_outside_app. split.
    + clear MU. induction HWr as [|[x y] Wr [_ [Hle HI]] HWr IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      exact (dl_outside_In W a x y OUT HI).
    + clear MU. induction HWa as [|[x y] Wa (Hle & Hx & Hy) HWa IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in Hle, Hx, Hy. clear - Ha B3 Hx ATR. lia.
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A3. pose proof (fk_ablk_lits _ _ A3) as A4.
    rewrite fk_outside_app. split.
    + clear MU. induction HWr as [|[x y] Wr [(A & Bq & AB & HA & HB) [Hle _]] HWr IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in HA, HB, Hle. pose proof (fk_ablk_lits _ _ AB) as ABL. pose proof (ablk_disj_band _ _ AB) as ABD.
      rewrite shad_div. unfold ASHOFF, AIMG_HI, KLS in *. clear - Ha' A4 ABL ABD HA HB Hle ATR B3. Z.div_mod_to_equations. lia.
    + clear MU. induction HWa as [|[x y] Wa (Hle & Hx & Hy) HWa IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in Hle, Hx, Hy. rewrite shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha' A4 Hx Hy Hle ATR B3. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma dl_ffr_pres_app1 : forall AI L RNG st LB (m m5 : amem) (W Wl : list (Z * Z)),
  AHEAP AI L RNG st LB m -> ablkLB LB ->
  Forall (fun iv => fst iv <= snd iv /\ ((ATOP <= fst iv /\ snd iv <= 2^47)
                                     \/ ((exists A Bq, ablk A Bq /\ A <= fst iv /\ snd iv <= Bq) /\ (exists jv, In jv W /\ fst jv <= fst iv /\ snd iv <= snd jv)))) Wl ->
  munch Wl m m5 -> wmono bsegs m m5 -> ffr_pres W LB m m5.
Proof.
  intros AI L RNG st LB m m5 W Wl AH LBH HW MU WM.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
  intros a [((cls & FA & fn & Hin & Ha) & OUT)|(a' & (cls & FA & fn & Hin & Ha') & ->)].
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    clear MU. induction HW as [|[x y] Wl [Hle [[Hx Hy]|[_ ([u v] & HI & Hu & Hv)]]] HW IH]; cbn [outside]; [exact I| |]; (split; [| exact IH]); cbn [fst snd] in *.
    + clear - Ha B3 Hx ATR. lia.
    + pose proof (dl_outside_In W a u v OUT HI) as X. clear - X Hu Hv. lia.
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A3. pose proof (fk_ablk_lits _ _ A3) as A4.
    clear MU. induction HW as [|[x y] Wl [Hle [[Hx Hy]|[(A & Bq & AB & HA & HB) _]]] HW IH]; cbn [outside]; [exact I| |]; (split; [| exact IH]); cbn [fst snd] in *.
    + rewrite shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha' A4 Hx Hy Hle ATR B3. Z.div_mod_to_equations. lia.
    + pose proof (fk_ablk_lits _ _ AB) as ABL. pose proof (ablk_disj_band _ _ AB) as ABD.
      rewrite shad_div. unfold ASHOFF, AIMG_HI, KLS in *. clear - Ha' A4 ABL ABD HA HB Hle ATR B3. Z.div_mod_to_equations. lia.
Qed.
Lemma dl_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) A B. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.
Lemma dl_bytes_at_slice : forall (m : amem) a (bs : list byte) off k,
  bytes_at bsegs m a bs -> (off + k <= length bs)%nat -> bytes_at bsegs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m a bs off k H Hk. rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma dl_wupd_length : forall ws i v, length (wupd ws i v) = length ws.
Proof. induction ws as [|w ws IH]; intros [|i] v; cbn; [reflexivity| reflexivity| reflexivity| f_equal; apply IH]. Qed.
Lemma dl_art_of_aheap : forall AI L RNG st LB m, AHEAP AI L RNG st LB m -> art m.
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & RIC & REAL & SHB' & _ & INI & LAY & _). unfold art. repeat (split; [assumption|]). assumption.
Qed.

Section DL.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
            (SPV lo DCTX DST CAP B0 B1 LSRC : Z) (src : list Z) (h : frame_header) (llt mlt oft pcs dsz bt stg fe : word) (ws : list word).

  (* [comment removed for export] *)
  Definition DLCTX : Prop :=
    (4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ DCTX mod 8 = 0 /\ 0 <= zlen src <= 131072 /\ 4096 <= LSRC /\ LSRC + zlen src < 2^47
     /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\ (DST = 0 -> CAP = 0) /\ (DST <> 0 -> 4096 <= B0)
     /\ 4096 <= lo /\ lo <= SPV - 6096 /\ SPV < 2^47)
    /\ ((DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (B1 <= lo \/ SPV <= B0) /\ (LSRC + zlen src <= lo \/ SPV <= LSRC)
        /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\ (B1 <= LSRC \/ LSRC + zlen src <= B0) /\ (LSRC + zlen src <= DCTX \/ DCTX + 95992 <= LSRC))
    /\ (Forall (fun c => 0 <= c < 256) src /\ 0 <= fh_bsmax h <= 131072 /\ wnth ws H5_isFrameDecompression = Z_to_bv 64 1)
    /\ (afpre AI rng_fs L RNG st LB m0 lo SPV 4 /\ tp = Z_to_bv 64 ATP
        /\ areg RNG m0 DCTX 95992 /\ ahull RNG m0 DCTX 95992 /\ ainblk LB DCTX 95992
        /\ areg RNG m0 LSRC (zlen src) /\ (0 < zlen src -> ahull RNG m0 LSRC (zlen src)) /\ (0 < zlen src -> ainimg LB LSRC (zlen src))
        /\ (B0 < B1 -> areg RNG m0 B0 (B1 - B0) /\ ahull RNG m0 B0 (B1 - B0) /\ ainblk LB B0 (B1 - B0))).
  Hypothesis CTX : DLCTX.

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

  (* [comment removed for export] *)
  Definition DLB (hufv lev : word) (wsv : list word) (m1 : amem) : Prop :=
    dctx_ptrs bsegs m1 DCTX llt mlt oft hufv
    /\ stk bsegs m1 (DCTX + 10296) (DCTX + 26684) /\ stk bsegs m1 (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells bsegs m1 (DCTX + 29928) (zfh_cells h)
    /\ dctx_h3 bsegs m1 DCTX pcs dsz bt stg lev fe
    /\ dctx_h5 bsegs m1 DCTX wsv
    /\ stk bsegs m1 (DCTX + 30372) (DCTX + 95940)
    /\ bytes_at bsegs m1 LSRC (map (Z_to_bv 8) src)
    /\ stk bsegs m1 B0 B1
    /\ stk bsegs m1 lo (SPV + -96)
    /\ rw_cells bsegs m1 (SPV + -96) DSAVED
    /\ mem_inv bsegs m1 /\ munch (FOOT ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1
    /\ AHEAP AI L RNG st LB m1 /\ ffr_pres FFR6 LB m0 m1
    /\ unpoisoned m1 DCTX (DCTX + 95992) /\ (0 < zlen src -> unpoisoned m1 LSRC (LSRC + zlen src)) /\ (B0 < B1 -> unpoisoned m1 B0 B1)
    /\ aro_client RNG m1 /\ azstk RNG m1 lo SPV.

  Ltac dl_open C :=
    pose proof C as ((DCL & DCH & DCA & SLEN & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH)
                     & (OFFD & OFFB & OFFSRC & BD & BSRC & SRCD) & (FBY & BSM & ISF)
                     & (AFP & TP & ARD & AHD & AID & ARS & AHS & AIS & ADST));
    pose proof AFP as (AH0 & ASH & ART0 & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
  Ltac open_dlb I := destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS);
                     unfold dctx_ptrs in PTRS; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  (* [comment removed for export] *)
  Lemma dl_ret : forall m1 hufv lev wsv r xra x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> 0 <= r < 2^64 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    (zd_is_error r = true
     \/ (1 <= r <= zlen src /\ HUFINVw m1 DCTX hufv lev /\ declit_placed DCTX DST CAP LSRC (zlen src) wsv)) ->
    evtF bsegs RNG POST (ST 0x87568 m1 xra (Z_to_bv 64 r) x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR KEEP RES. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold RES. fk_hold MU. fk_hold FFR.
    zstep.                                                 (* [comment removed for export] *)
    do 12 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_declit_postA.
    unfold fk_held in *.
    do 14 eexists. exists m1, r, hufv, lev, wsv. split; [reflexivity|].
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [eapply stk_merge; [exact STK| replace SPV with (SPV + -96 + Z.of_nat 96) at 2 by (clear; lia); exact FRAS| clear - LOS; lia]|].
    split; [exact FFR|]. split; [exact AH|]. split; [exact BUF|].
    split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact H3|]. split; [exact H5|]. split; [exact KEEP|].
    split; [exact XB|]. split; [exact HR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_e20 : forall m1 hufv lev wsv xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    evtF bsegs RNG POST (ST 0x87564 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP. pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _).
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
    eapply (dl_ret m1 hufv lev wsv (2^64 - 20)); [exact I| clear; lia| exact KEEP| left; reflexivity].
  Qed.
End DL.
End CANSEC1.
