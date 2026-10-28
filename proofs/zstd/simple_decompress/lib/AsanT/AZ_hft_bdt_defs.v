(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition bdA_hyps (RNG : footprint) (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z) : Prop :=
  5 <= tl <= 9
  /\ 0 <= maxSV <= 255
  /\ maxSV + 1 <= zlen norm
  /\ (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm)
  /\ pws norm (maxSV + 1) = 2^tl
  /\ 2 * (maxSV + 1) + 2^tl + 8 <= wlen
  /\ wlen < 2^32
  /\ 4096 <= DT
  /\ DT + 4 + 4 * 2^tl < 2^47
  /\ 4096 <= W
  /\ W + wlen < 2^47
  /\ 4096 <= NC
  /\ NC + 2 * zlen norm < 2^47
  /\ 4096 <= lo
  /\ lo <= SPV - 192
  /\ SPV < 2^47
  /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0   (* [comment removed for export] *)
  /\ (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT)
  /\ (W + wlen <= lo \/ SPV <= W)
  /\ (NC + 2 * zlen norm <= lo \/ SPV <= NC)
  /\ (DT + 4 + 4 * 2^tl <= W \/ W + wlen <= DT)
  /\ (DT + 4 + 4 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT)
  /\ (W + wlen <= NC \/ NC + 2 * zlen norm <= W)
  /\ ablk DT (DT + 4 + 4 * 2^tl)
  /\ rng RNG DT (4 + 4 * 2^tl)
  /\ rng RNG (shad DT) (shspan DT (4 + 4 * 2^tl))
  /\ ablk W (W + wlen)
  /\ rng RNG W wlen
  /\ rng RNG (shad W) (shspan W wlen)
  /\ rng RNG NC (2 * zlen norm)
  /\ rng RNG (shad NC) (shspan NC (2 * zlen norm))
  /\ KHIGH <= lo
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Lemma bdA_open : forall RNG SPV lo DT NC W wlen maxSV tl norm, bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm ->
  forall G : Prop, (5 <= tl <= 9 ->
    0 <= maxSV <= 255 ->
    maxSV + 1 <= zlen norm ->
    (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
    pws norm (maxSV + 1) = 2^tl ->
    2 * (maxSV + 1) + 2^tl + 8 <= wlen ->
    wlen < 2^32 ->
    4096 <= DT ->
    DT + 4 + 4 * 2^tl < 2^47 ->
    4096 <= W ->
    W + wlen < 2^47 ->
    4096 <= NC ->
    NC + 2 * zlen norm < 2^47 ->
    4096 <= lo ->
    lo <= SPV - 192 ->
    SPV < 2^47 ->
    DT mod 4 = 0 -> W mod 2 = 0 -> NC mod 2 = 0 ->
    (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT) ->
    (W + wlen <= lo \/ SPV <= W) ->
    (NC + 2 * zlen norm <= lo \/ SPV <= NC) ->
    (DT + 4 + 4 * 2^tl <= W \/ W + wlen <= DT) ->
    (DT + 4 + 4 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT) ->
    (W + wlen <= NC \/ NC + 2 * zlen norm <= W) ->
    ablk DT (DT + 4 + 4 * 2^tl) ->
    rng RNG DT (4 + 4 * 2^tl) ->
    rng RNG (shad DT) (shspan DT (4 + 4 * 2^tl)) ->
    ablk W (W + wlen) ->
    rng RNG W wlen ->
    rng RNG (shad W) (shspan W wlen) ->
    rng RNG NC (2 * zlen norm) ->
    rng RNG (shad NC) (shspan NC (2 * zlen norm)) ->
    KHIGH <= lo ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until norm. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31 & Y32 & Y33 & Y34 & Y35). eapply K; eassumption. Qed.
Ltac open_hy HY := apply (bdA_open _ _ _ _ _ _ _ _ _ _ HY); intros TLR MSVR NLEN NGE NSUM WLEN WLEN32 DTL DTH WL WH NCL NCH LO0 LOS SPR DTA WA NCA OFFDT OFFW OFFNC DTW DTNC WNC ABDT RDT RSDT ABW RW RSW RNC RSNC KLO RSTK RI.

(* [comment removed for export] *)
Definition BDA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : amem) (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z)
    (f8 f16 : word)   (* [comment removed for export] *)
    (h0 h1 : word) (tb sn sp : list Z) (m1 : amem) : Prop :=
  rw_cells bsegs m1 DT [C2 h0; C2 h1]
  /\ u8arr bsegs m1 (DT + 4) (map (Z_to_bv 8) tb)
  /\ zlen tb = 4 * 2^tl
  /\ Forall isbyte tb
  /\ u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn))
  /\ zlen sn = maxSV + 1
  /\ u8arr bsegs m1 (W + 2 * (maxSV + 1)) (map (Z_to_bv 8) sp)
  /\ zlen sp = wlen - 2 * (maxSV + 1)
  /\ Forall isbyte sp
  /\ bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ stk bsegs m1 lo (SPV + -144)
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1
  /\ wmono bsegs m m1
  /\ (exists j0, rw_cells bsegs m1 (SPV + -144) [CB 8 j0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 W); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Lemma BDA_open : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16 h0 h1 tb sn sp m1,
  BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16 h0 h1 tb sn sp m1 ->
  forall G : Prop, (forall j0, rw_cells bsegs m1 DT [C2 h0; C2 h1] ->
    u8arr bsegs m1 (DT + 4) (map (Z_to_bv 8) tb) ->
    zlen tb = 4 * 2^tl ->
    Forall isbyte tb ->
    u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn)) ->
    zlen sn = maxSV + 1 ->
    u8arr bsegs m1 (W + 2 * (maxSV + 1)) (map (Z_to_bv 8) sp) ->
    zlen sp = wlen - 2 * (maxSV + 1) ->
    Forall isbyte sp ->
    bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm)) ->
    stk bsegs m1 lo (SPV + -144) ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 ->
    wmono bsegs m m1 ->
    rw_cells bsegs m1 (SPV + -144) [CB 8 j0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 W); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & j0 & FR). eapply (K j0); eassumption. Qed.
Ltac open_bd I := apply (BDA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros j0 HDR CEL CLEN CBY SNX SNLEN SPRD SPLEN SPBY NCB STK MI MU WM FR.
(* [comment removed for export] *)
Lemma BDA_close : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16 h0 h1 tb sn sp m1 j0,
  rw_cells bsegs m1 DT [C2 h0; C2 h1] ->
  u8arr bsegs m1 (DT + 4) (map (Z_to_bv 8) tb) ->
  zlen tb = 4 * 2^tl ->
  Forall isbyte tb ->
  u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn)) ->
  zlen sn = maxSV + 1 ->
  u8arr bsegs m1 (W + 2 * (maxSV + 1)) (map (Z_to_bv 8) sp) ->
  zlen sp = wlen - 2 * (maxSV + 1) ->
  Forall isbyte sp ->
  bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm)) ->
  stk bsegs m1 lo (SPV + -144) ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 ->
  wmono bsegs m m1 ->
  rw_cells bsegs m1 (SPV + -144) [CB 8 j0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (2^tl)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 W); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16 h0 h1 tb sn sp m1.
Proof. intros. unfold BDA. repeat (split; [eassumption|]). eexists; eassumption. Qed.
Ltac close_bd := eapply BDA_close; eassumption.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

(* [comment removed for export] *)
Lemma bdA_size_rng : forall RNG SPV lo DT NC W wlen maxSV tl norm,
  bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm -> 32 <= 2^tl <= 512 /\ 16 <= 2^(tl - 1) <= 256 /\ 2^(tl - 1) * 2 = 2^tl.
Proof.
  intros until norm. intros HY. open_hy HY.
  assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
  assert (2^4 <= 2^(tl - 1)) by (apply Z.pow_le_mono_r; lia). assert (2^(tl - 1) <= 2^8) by (apply Z.pow_le_mono_r; lia).
  change (2^5) with 32 in *. change (2^9) with 512 in *. change (2^4) with 16 in *. change (2^8) with 256 in *.
  split; [lia|]. split; [lia|]. replace tl with (Z.succ (tl - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis UDT : unpoisoned m DT (DT + 4 + 4 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis ART0 : art m.
  Variables (f8 f16 : word).
  Notation BDm := (BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16).

  (* [comment removed for export] *)
  Lemma bd_bands : (DT + 4 + 4 * 2^tl + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (W + wlen + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= W)
                   /\ 0x10007fff8000 <= SPV - 192 /\ 0x625000 <= DT /\ 0x625000 <= W /\ DT + 4 + 4 * 2^tl + 8 <= 2^47 /\ W + wlen + 8 <= 2^47.
  Proof.
    open_hy HY. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABDT, ABW. unfold KHIGH in KLO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_unp_dtM : forall m1, munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 -> unpoisoned m1 DT (DT + 4 + 4 * 2^tl).
  Proof.
    intros m1 MU. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_unp_wM : forall m1, munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 -> unpoisoned m1 W (W + wlen).
  Proof.
    intros m1 MU. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_unp_ncM : forall m1, munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 -> unpoisoned m1 NC (NC + 2 * zlen norm).
  Proof.
    intros m1 MU. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8). pose proof UNC as (U0 & U1 & _).
    eapply unpoisoned_munch; [exact UNC | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_artM : forall m1, munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 -> wmono bsegs m m1 -> art m1.
  Proof.
    intros m1 MU WM. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply art_transport; [exact ART0| exact MU| exact WM|]. repeat constructor; cbn [fst]; lia.
  Qed.
  Lemma bd_unp_dt : forall h0 h1 tb sn sp m1, BDm h0 h1 tb sn sp m1 -> unpoisoned m1 DT (DT + 4 + 4 * 2^tl).
  Proof.
    intros until m1. intros I. open_bd I. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_unp_w : forall h0 h1 tb sn sp m1, BDm h0 h1 tb sn sp m1 -> unpoisoned m1 W (W + wlen).
  Proof.
    intros until m1. intros I. open_bd I. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_unp_nc : forall h0 h1 tb sn sp m1, BDm h0 h1 tb sn sp m1 -> unpoisoned m1 NC (NC + 2 * zlen norm).
  Proof.
    intros until m1. intros I. open_bd I. open_hy HY. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    pose proof UNC as (U0 & U1 & _).
    eapply unpoisoned_munch; [exact UNC | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bd_art : forall h0 h1 tb sn sp m1, BDm h0 h1 tb sn sp m1 -> art m1.
  Proof.
    intros until m1. intros I. open_bd I. pose proof bd_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply art_transport; [exact ART0| exact MU| exact WM|]. repeat constructor; cbn [fst]; lia.
  Qed.
End G.
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hy HY := apply (bdA_open _ _ _ _ _ _ _ _ _ _ HY); intros TLR MSVR NLEN NGE NSUM WLEN WLEN32 DTL DTH WL WH NCL NCH LO0 LOS SPR DTA WA NCA OFFDT OFFW OFFNC DTW DTNC WNC ABDT RDT RSDT ABW RW RSW RNC RSNC KLO RSTK RI.
Ltac open_bd I := apply (BDA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros j0 HDR CEL CLEN CBY SNX SNLEN SPRD SPLEN SPBY NCB STK MI MU WM FR.
Ltac close_bd := eapply BDA_close; eassumption.
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.