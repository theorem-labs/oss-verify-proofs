(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdSeqBuildW SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition bfA_hyps (RNG : footprint) (SPV lo DT NC BASE BITS W wlen maxSV tl : Z) (k : seq_kind) (norm : list Z) : Prop :=
  5 <= tl <= 9
  /\ 0 <= maxSV <= 52
  /\ maxSV <= kind_max k
  /\ zlen (kind_base k) = kind_max k + 1
  /\ zlen (kind_bits k) = kind_max k + 1
  /\ maxSV + 1 <= zlen norm
  /\ (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm)
  /\ pws norm (maxSV + 1) = 2^tl
  /\ 626 <= wlen
  /\ 4096 <= DT
  /\ DT + 8 + 8 * 2^tl < 2^47
  /\ 4096 <= W
  /\ W + wlen < 2^47
  /\ 4096 <= NC
  /\ NC + 2 * zlen norm < 2^47
  /\ 4096 <= BASE
  /\ BASE + 212 <= 2^47
  /\ 4096 <= BITS
  /\ BITS + 53 <= 2^47
  /\ 0 <= lo
  /\ lo <= SPV - 176
  /\ SPV < 2^47
  /\ DT mod 4 = 0
  /\ W mod 2 = 0
  /\ NC mod 2 = 0
  /\ BASE mod 4 = 0
  /\ (DT + 8 + 8 * 2^tl <= lo \/ SPV <= DT)
  /\ (W + wlen <= lo \/ SPV <= W)
  /\ (NC + 2 * zlen norm <= lo \/ SPV <= NC)
  /\ (BASE + 212 <= lo \/ SPV <= BASE)
  /\ (BITS + 53 <= lo \/ SPV <= BITS)
  /\ (DT + 8 + 8 * 2^tl <= W \/ W + wlen <= DT)
  /\ (DT + 8 + 8 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT)
  /\ (W + wlen <= NC \/ NC + 2 * zlen norm <= W)
  /\ (DT + 8 + 8 * 2^tl <= BASE \/ BASE + 212 <= DT)
  /\ (DT + 8 + 8 * 2^tl <= BITS \/ BITS + 53 <= DT)
  /\ (W + wlen <= BASE \/ BASE + 212 <= W)
  /\ (W + wlen <= BITS \/ BITS + 53 <= W)
  /\ ablk DT (DT + 8 + 8 * 2^tl)
  /\ rng RNG DT (8 + 8 * 2^tl)
  /\ rng RNG (shad DT) (shspan DT (8 + 8 * 2^tl))
  /\ ablk W (W + wlen)
  /\ rng RNG W wlen
  /\ rng RNG (shad W) (shspan W wlen)
  /\ rng RNG NC (2 * zlen norm)
  /\ rng RNG (shad NC) (shspan NC (2 * zlen norm))
  /\ rng RNG BASE (4 * (kind_max k + 1))
  /\ rng RNG (shad BASE) (shspan BASE (4 * (kind_max k + 1)))
  /\ rng RNG BITS (kind_max k + 1)
  /\ rng RNG (shad BITS) (shspan BITS (kind_max k + 1))
  /\ KHIGH <= lo
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Lemma bfA_open : forall RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm, bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm ->
  forall G : Prop, (5 <= tl <= 9 ->
    0 <= maxSV <= 52 ->
    maxSV <= kind_max k ->
    zlen (kind_base k) = kind_max k + 1 ->
    zlen (kind_bits k) = kind_max k + 1 ->
    maxSV + 1 <= zlen norm ->
    (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
    pws norm (maxSV + 1) = 2^tl ->
    626 <= wlen ->
    4096 <= DT ->
    DT + 8 + 8 * 2^tl < 2^47 ->
    4096 <= W ->
    W + wlen < 2^47 ->
    4096 <= NC ->
    NC + 2 * zlen norm < 2^47 ->
    4096 <= BASE ->
    BASE + 212 <= 2^47 ->
    4096 <= BITS ->
    BITS + 53 <= 2^47 ->
    0 <= lo ->
    lo <= SPV - 176 ->
    SPV < 2^47 ->
    DT mod 4 = 0 ->
    W mod 2 = 0 ->
    NC mod 2 = 0 ->
    BASE mod 4 = 0 ->
    (DT + 8 + 8 * 2^tl <= lo \/ SPV <= DT) ->
    (W + wlen <= lo \/ SPV <= W) ->
    (NC + 2 * zlen norm <= lo \/ SPV <= NC) ->
    (BASE + 212 <= lo \/ SPV <= BASE) ->
    (BITS + 53 <= lo \/ SPV <= BITS) ->
    (DT + 8 + 8 * 2^tl <= W \/ W + wlen <= DT) ->
    (DT + 8 + 8 * 2^tl <= NC \/ NC + 2 * zlen norm <= DT) ->
    (W + wlen <= NC \/ NC + 2 * zlen norm <= W) ->
    (DT + 8 + 8 * 2^tl <= BASE \/ BASE + 212 <= DT) ->
    (DT + 8 + 8 * 2^tl <= BITS \/ BITS + 53 <= DT) ->
    (W + wlen <= BASE \/ BASE + 212 <= W) ->
    (W + wlen <= BITS \/ BITS + 53 <= W) ->
    ablk DT (DT + 8 + 8 * 2^tl) ->
    rng RNG DT (8 + 8 * 2^tl) ->
    rng RNG (shad DT) (shspan DT (8 + 8 * 2^tl)) ->
    ablk W (W + wlen) ->
    rng RNG W wlen ->
    rng RNG (shad W) (shspan W wlen) ->
    rng RNG NC (2 * zlen norm) ->
    rng RNG (shad NC) (shspan NC (2 * zlen norm)) ->
    rng RNG BASE (4 * (kind_max k + 1)) ->
    rng RNG (shad BASE) (shspan BASE (4 * (kind_max k + 1))) ->
    rng RNG BITS (kind_max k + 1) ->
    rng RNG (shad BITS) (shspan BITS (kind_max k + 1)) ->
    KHIGH <= lo ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until norm. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31 & Y32 & Y33 & Y34 & Y35 & Y36 & Y37 & Y38 & Y39 & Y40 & Y41 & Y42 & Y43 & Y44 & Y45 & Y46 & Y47 & Y48 & Y49 & Y50 & Y51 & Y52). eapply K; eassumption. Qed.
Ltac open_hy HY := apply (bfA_open _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros TLR MSVR MSVK LKB LKBI NLEN NGE NSUM WLEN DTL DTH WL WH NCL NCH BAL BAH BIL BIH LO0 LOS SPR DT4 W2 NC2 BASE4 OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI ABDT RDT RSDT ABW RW RSW RNC RSNC RBA RSBA RBI RSBI KLO RSTK RI.

(* [comment removed for export] *)
Definition BFA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : amem) (SPV lo DT NC BASE BITS W wlen maxSV tl : Z) (k : seq_kind) (norm : list Z)
    (h0 h1 w0 w8 w16 w24 : word) (cells : list seqsym) (sn sp : list Z) (m1 : amem) : Prop :=
  rw_cells bsegs m1 DT [C4 h0; C4 h1]
  /\ u8arr bsegs m1 (DT + 8) (map (Z_to_bv 8) (flat_map seqsym_bytes cells))
  /\ zlen cells = 2^tl
  /\ u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn))
  /\ zlen sn = 53
  /\ u8arr bsegs m1 (W + 106) (map (Z_to_bv 8) sp)
  /\ zlen sp = wlen - 106
  /\ Forall isbyte sp
  /\ bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ bytes_at bsegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k)))
  /\ bytes_at bsegs m1 BITS (map (Z_to_bv 8) (kind_bits k))
  /\ stk bsegs m1 lo (SPV + -144)
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1
  /\ wmono bsegs m m1
  /\ rw_cells bsegs m1 (SPV + -144) [C8 w0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 W); C8 (Z_to_bv 64 tl); C8 w8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma BFA_open : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm h0 h1 w0 w8 w16 w24 cells sn sp m1,
  BFA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm h0 h1 w0 w8 w16 w24 cells sn sp m1 ->
  forall G : Prop, (rw_cells bsegs m1 DT [C4 h0; C4 h1] ->
    u8arr bsegs m1 (DT + 8) (map (Z_to_bv 8) (flat_map seqsym_bytes cells)) ->
    zlen cells = 2^tl ->
    u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn)) ->
    zlen sn = 53 ->
    u8arr bsegs m1 (W + 106) (map (Z_to_bv 8) sp) ->
    zlen sp = wlen - 106 ->
    Forall isbyte sp ->
    bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm)) ->
    bytes_at bsegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
    bytes_at bsegs m1 BITS (map (Z_to_bv 8) (kind_bits k)) ->
    stk bsegs m1 lo (SPV + -144) ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 ->
    wmono bsegs m m1 ->
    rw_cells bsegs m1 (SPV + -144) [C8 w0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 W); C8 (Z_to_bv 64 tl); C8 w8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & FR). eapply K; eassumption. Qed.
Ltac open_bf I := apply (BFA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros HDR CEL CLEN SNX SNLEN SPRD SPLEN SPBY NCB BASEB BITSB STK MI MU WM FR.
(* [comment removed for export] *)
Lemma BFA_close : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm h0 h1 w0 w8 w16 w24 cells sn sp m1,
  rw_cells bsegs m1 DT [C4 h0; C4 h1] ->
  u8arr bsegs m1 (DT + 8) (map (Z_to_bv 8) (flat_map seqsym_bytes cells)) ->
  zlen cells = 2^tl ->
  u8arr bsegs m1 W (u16s (map (Z_to_bv 64) sn)) ->
  zlen sn = 53 ->
  u8arr bsegs m1 (W + 106) (map (Z_to_bv 8) sp) ->
  zlen sp = wlen - 106 ->
  Forall isbyte sp ->
  bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm)) ->
  bytes_at bsegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
  bytes_at bsegs m1 BITS (map (Z_to_bv 8) (kind_bits k)) ->
  stk bsegs m1 lo (SPV + -144) ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 ->
  wmono bsegs m m1 ->
  rw_cells bsegs m1 (SPV + -144) [C8 w0; C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 W); C8 (Z_to_bv 64 tl); C8 w8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  BFA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm h0 h1 w0 w8 w16 w24 cells sn sp m1.
Proof. intros. unfold BFA. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_bf := eapply BFA_close; eassumption.

(* [comment removed for export] *)
Definition bfA_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DT W wlen tl lo : Z) (m : amem) (t : seq_table) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' wb',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ u8arr bsegs m' DT (map (Z_to_bv 8) (seq_table_bytes t))
    /\ u8arr bsegs m' W wb' /\ zlen wb' = wlen.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

(* [comment removed for export] *)
Lemma sqb_length : forall cells, zlen (flat_map seqsym_bytes cells) = 8 * zlen cells.
Proof. induction cells as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, seqsym_bytes_length. cbn [length] in *. lia. Qed.
Lemma sqb_length_map : forall cells, zlen (map (Z_to_bv 8) (flat_map seqsym_bytes cells)) = 8 * zlen cells.
Proof. intros. rewrite length_map. apply sqb_length. Qed.

(* [comment removed for export] *)
Lemma bfA_size_rng : forall RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm,
  bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm -> 32 <= 2^tl <= 512 /\ 16 <= 2^(tl - 1) <= 256 /\ 2^(tl - 1) * 2 = 2^tl.
Proof.
  intros until norm. intros HY. open_hy HY.
  assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
  assert (2^4 <= 2^(tl - 1)) by (apply Z.pow_le_mono_r; lia). assert (2^(tl - 1) <= 2^8) by (apply Z.pow_le_mono_r; lia).
  change (2^5) with 32 in *. change (2^9) with 512 in *. change (2^4) with 16 in *. change (2^8) with 256 in *.
  split; [lia|]. split; [lia|]. replace tl with (Z.succ (tl - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma kind_max_range : forall k, 0 <= kind_max k <= 52.
Proof. intros [| |]; cbn; lia. Qed.

(* [comment removed for export] *)
Lemma bf_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma bf_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply bf_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply bf_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC BASE BITS W wlen maxSV tl : Z) (k : seq_kind) (norm : list Z).
  Hypothesis HY : bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm.
  Hypothesis UDT : unpoisoned m DT (DT + 8 + 8 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis UBA : unpoisoned m BASE (BASE + 4 * (kind_max k + 1)).
  Hypothesis UBI : unpoisoned m BITS (BITS + (kind_max k + 1)).
  Hypothesis ART0 : art m.
  Notation BFm := (BFA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm).

  (* [comment removed for export] *)
  Lemma bf_bands : (DT + 8 + 8 * 2^tl + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (W + wlen + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= W)
                   /\ 0x10007fff8000 <= SPV - 176 /\ 0x625000 <= DT /\ 0x625000 <= W /\ DT + 8 + 8 * 2^tl + 8 <= 2^47 /\ W + wlen + 8 <= 2^47.
  Proof.
    open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABDT, ABW. unfold KHIGH in KLO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_unp_dtM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> unpoisoned m1 DT (DT + 8 + 8 * 2^tl).
  Proof.
    intros m1 MU. open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bf_unp_wM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> unpoisoned m1 W (W + wlen).
  Proof.
    intros m1 MU. open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bf_unp_ncM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> unpoisoned m1 NC (NC + 2 * zlen norm).
  Proof.
    intros m1 MU. open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8). pose proof UNC as (U0 & U1 & _).
    eapply unpoisoned_munch; [exact UNC | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bf_unp_baM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> unpoisoned m1 BASE (BASE + 4 * (kind_max k + 1)).
  Proof.
    intros m1 MU. open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8). pose proof UBA as (U0 & U1 & _).
    pose proof (kind_max_range k) as KM.
    eapply unpoisoned_munch; [exact UBA | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bf_unp_biM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> unpoisoned m1 BITS (BITS + (kind_max k + 1)).
  Proof.
    intros m1 MU. open_hy HY. clear NGE OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8). pose proof UBI as (U0 & U1 & _).
    pose proof (kind_max_range k) as KM.
    eapply unpoisoned_munch; [exact UBI | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma bf_artM : forall m1, munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m1 -> wmono bsegs m m1 -> art m1.
  Proof.
    intros m1 MU WM. pose proof bf_bands as (B1 & B2 & B3 & B4 & B5 & B7 & B8).
    eapply bf_art_transport; [exact ART0| exact MU| exact WM|]. repeat constructor; cbn [fst]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma bf_wk_stkA : forall h0 h1 w0 w8 w16 w24 cells sn sp m1, BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 ->
    stk bsegs m1 W (W + wlen) /\ stk bsegs m1 DT (DT + 8 + 8 * 2^tl).
  Proof.
    intros until m1. intros I. open_hy HY. open_bf I. split.
    - apply rw_cells_of_u8arr in SNX. apply stk_of_rw_cells in SNX. apply rw_cells_of_u8arr in SPRD. apply stk_of_rw_cells in SPRD.
      cbn [cells_size csize] in SNX, SPRD. rewrite u16s_length, length_map in SNX. rewrite length_map in SPRD.
      apply (stk_merge bsegs m1 W (W + 106) (W + wlen)); [| |lia].
      + replace (W + 106) with (W + Z.of_nat (2 * length sn + 0)) by lia. exact SNX.
      + replace (W + wlen) with (W + 106 + Z.of_nat (length sp + 0)) by lia. exact SPRD.
    - apply stk_of_rw_cells in HDR. apply rw_cells_of_u8arr in CEL. apply stk_of_rw_cells in CEL.
      cbn [cells_size csize] in HDR, CEL. rewrite length_map in CEL. pose proof (sqb_length cells) as SQL.
      apply (stk_merge bsegs m1 DT (DT + 8) (DT + 8 + 8 * 2^tl)); [| |lia].
      + replace (DT + 8) with (DT + Z.of_nat (4 + (4 + 0))) at 2 by lia. exact HDR.
      + replace (DT + 8 + 8 * 2^tl) with (DT + 8 + Z.of_nat (length (flat_map seqsym_bytes cells) + 0)) by lia. exact CEL.
  Qed.
End G.
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hy HY := apply (bfA_open _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros TLR MSVR MSVK LKB LKBI NLEN NGE NSUM WLEN DTL DTH WL WH NCL NCH BAL BAH BIL BIH LO0 LOS SPR DT4 W2 NC2 BASE4 OFFDT OFFW OFFNC OFFBA OFFBI DTW DTNC WNC DTBA DTBI WBA WBI ABDT RDT RSDT ABW RW RSW RNC RSNC RBA RSBA RBI RSBI KLO RSTK RI.
Ltac open_bf I := apply (BFA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros HDR CEL CLEN SNX SNLEN SPRD SPLEN SPBY NCB BASEB BITSB STK MI MU WM FR.
Ltac close_bf := eapply BFA_close; eassumption.
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.
