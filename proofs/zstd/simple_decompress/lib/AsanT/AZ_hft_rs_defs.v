(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).
(* [comment removed for export] *)
Notation RS_WJ_STACK := 2272 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition rsA_hyps (RNG : footprint) (SPV lo HW RS NBP TLP SRC n WK wksz B bsz : Z) : Prop :=
  0 <= n
  /\ n < 2^32
  /\ 4096 <= SRC
  /\ SRC + n < 2^47
  /\ 0 <= wksz
  /\ wksz < 2^32
  /\ WK mod 4 = 0
  /\ RS mod 4 = 0
  /\ 4096 <= B
  /\ B + bsz < 2^47
  /\ B <= RS
  /\ RS + 52 <= HW
  /\ RS + 52 <= WK
  /\ HW + 256 <= B + bsz
  /\ WK + wksz <= B + bsz
  /\ (WK + wksz <= HW \/ HW + 256 <= WK)
  /\ 4096 <= NBP
  /\ NBP + 4 < 2^47
  /\ NBP mod 4 = 0
  /\ (NBP + 4 <= lo \/ SPV <= NBP)
  /\ 4096 <= TLP
  /\ TLP + 4 < 2^47
  /\ TLP mod 4 = 0
  /\ (TLP + 4 <= lo \/ SPV <= TLP)
  /\ (NBP + 4 <= TLP \/ TLP + 4 <= NBP)
  /\ (B + bsz <= lo \/ SPV + 8 <= B)
  /\ (B + bsz <= NBP \/ NBP + 4 <= B)
  /\ (B + bsz <= TLP \/ TLP + 4 <= B)
  /\ (B + bsz <= SRC \/ SRC + n <= B)
  /\ (SRC + n <= lo \/ SPV <= SRC)
  /\ 4096 <= lo
  /\ lo <= SPV - 5056
  /\ SPV + 16 < 2^47
  /\ SPV mod 16 = 0
  /\ KHIGH <= lo
  /\ ATOP + 4096 <= lo
  /\ rng RNG lo (SPV + 16 - lo)
  /\ rng_aimg RNG
  /\ ablk B (B + bsz)
  /\ rng RNG B bsz
  /\ rng RNG (shad B) (shspan B bsz)
  /\ rng RNG NBP 4
  /\ rng RNG (shad NBP) 1
  /\ rng RNG TLP 4
  /\ rng RNG (shad TLP) 1.

Lemma rsA_open : forall RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz, rsA_hyps RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz ->
  forall G : Prop, (0 <= n ->
    n < 2^32 ->
    4096 <= SRC ->
    SRC + n < 2^47 ->
    0 <= wksz ->
    wksz < 2^32 ->
    WK mod 4 = 0 ->
    RS mod 4 = 0 ->
    4096 <= B ->
    B + bsz < 2^47 ->
    B <= RS ->
    RS + 52 <= HW ->
    RS + 52 <= WK ->
    HW + 256 <= B + bsz ->
    WK + wksz <= B + bsz ->
    (WK + wksz <= HW \/ HW + 256 <= WK) ->
    4096 <= NBP ->
    NBP + 4 < 2^47 ->
    NBP mod 4 = 0 ->
    (NBP + 4 <= lo \/ SPV <= NBP) ->
    4096 <= TLP ->
    TLP + 4 < 2^47 ->
    TLP mod 4 = 0 ->
    (TLP + 4 <= lo \/ SPV <= TLP) ->
    (NBP + 4 <= TLP \/ TLP + 4 <= NBP) ->
    (B + bsz <= lo \/ SPV + 8 <= B) ->
    (B + bsz <= NBP \/ NBP + 4 <= B) ->
    (B + bsz <= TLP \/ TLP + 4 <= B) ->
    (B + bsz <= SRC \/ SRC + n <= B) ->
    (SRC + n <= lo \/ SPV <= SRC) ->
    4096 <= lo ->
    lo <= SPV - 5056 ->
    SPV + 16 < 2^47 ->
    SPV mod 16 = 0 ->
    KHIGH <= lo ->
    ATOP + 4096 <= lo ->
    rng RNG lo (SPV + 16 - lo) ->
    rng_aimg RNG ->
    ablk B (B + bsz) ->
    rng RNG B bsz ->
    rng RNG (shad B) (shspan B bsz) ->
    rng RNG NBP 4 ->
    rng RNG (shad NBP) 1 ->
    rng RNG TLP 4 ->
    rng RNG (shad TLP) 1 -> G) -> G.
Proof. intros until bsz. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31 & Y32 & Y33 & Y34 & Y35 & Y36 & Y37 & Y38 & Y39 & Y40 & Y41 & Y42 & Y43 & Y44). eapply K; eassumption. Qed.
Ltac open_hy HY := apply (rsA_open _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros NN NR SRCL SRCH WKSZ0 WKSZ WKA RSA BL BH BRS RSHW RSWK HWB WKB HWWK NBL NBH NBA OFFNB TLL TLH TLA OFFTL NBTL OFFB BNB BTL BSRC OFFSRC LO0 LOS SPR SPA KLO BOT RSTK RI ABB RB RSB RNB RSNB RTL RSTL.

(* [comment removed for export] *)
Definition RSM (ra s0 s1 s2 s3 s4 s5 s6 : word) (mj : amem) (SPV lo HW RS NBP TLP WK wksz : Z)
    (hw rank : list Z) (wn wt : word) (m1 : amem) : Prop :=
  u8arr bsegs m1 HW (map (Z_to_bv 8) hw)
  /\ zlen hw = 256
  /\ Forall isbyte hw
  /\ u32arr bsegs m1 RS (map (Z_to_bv 64) rank)
  /\ zlen rank = 13
  /\ rw_cells bsegs m1 NBP [C4 wn]
  /\ rw_cells bsegs m1 TLP [C4 wt]
  /\ stk bsegs m1 WK (WK + wksz)
  /\ stk bsegs m1 lo (SPV + -64)
  /\ rw_cells bsegs m1 (SPV + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ mem_inv bsegs m1
  /\ munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1
  /\ wmono bsegs mj m1.

Lemma RSM_open : forall ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz hw rank wn wt m1,
  RSM ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz hw rank wn wt m1 ->
  forall G : Prop, (u8arr bsegs m1 HW (map (Z_to_bv 8) hw) ->
    zlen hw = 256 ->
    Forall isbyte hw ->
    u32arr bsegs m1 RS (map (Z_to_bv 64) rank) ->
    zlen rank = 13 ->
    rw_cells bsegs m1 NBP [C4 wn] ->
    rw_cells bsegs m1 TLP [C4 wt] ->
    stk bsegs m1 WK (WK + wksz) ->
    stk bsegs m1 lo (SPV + -64) ->
    rw_cells bsegs m1 (SPV + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv bsegs m1 ->
    munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 ->
    wmono bsegs mj m1 -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12). eapply K; eassumption. Qed.
Ltac open_rsm I := apply (RSM_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros HWC HWLEN HWBY RK RKLEN NBC TLC WKS STK FR MI MU WM.
Lemma RSM_close : forall ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz hw rank wn wt m1,
  u8arr bsegs m1 HW (map (Z_to_bv 8) hw) ->
  zlen hw = 256 ->
  Forall isbyte hw ->
  u32arr bsegs m1 RS (map (Z_to_bv 64) rank) ->
  zlen rank = 13 ->
  rw_cells bsegs m1 NBP [C4 wn] ->
  rw_cells bsegs m1 TLP [C4 wt] ->
  stk bsegs m1 WK (WK + wksz) ->
  stk bsegs m1 lo (SPV + -64) ->
  rw_cells bsegs m1 (SPV + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m1 ->
  munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 ->
  wmono bsegs mj m1 ->
  RSM ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz hw rank wn wt m1.
Proof. intros. unfold RSM. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_rsm := eapply RSM_close; eassumption.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

(* [comment removed for export] *)
Lemma rs_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma rs_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply rs_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply rs_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (SPV lo HW RS NBP TLP SRC n WK wksz B bsz : Z) (mj : amem).
  Hypothesis HY : rsA_hyps RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz.
  Hypothesis UBj : unpoisoned mj B (B + bsz).
  Hypothesis UNBj : unpoisoned mj NBP (NBP + 4).
  Hypothesis UTLj : unpoisoned mj TLP (TLP + 4).
  Hypothesis ARTj : art mj.

  (* [comment removed for export] *)
  Hypothesis CB : (NBP + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= NBP) /\ (TLP + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= TLP)
                  /\ 0x625000 <= NBP /\ 0x625000 <= TLP /\ NBP + 4 + 8 <= 2^47 /\ TLP + 4 + 8 <= 2^47.

  Lemma rs_bands : (B + bsz <= 0x7fff7000 \/ 0x10007fff8000 <= B) /\ 0x10007fff8000 + 5056 <= SPV /\ 0x625000 <= B /\ B + bsz + 8 <= 2^47.
  Proof.
    open_hy HY. clear - ABB KLO LOS BH BL.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABB. unfold KHIGH in KLO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_unp_bM : forall m1, munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 -> unpoisoned m1 B (B + bsz).
  Proof.
    intros m1 MU. open_hy HY. pose proof rs_bands as (B1 & B2 & B3 & B4). pose proof CB as (C1 & C2 & C3 & C4 & C5 & C6).
    eapply unpoisoned_munch; [exact UBj | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear - B1 B2 B3 B4 C1 C2 C3 C4 C5 C6 BRS RSHW HWB BNB BTL OFFB LOS.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma rs_unp_nbM : forall m1, munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 -> unpoisoned m1 NBP (NBP + 4).
  Proof.
    intros m1 MU. open_hy HY. pose proof rs_bands as (B1 & B2 & B3 & B4). pose proof CB as (C1 & C2 & C3 & C4 & C5 & C6).
    eapply unpoisoned_munch; [exact UNBj | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear - B1 B2 B3 B4 C1 C2 C3 C4 C5 C6 BRS RSHW HWB BNB BTL NBTL OFFNB LOS.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma rs_unp_tlM : forall m1, munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 -> unpoisoned m1 TLP (TLP + 4).
  Proof.
    intros m1 MU. open_hy HY. pose proof rs_bands as (B1 & B2 & B3 & B4). pose proof CB as (C1 & C2 & C3 & C4 & C5 & C6).
    eapply unpoisoned_munch; [exact UTLj | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear - B1 B2 B3 B4 C1 C2 C3 C4 C5 C6 BRS RSHW HWB BNB BTL NBTL OFFTL LOS.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma rs_artM : forall m1, munch [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)] mj m1 -> wmono bsegs mj m1 -> art m1.
  Proof.
    intros m1 MU WM. open_hy HY. pose proof rs_bands as (B1 & B2 & B3 & B4). pose proof CB as (C1 & C2 & C3 & C4 & C5 & C6).
    eapply rs_art_transport; [exact ARTj| exact MU| exact WM|]. clear - B1 B2 B3 C3 C4 BRS RSHW HWB. repeat constructor; cbn [fst]; lia.
  Qed.
End G.
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hy HY := apply (rsA_open _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros NN NR SRCL SRCH WKSZ0 WKSZ WKA RSA BL BH BRS RSHW RSWK HWB WKB HWWK NBL NBH NBA OFFNB TLL TLH TLA OFFTL NBTL OFFB BNB BTL BSRC OFFSRC LO0 LOS SPR SPA KLO BOT RSTK RI ABB RB RSB RNB RSNB RTL RSTL.
Ltac open_rsm I := apply (RSM_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros HWC HWLEN HWBY RK RKLEN NBC TLC WKS STK FR MI MU WM.
Ltac close_rsm := eapply RSM_close; eassumption.
