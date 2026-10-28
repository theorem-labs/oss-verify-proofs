(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x2_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.

Definition APX2H : Z := 0x97a2c.        (* [comment removed for export] *)
Definition X2H_RET : Z := 0x97990.      (* [comment removed for export] *)
Definition X2H_TRAP : Z := 0xa546c.     (* [comment removed for export] *)
Definition APX2H2 : Z := 0x98624.
Definition X2H2_RET : Z := 0x985b0.

(* [comment removed for export] *)
Definition x2hA_hyps (RNG : footprint) (SPA DT SYM : Z) : Prop :=
  4096 <= DT
  /\ DT + 16388 <= 2^47
  /\ DT mod 4 = 0
  /\ 4096 <= SYM
  /\ SYM + 256 < 2^47
  /\ KHIGH <= SPA
  /\ SPA + 728 <= 2^47
  /\ SPA mod 16 = 0
  /\ (DT + 16388 <= SYM \/ SYM + 256 <= DT)
  /\ (DT + 16388 <= SPA \/ SPA + 728 <= DT)
  /\ (SYM + 256 <= SPA \/ SPA + 728 <= SYM)
  /\ ablk DT (DT + 16388)
  /\ rng RNG DT 16388
  /\ rng RNG (shad DT) (shspan DT 16388)
  /\ ablk SYM (SYM + 256)
  /\ rng RNG SYM 256
  /\ rng RNG (shad SYM) (shspan SYM 256)
  /\ rng RNG SPA 728
  /\ rng_aimg RNG.

Lemma x2hA_open : forall RNG SPA DT SYM, x2hA_hyps RNG SPA DT SYM ->
  forall G : Prop, (4096 <= DT -> DT + 16388 <= 2^47 -> DT mod 4 = 0 -> 4096 <= SYM -> SYM + 256 < 2^47 ->
    KHIGH <= SPA -> SPA + 728 <= 2^47 -> SPA mod 16 = 0 ->
    (DT + 16388 <= SYM \/ SYM + 256 <= DT) -> (DT + 16388 <= SPA \/ SPA + 728 <= DT) -> (SYM + 256 <= SPA \/ SPA + 728 <= SYM) ->
    ablk DT (DT + 16388) -> rng RNG DT 16388 -> rng RNG (shad DT) (shspan DT 16388) ->
    ablk SYM (SYM + 256) -> rng RNG SYM 256 -> rng RNG (shad SYM) (shspan SYM 256) ->
    rng RNG SPA 728 -> rng_aimg RNG -> G) -> G.
Proof. intros until SYM. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18). eapply K; eassumption. Qed.

(* [comment removed for export] *)
Definition X2HSC (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : word) : list cell :=
  [C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9].

(* [comment removed for export] *)
Definition x2h_postA (XPC : Z) (x2 gp tp x8 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPA DT T : Z) (m : amem) (cur' : Z) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31
                    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : word) m' (dt' : list Z),
    ms' = MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 0x7fff8000) x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 XPC) fc None m' (seg_rom bsegs)
    /\ munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' DT (map (Z_to_bv 8) dt') /\ zlen dt' = 16388 /\ Forall isbyte dt'
    /\ x2pref T cur' dt' /\ rw_cells bsegs m' (SPA + 624) (X2HSC y0 y1 y2 y3 y4 y5 y6 y7 y8 y9).
Definition x2h_postA1 := x2h_postA X2H_RET.
Definition x2h_postA2 := x2h_postA X2H2_RET.

Definition x2h1_slots (m : amem) (SPA DT SYM bg cnt : Z) : Prop :=
  rw_cells bsegs m (SPA + 144) [C8 (Z_to_bv 64 (DT + 8))]
  /\ rw_cells bsegs m (SPA + 160) [C8 (Z_to_bv 64 (DT + 7))]
  /\ rw_cells bsegs m (SPA + 192) [C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 35)); C8 (Z_to_bv 64 (DT + 28));
                                   C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 11)); C8 (Z_to_bv 64 (DT + 4));
                                   C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells bsegs m (SPA + 288) [C8 (Z_to_bv 64 (bg + cnt))]
  /\ rw_cells bsegs m (SPA + 608) [C8 (Z_to_bv 64 SYM)].

Definition x2h2_slots (m : amem) (SPA DT SYM st bs nb w2 T : Z) : Prop :=
  rw_cells bsegs m (SPA + 296) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 19 + 4 * st)); C8 (Z_to_bv 64 (DT + 12 + 4 * st));
                                C8 (Z_to_bv 64 (DT + 27 + 4 * st)); C8 (Z_to_bv 64 (DT + 20 + 4 * st)); C8 (Z_to_bv 64 (DT + 35 + 4 * st));
                                C8 (Z_to_bv 64 (DT + 28 + 4 * st)); C8 (Z_to_bv 64 (DT + 11 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st))]
  /\ rw_cells bsegs m (SPA + 368) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 19 + 4 * st)); C8 (Z_to_bv 64 (DT + 12 + 4 * st));
                                   C8 (Z_to_bv 64 (DT + 11 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st))]
  /\ rw_cells bsegs m (SPA + 408) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 11 + 4 * st)); C8 (Z_to_bv 64 (DT + 8 + 4 * st));
                                   C8 (Z_to_bv 64 (DT + 7 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st))]
  /\ rw_cells bsegs m (SPA + 448) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 7 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st))]
  /\ rw_cells bsegs m (SPA + 472) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 19 + 4 * st)); C8 (Z_to_bv 64 (DT + 12 + 4 * st));
                                   C8 (Z_to_bv 64 (DT + 27 + 4 * st)); C8 (Z_to_bv 64 (DT + 20 + 4 * st)); C8 (Z_to_bv 64 (DT + 35 + 4 * st));
                                   C8 (Z_to_bv 64 (DT + 28 + 4 * st)); C8 (Z_to_bv 64 (DT + 11 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st))]
  /\ rw_cells bsegs m (SPA + 544) [C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (DT + 4 + 4 * st)); C8 (Z_to_bv 64 (bs + 33554432));
                                   C8 (Z_to_bv 64 (nb + w2))]
  /\ rw_cells bsegs m (SPA + 600) [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 SYM)].

Definition x2h_stmtA1 : Prop :=
  forall (RNG : footprint) (x1 x2 gp tp x5 x6 x7 x8 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (SPA DT SYM pos cnt bg nb T : Z) (dt : list Z) (syb : list byte),
  x2hA_hyps RNG SPA DT SYM ->
  mem_inv bsegs m -> u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt ->
  bytes_at bsegs m SYM syb -> zlen syb = 256 -> art m ->
  unpoisoned m DT (DT + 16388) -> unpoisoned m SYM (SYM + 256) -> tp = Z_to_bv 64 ATP ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> pos + 2^(T - nb) * cnt <= 4096 ->
  x2pref T pos dt -> x2h1_slots m SPA DT SYM bg cnt -> rw_cells bsegs m (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) ->
  evtF bsegs RNG (x2h_postA1 x2 gp tp x8 F fc SPA DT T m (pos + 2^(T - nb) * cnt))
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 nb) x11 (Z_to_bv 64 (T - nb)) x13 x14 x15 (Z_to_bv 64 bg) x17
               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 pos) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 APX2H) fc None m (seg_rom bsegs)).

Definition x2h_stmtA2 : Prop :=
  forall (RNG : footprint) (x1 x2 gp tp x5 x6 x7 x8 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (SPA DT SYM pos st cnt bg nb w2 T bs : Z) (dt : list Z) (syb : list byte),
  x2hA_hyps RNG SPA DT SYM ->
  mem_inv bsegs m -> u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt ->
  bytes_at bsegs m SYM syb -> zlen syb = 256 -> art m ->
  unpoisoned m DT (DT + 16388) -> unpoisoned m SYM (SYM + 256) -> tp = Z_to_bv 64 ATP ->
  0 <= st <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> pos + 2^(T - nb) * cnt <= 4096 ->
  0 <= bs < 256 -> 0 <= w2 < 2^20 ->
  x2pref T pos dt -> x2h2_slots m SPA DT SYM st bs nb w2 T -> rw_cells bsegs m (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) ->
  evtF bsegs RNG (x2h_postA2 x2 gp tp x8 F fc SPA DT T m (pos + 2^(T - nb) * cnt))
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 w2) x11 (Z_to_bv 64 bg) x13 x14 x15 (Z_to_bv 64 (bg + cnt)) (Z_to_bv 64 1)
               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (pos - st)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 APX2H2) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma x2h_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma x2h_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply x2h_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply x2h_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.
Lemma x2h_cells_sub : forall m A cs i j, rw_cells bsegs m A cs ->
  rw_cells bsegs m (A + Z.of_nat (cells_size (firstn i cs))) (firstn j (skipn i cs)).
Proof.
  intros m A cs i j H. rewrite <- (firstn_skipn i cs) in H. apply ZdWalkKit.rw_cells_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn j (skipn i cs)) in H. apply ZdWalkKit.rw_cells_app in H. exact (proj1 H).
Qed.

Section G.
  Variables (RNG : footprint) (SPA DT SYM : Z) (m0 : amem).
  Hypothesis HY : x2hA_hyps RNG SPA DT SYM.
  Hypothesis UDT : unpoisoned m0 DT (DT + 16388).
  Hypothesis USY : unpoisoned m0 SYM (SYM + 256).
  Hypothesis ART0 : art m0.

  (* [comment removed for export] *)
  Lemma x2h_bands : (DT + 16388 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (SYM + 256 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= SYM)
                    /\ 0x10007fff8000 <= SPA /\ SPA + 728 <= 2^47 /\ 0x625000 <= DT /\ 0x625000 <= SYM /\ DT + 16388 <= 2^47 /\ SYM + 256 < 2^47.
  Proof.
    destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & ABD & Y12 & Y13 & ABS & Y15 & Y16 & Y17 & Y18).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABS. unfold KHIGH in Y5.
    repeat split; lia.
  Qed.

  Lemma x2h_unp_dtM : forall m1, munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m1 -> unpoisoned m1 DT (DT + 16388).
  Proof.
    intros m1 MU. pose proof x2h_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2h_unp_syM : forall m1, munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m1 -> unpoisoned m1 SYM (SYM + 256).
  Proof.
    intros m1 MU. pose proof x2h_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact USY | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2h_artM : forall m1, munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m1 -> wmono bsegs m0 m1 -> art m1.
  Proof.
    intros m1 MU WM. pose proof x2h_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply x2h_art_transport; [exact ART0| exact MU| exact WM|]. repeat constructor; cbn [fst]; lia.
  Qed.

  (* [comment removed for export] *)
  Definition XH (syb : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : word) (dt : list Z) (m : amem) : Prop :=
    u8arr bsegs m DT (map (Z_to_bv 8) dt)
    /\ zlen dt = 16388
    /\ Forall isbyte dt
    /\ bytes_at bsegs m SYM syb
    /\ zlen syb = 256
    /\ rw_cells bsegs m (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)
    /\ mem_inv bsegs m
    /\ munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m
    /\ wmono bsegs m0 m.
  Lemma XH_open : forall syb v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 dt m, XH syb v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 dt m ->
    forall G : Prop, (u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt -> bytes_at bsegs m SYM syb -> zlen syb = 256 ->
      rw_cells bsegs m (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) -> mem_inv bsegs m ->
      munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m -> wmono bsegs m0 m -> G) -> G.
  Proof. intros until m. intros I G K. destruct I as (A & B & C & D & E & F0 & G0 & H & I). eapply K; eassumption. Qed.
  Lemma XH_close : forall syb v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 dt m,
    u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt -> bytes_at bsegs m SYM syb -> zlen syb = 256 ->
    rw_cells bsegs m (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) -> mem_inv bsegs m ->
    munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m -> wmono bsegs m0 m ->
    XH syb v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 dt m.
  Proof. intros. unfold XH. repeat (split; [assumption|]). assumption. Qed.
  Lemma x2h1_slots_tr : forall bg cnt m1, x2h1_slots m0 SPA DT SYM bg cnt ->
    munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m1 -> wmono bsegs m0 m1 -> x2h1_slots m1 SPA DT SYM bg cnt.
  Proof.
    intros bg cnt m1 (S1 & S2 & S3 & S4 & S5) MU WM.
    destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & _).
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    all: eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [| split; [| exact I]]; lia].
  Qed.
  Lemma x2h2_slots_tr : forall st bs nb w2 T m1, x2h2_slots m0 SPA DT SYM st bs nb w2 T ->
    munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m1 -> wmono bsegs m0 m1 -> x2h2_slots m1 SPA DT SYM st bs nb w2 T.
  Proof.
    intros st bs nb w2 T m1 (S1 & S2 & S3 & S4 & S5 & S6 & S7) MU WM.
    destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & _).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    all: eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [| split; [| exact I]]; lia].
  Qed.
End G.
End CANSEC1.

Ltac open_hyh HY := apply (x2hA_open _ _ _ _ HY); intros DTL DTH DT4 SYL SYH KLO SPT SP16 DSY DSP SSP ABD RDT RSDT ABS RSY RSSY RSTF RI.
Ltac open_xh I := apply (XH_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY SYB SYLEN FR MI MU WM; unfold X2HSC in FR.
Ltac close_xh := unfold X2HSC; eapply XH_close; try eassumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma x2w_hi : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  Z.lor A B / 65536 = tb + 512.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2.
  rewrite <- (Z.shiftr_div_pow2 _ 16) by lia. rewrite Z.shiftr_lor. rewrite !Z.shiftr_div_pow2 by lia.
  replace (B / 2 ^ 16) with 0 by (rewrite HB; symmetry; apply Z.div_small; lia).
  rewrite Z.lor_0_r. rewrite HA. change (2 ^ 16) with 65536. Z.div_mod_to_equations. lia.
Qed.
Lemma x2w_range : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  0 <= Z.lor A B < 18446744073709551616.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. split; [apply Z.lor_nonneg; lia|].
  assert (L : Z.lor A B < 2 ^ 26); [| change (2 ^ 26) with 67108864 in L; lia].
  destruct (Z.eq_dec (Z.lor A B) 0) as [E|NE]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg A B); lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply Z.log2_lt_pow2; lia|]. destruct (Z.eq_dec B 0) as [E0|N0]; [rewrite E0; cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.

Lemma x2w_bytes : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  (Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64) / 65536) mod 256 = tb /\ (Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64) / 65536 / 256) mod 256 = 2.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small A) by lia. rewrite (Z.mod_small B) by lia. rewrite Z.lor_comm. rewrite (x2w_hi A B tb sv s2 HA HB Ht Hs H2).
  split; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Ltac x2w_use tb sv s2 SVR R2 :=
  lazymatch goal with H : hidden (_ = (Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64) / 65536) mod 256) |- _ =>
    let W := fresh "W2B" in
    pose proof (x2w_bytes A B tb sv s2) as W;
    specialize (W ltac:(lia)); specialize (W ltac:(lia)); specialize (W ltac:(lia)); specialize (W ltac:(clear - SVR; lia)); specialize (W ltac:(clear - R2; lia));
    let Wa := fresh "W2a" in let Wb := fresh "W2b" in destruct W as [Wa Wb];
    repeat match goal with E : hidden (?v = ?e) |- _ => first [rewrite Wa in E| rewrite Wb in E]; unfold hidden in E; subst v end;
    clear Wa Wb
  end.

Lemma x2d_bytes : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  let D := (4294967297 * Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64)) mod 2 ^ 64 in
  (D / 65536) mod 256 = tb /\ (D / 65536 / 256) mod 256 = 2 /\ (D / 281474976710656) mod 256 = tb /\ (D / 281474976710656 / 256) mod 256 = 2.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small A) by lia. rewrite (Z.mod_small B) by lia. rewrite Z.lor_comm.
  pose proof (x2w_hi A B tb sv s2 HA HB Ht Hs H2) as HV. pose proof (x2w_range A B tb sv s2 HA HB Ht Hs H2) as RV.
  change (2 ^ 26) with 67108864 in RV.
  remember (Z.lor A B) as V eqn:EV. clear EV HA HB A B. cbv zeta.
  rewrite (Z.mod_small (4294967297 * V)) by lia.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Ltac x2d_use tb sv s2 SVR R2 :=
  lazymatch goal with H : hidden (_ = ((4294967297 * Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64)) mod 2 ^ 64 / 65536) mod 256) |- _ =>
    let W := fresh "W2B" in
    pose proof (x2d_bytes A B tb sv s2) as W;
    specialize (W ltac:(lia)); specialize (W ltac:(lia)); specialize (W ltac:(lia)); specialize (W ltac:(clear - SVR; lia)); specialize (W ltac:(clear - R2; lia));
    cbv zeta in W;
    let Wa := fresh "W2a" in let Wb := fresh "W2b" in let Wc := fresh "W2c" in let Wd := fresh "W2d" in destruct W as (Wa & Wb & Wc & Wd);
    repeat match goal with E : hidden (?v = ?e) |- _ => first [rewrite Wa in E| rewrite Wb in E| rewrite Wc in E| rewrite Wd in E]; unfold hidden in E; subst v end;
    clear Wa Wb Wc Wd
  end.

