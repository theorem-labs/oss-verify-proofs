(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition shspan (A n : Z) : Z := (A + n + 7) / 8 - A / 8.
Definition c2ok (T : Z) (dt : list Z) (u : Z) : Prop := 0 <= Znth (4 * u + 6) dt <= T /\ 1 <= Znth (4 * u + 7) dt <= 2.
Definition x2pref (T cur : Z) (dt : list Z) : Prop := forall u, 0 <= u < cur -> c2ok T dt u.
Lemma x2pref_0 : forall T dt, x2pref T 0 dt.
Proof. intros T dt u Hu. lia. Qed.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.
Definition x2hb_art (m : amem) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m.

Definition APX2HB : Z := 0x8d25c.
Definition X2HB_FRAME : Z := 112.
Definition X2HB_RET : Z := 0x8dbd8.
Definition X2HB_CHK : Z := 0x8dc14.

Definition x2hb_hyps (RNG : footprint) (SPF DT SYM mtl : Z) : Prop :=
  4096 <= DT
  /\ DT + (4 * (1 + 2 ^ mtl)) <= 2^47
  /\ DT mod 4 = 0
  /\ 4096 <= SYM
  /\ SYM + 256 < 2^47
  /\ KHIGH <= SPF - 112
  /\ SPF + 16 <= 2^47
  /\ SPF mod 16 = 0
  /\ (DT + (4 * (1 + 2 ^ mtl)) <= SYM \/ SYM + 256 <= DT)
  /\ (DT + (4 * (1 + 2 ^ mtl)) <= SPF - 112 \/ SPF <= DT)
  /\ (SYM + 256 <= SPF - 112 \/ SPF <= SYM)
  /\ ablk DT (DT + (4 * (1 + 2 ^ mtl)))
  /\ rng RNG DT (4 * (1 + 2 ^ mtl))
  /\ rng RNG (shad DT) (shspan DT (4 * (1 + 2 ^ mtl)))
  /\ ablk SYM (SYM + 256)
  /\ rng RNG SYM 256
  /\ rng RNG (shad SYM) (shspan SYM 256)
  /\ rng RNG (SPF - 112) 112
  /\ rng_aimg RNG.

Lemma x2hb_open : forall RNG SPF DT SYM mtl, x2hb_hyps RNG SPF DT SYM mtl ->
  forall G : Prop, (4096 <= DT -> DT + (4 * (1 + 2 ^ mtl)) <= 2^47 -> DT mod 4 = 0 -> 4096 <= SYM -> SYM + 256 < 2^47 ->
    KHIGH <= SPF - 112 -> SPF + 16 <= 2^47 -> SPF mod 16 = 0 ->
    (DT + (4 * (1 + 2 ^ mtl)) <= SYM \/ SYM + 256 <= DT) -> (DT + (4 * (1 + 2 ^ mtl)) <= SPF - 112 \/ SPF <= DT) -> (SYM + 256 <= SPF - 112 \/ SPF <= SYM) ->
    ablk DT (DT + (4 * (1 + 2 ^ mtl))) -> rng RNG DT (4 * (1 + 2 ^ mtl)) -> rng RNG (shad DT) (shspan DT (4 * (1 + 2 ^ mtl))) ->
    ablk SYM (SYM + 256) -> rng RNG SYM 256 -> rng RNG (shad SYM) (shspan SYM 256) ->
    rng RNG (SPF - 112) 112 -> rng_aimg RNG -> G) -> G.
Proof. intros until mtl. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18). eapply K; eassumption. Qed.

Definition X2HBFR (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 x1].

Definition x2hb_post (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPF DT T mtl : Z) (m : amem) (cur' : Z) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' (dt' : list Z),
    ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (ret_pc x1) fc None m' (seg_rom bsegs)
    /\ munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' DT (map (Z_to_bv 8) dt') /\ zlen dt' = (4 * (1 + 2 ^ mtl)) /\ Forall isbyte dt'
    /\ x2pref T cur' dt' /\ stk bsegs m' (SPF - 112) SPF.

Definition x2hb_stmt : Prop :=
  forall (RNG : footprint) (x1 gp tp x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (dt : list Z) (syb : list byte),
  x2hb_hyps RNG SPF DT SYM mtl ->
  mem_inv bsegs m -> u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = (4 * (1 + 2 ^ mtl)) -> Forall isbyte dt ->
  bytes_at bsegs m SYM syb -> zlen syb = 256 -> stk bsegs m (SPF - 112) SPF -> x2hb_art m ->
  unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m SYM (SYM + 256) -> tp = Z_to_bv 64 ATP ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 -> T <= mtl -> pos + 2^(T - nb) * cnt <= 2 ^ mtl ->
  (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m (pos + 2^(T - nb) * cnt))
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg)) (Z_to_bv 64 (SYM + bg + cnt))
               (Z_to_bv 64 nb) (Z_to_bv 64 T) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8d25c) fc None m (seg_rom bsegs)).

Lemma x2hb_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma x2hb_art_transport : forall W m m', x2hb_art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0x60f000 <= fst iv) W -> x2hb_art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold x2hb_art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply x2hb_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply x2hb_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (SPF DT SYM mtl : Z) (m0 : amem).
  Hypothesis HY : x2hb_hyps RNG SPF DT SYM mtl.
  Hypothesis UDT : unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))).
  Hypothesis USY : unpoisoned m0 SYM (SYM + 256).
  Hypothesis ART0 : x2hb_art m0.

  Lemma x2hb_bands : (DT + (4 * (1 + 2 ^ mtl)) + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (SYM + 256 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= SYM)
                    /\ 0x10007fff8000 + 112 <= SPF /\ SPF + 16 <= 2^47 /\ 0x60f000 <= DT /\ 0x60f000 <= SYM /\ DT + (4 * (1 + 2 ^ mtl)) <= 2^47 /\ SYM + 256 < 2^47.
  Proof.
    destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & ABD & Y12 & Y13 & ABS & Y15 & Y16 & Y17 & Y18).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABS. unfold KHIGH in Y5.
    repeat split; lia.
  Qed.

  Lemma x2hb_unp_dtM : forall m1, munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m1 -> unpoisoned m1 DT (DT + (4 * (1 + 2 ^ mtl))).
  Proof.
    intros m1 MU. pose proof x2hb_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2hb_unp_syM : forall m1, munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m1 -> unpoisoned m1 SYM (SYM + 256).
  Proof.
    intros m1 MU. pose proof x2hb_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact USY | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2hb_artM : forall m1, munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m1 -> wmono bsegs m0 m1 -> x2hb_art m1.
  Proof.
    intros m1 MU WM. pose proof x2hb_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply x2hb_art_transport; [exact ART0| exact MU| exact WM|]. repeat constructor; cbn [fst]; lia.
  Qed.

  Definition XHb (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (syb j0 : list byte) (dt : list Z) (m : amem) : Prop :=
    u8arr bsegs m DT (map (Z_to_bv 8) dt)
    /\ zlen dt = (4 * (1 + 2 ^ mtl))
    /\ Forall isbyte dt
    /\ bytes_at bsegs m SYM syb
    /\ zlen syb = 256
    /\ rw_cells bsegs m (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0)
    /\ mem_inv bsegs m
    /\ munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m
    /\ wmono bsegs m0 m.
  Lemma XHb_open : forall x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m, XHb x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m ->
    forall G : Prop, (u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = (4 * (1 + 2 ^ mtl)) -> Forall isbyte dt -> bytes_at bsegs m SYM syb -> zlen syb = 256 ->
      rw_cells bsegs m (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0) -> mem_inv bsegs m ->
      munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m -> wmono bsegs m0 m -> G) -> G.
  Proof. intros until m. intros I G K. destruct I as (A & B & C & D & E & F0 & G0 & H & I). eapply K; eassumption. Qed.
  Lemma XHb_close : forall x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m,
    u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = (4 * (1 + 2 ^ mtl)) -> Forall isbyte dt -> bytes_at bsegs m SYM syb -> zlen syb = 256 ->
    rw_cells bsegs m (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0) -> mem_inv bsegs m ->
    munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m0 m -> wmono bsegs m0 m ->
    XHb x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m.
  Proof. intros. unfold XHb. repeat (split; [assumption|]). assumption. Qed.
End G.
End CANSEC1.

Ltac open_hyhb HY := apply (x2hb_open _ _ _ _ _ HY); intros DTL DTH DT4 SYL SYH KLO SPT SP16 DSY DSP SSP ABD RDT RSDT ABS RSY RSSY RSTF RI.
Ltac open_xhb I := apply (XHb_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY SYB SYLEN FR MI MU WM; unfold X2HBFR in FR.
Ltac close_xhb := unfold X2HBFR; eapply XHb_close; try eassumption.
Lemma x2hb_w_hi : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  Z.lor A B / 65536 = tb + 512.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2.
  rewrite <- (Z.shiftr_div_pow2 _ 16) by lia. rewrite Z.shiftr_lor. rewrite !Z.shiftr_div_pow2 by lia.
  replace (B / 2 ^ 16) with 0 by (rewrite HB; symmetry; apply Z.div_small; lia).
  rewrite Z.lor_0_r. rewrite HA. change (2 ^ 16) with 65536. Z.div_mod_to_equations. lia.
Qed.
Lemma x2hb_w_range : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  0 <= Z.lor A B < 18446744073709551616.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. split; [apply Z.lor_nonneg; lia|].
  assert (L : Z.lor A B < 2 ^ 26); [| change (2 ^ 26) with 67108864 in L; lia].
  destruct (Z.eq_dec (Z.lor A B) 0) as [E|NE]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg A B); lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply Z.log2_lt_pow2; lia|]. destruct (Z.eq_dec B 0) as [E0|N0]; [rewrite E0; cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.

Lemma x2hb_w_bytes : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  (Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64) / 65536) mod 256 = tb /\ (Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64) / 65536 / 256) mod 256 = 2.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small A) by lia. rewrite (Z.mod_small B) by lia. rewrite Z.lor_comm. rewrite (x2hb_w_hi A B tb sv s2 HA HB Ht Hs H2).
  split; Z.div_mod_to_equations; lia.
Qed.

Lemma x2hb_d_bytes : forall A B tb sv s2, A = 65536 * tb + sv + 33554432 -> B = 256 * s2 -> 0 <= tb <= 12 -> 0 <= sv < 256 -> 0 <= s2 < 256 ->
  let D := (4294967297 * Z.lor (B mod 2 ^ 64) (A mod 2 ^ 64)) mod 2 ^ 64 in
  (D / 65536) mod 256 = tb /\ (D / 65536 / 256) mod 256 = 2 /\ (D / 281474976710656) mod 256 = tb /\ (D / 281474976710656 / 256) mod 256 = 2.
Proof.
  intros A B tb sv s2 HA HB Ht Hs H2. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small A) by lia. rewrite (Z.mod_small B) by lia. rewrite Z.lor_comm.
  pose proof (x2hb_w_hi A B tb sv s2 HA HB Ht Hs H2) as HV. pose proof (x2hb_w_range A B tb sv s2 HA HB Ht Hs H2) as RV.
  change (2 ^ 26) with 67108864 in RV.
  remember (Z.lor A B) as V eqn:EV. clear EV HA HB A B. cbv zeta.
  rewrite (Z.mod_small (4294967297 * V)) by lia.
  Z.div_mod_to_equations. lia.
Qed.
