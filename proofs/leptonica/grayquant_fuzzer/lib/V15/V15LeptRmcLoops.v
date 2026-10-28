(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs DitherLib DitherLoop LeptCmapArr LeptRmcLib LeptGrayFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptRmcSegs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL2a.
Import V15CL2a.V15LeptRmcFP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_s15 : forall {fx : FPState}, wr_readable SEGS.
Proof.
  intros fx seg Hin Hw. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

Lemma pcw : forall z : Z, (0 <= z < 2 ^ 64)%Z -> forall w : word, bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z Hz w <-. apply zbv_self. Qed.

Section Loops.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fregs (regs : bvmap 5 word) (g rm gm bm n4 : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 g /\ getr regs 12 = Z_to_bv 64 rm /\ getr regs 13 = Z_to_bv 64 gm /\ getr regs 14 = Z_to_bv 64 bm /\ getr regs 30 = Z_to_bv 64 n4 /\
  getr regs 15 = Z_to_bv 64 1 /\ getr regs 16 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 1 /\ getr regs 6 = Z_to_bv 64 1 /\
  getr regs 7 = Z_to_bv 64 1 /\ getr regs 28 = Z_to_bv 64 1 /\ getr regs 29 = Z_to_bv 64 1.

Lemma rmc_fill_loop : forall (k : nat) (fx : FPState) regs (M0 M : word -> option byte) (g rm gm bm n i : Z),
  frm_zero (@fp_csr fx) -> gconsts (@fp_regs fx) -> Z.of_nat k = (n - i)%Z -> (0 <= i < n)%Z -> (n <= 256)%Z ->
  (1 <= g)%Z -> (g + 1024 < 2 ^ 63)%Z -> (1 <= rm)%Z -> (rm + 1024 < 2 ^ 63)%Z -> (1 <= gm)%Z -> (gm + 1024 < 2 ^ 63)%Z -> (1 <= bm)%Z -> (bm + 1024 < 2 ^ 63)%Z ->
  store_ok SEGS M0 (Z_to_bv 64 g) 1024 = true ->
  arr255 SEGS M0 rm n -> arr255 SEGS M0 gm n -> arr255 SEGS M0 bm n ->
  (g + 1024 <= rm \/ rm + 4 * n <= g)%Z -> (g + 1024 <= gm \/ gm + 4 * n <= g)%Z -> (g + 1024 <= bm \/ bm + 4 * n <= g)%Z ->
  rinv [(g, 1024%Z)] M0 M ->
  fregs regs g rm gm bm (4 * n) -> getr regs 11 = Z_to_bv 64 (4 * i) ->
  exists fr' cs' regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1a920) M rom) (@mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x1a9cc) M' rom)
    /\ frm_zero cs' /\ rinv [(g, 1024%Z)] M0 M'
    /\ regs_agree (fun r => In r [8; 9; 11; 18; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros fx regs M0 M g rm gm bm n i Hz GC Hk Hi Hn Hg Hg63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 SOK Ar Ag Ab APr APg APb RI FR H11; [lia|].
  assert (CELL : forall p, (0 <= p)%Z -> (p + 1024 < 2 ^ 63)%Z -> arr255 SEGS M0 p n -> (g + 1024 <= p \/ p + 4 * n <= g)%Z ->
                 exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 (p + 4 * i + 0)) 4 = Some (Z_to_le_bytes 4 v)).
  { intros p Hp Hp63 A AP. destruct (A i Hi) as (v & Hv & R). exists v. split; [exact Hv|]. rewrite Z.add_0_r. rewrite <- R.
    apply (rinv_rdn SEGS [(g, 1024%Z)] M0 M (p + 4 * i) 4 RI); [clear - Hp Hi; lia | cbn; clear - Hp63 Hi Hn; lia|].
    intros r [<- | []]. cbn [fst snd]. clear - AP Hi. lia. }
  destruct (CELL rm ltac:(clear - Hrm; lia) Hrm63 Ar APr) as (vr & Hvr & Cr). destruct (CELL gm ltac:(clear - Hgm; lia) Hgm63 Ag APg) as (vg & Hvg & Cg).
  destruct (CELL bm ltac:(clear - Hbm; lia) Hbm63 Ab APb) as (vb & Hvb & Cb).
  assert (SOKi : store_ok SEGS M (Z_to_bv 64 (g + 4 * i)) 4 = true)
    by (apply (reg_sok SEGS M0 M g 1024 (g + 4 * i) 4 (proj1 RI) SOK ltac:(clear - Hg; lia)); cbn; clear - Hg Hg63 Hi Hn; lia).
  assert (N : (0 <= 4 * i <= 1020)%Z /\ (0 <= g + 4 * i)%Z /\ (g + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= 4 * i)%Z /\ (4 * i + 4 <= 4 * n <= 1024)%Z) by (clear - Hi Hn Hg Hg63; lia).
  destruct N as (N1 & N2 & N3 & N4 & N5).
  destruct FR as (F10 & F12 & F13 & F14 & F30 & F15 & F16 & F17 & F5 & F6 & F7 & F28 & F29).
  destruct (rmc_L1a rom fx regs M rm gm bm (4 * i) vr vg vb Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 N1 Hvr Hvg Hvb Cr Cg Cb H11 F12 F13 F14 F17 F5 F6 F7 F28 F29)
    as (r1 & RUN1 & G31 & G8 & G9 & AG1).
  replace (Z_to_bv 64 0x1a974) with (0x1a974 : word) in RUN1 by (apply bv_eq; reflexivity).
  destruct (rmc_L1f rom fx r1 M vr vg vb Hz GC ltac:(clear - Hvr; lia) ltac:(clear - Hvg; lia) ltac:(clear - Hvb; lia) G31 G8 G9) as (fr2 & cs2 & r2 & RUN2 & Hz2 & GC2 & AG2).
  replace (0x1a9a4 : word) with (Z_to_bv 64 0x1a9a4) in RUN2 by (apply bv_eq; reflexivity).
  destruct (rmc_L1c rom (mkFP fr2 cs2) r2 M g (4 * i) Hg Hg63 N1) as (r3 & RUN3 & K31 & AG3);
    try (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; assumption).
  replace (Z_to_bv 64 0x1a9bc) with (0x1a9bc : word) in RUN3 by (apply bv_eq; reflexivity).
  assert (P11 : getr r3 11 = Z_to_bv 64 (4 * i)) by (rewrite (AG3 11%bv) by notin_list; rewrite (AG2 11%bv) by notin_list; rewrite (AG1 11%bv) by notin_list; exact H11).
  assert (P30 : getr r3 30 = Z_to_bv 64 (4 * n)) by (rewrite (AG3 30%bv) by notin_list; rewrite (AG2 30%bv) by notin_list; rewrite (AG1 30%bv) by notin_list; exact F30).
  assert (KEEPR : forall r4, regs_agree (fun x => In x [8; 11]%list) r3 r4 -> fregs r4 g rm gm bm (4 * n)).
  { intros r4 AG4. unfold fregs. repeat split; (rewrite (AG4 _) by notin_list; rewrite (AG3 _) by notin_list; rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; assumption). }
  assert (AGALL : forall r4, regs_agree (fun x => In x [8; 11]%list) r3 r4 -> regs_agree (fun r => In r [8; 9; 11; 18; 31]%list) regs r4).
  { intros r4 AG4 r Hr. rewrite (AG4 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto. }
  destruct (Z.eq_dec (i + 1) n) as [LAST|MORE].
  - destruct (rmc_L1d rom true (mkFP fr2 cs2) r3 M (g + 4 * i) (4 * i) (4 * n) Hz2 N2 N3 N4 N5 SOKi ltac:(cbn; clear - LAST; lia) K31 P11 P30)
      as (cs4 & r4 & bs & RUN4 & Hz4 & Lbs & Q11 & AG4).
    replace (0x1a9cc : word) with (Z_to_bv 64 0x1a9cc) in RUN4 by (apply bv_eq; reflexivity).
    exists fr2, cs4, r4, (wbytes M (Z_to_bv 64 (g + 4 * i)) bs).
    split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact Hz4|]. split; [|exact (AGALL r4 AG4)].
    apply (rinv_wbytes [(g, 1024%Z)] M0 M (g + 4 * i) 4 bs RI); [rewrite Lbs; reflexivity | clear - N2 N3; lia | clear - N3; lia|].
    exists (g, 1024%Z). split; [left; reflexivity | cbn [fst snd]; clear - Hi Hn; lia].
  - destruct (rmc_L1d rom false (mkFP fr2 cs2) r3 M (g + 4 * i) (4 * i) (4 * n) Hz2 N2 N3 N4 N5 SOKi ltac:(cbn; clear - MORE; lia) K31 P11 P30)
      as (cs4 & r4 & bs & RUN4 & Hz4 & Lbs & Q11 & AG4).
    replace (0x1a920 : word) with (Z_to_bv 64 0x1a920) in RUN4 by (apply bv_eq; reflexivity).
    assert (RI1 : rinv [(g, 1024%Z)] M0 (wbytes M (Z_to_bv 64 (g + 4 * i)) bs)).
    { apply (rinv_wbytes [(g, 1024%Z)] M0 M (g + 4 * i) 4 bs RI); [rewrite Lbs; reflexivity | clear - N2 N3; lia | clear - N3; lia|].
      exists (g, 1024%Z). split; [left; reflexivity | cbn [fst snd]; clear - Hi Hn; lia]. }
    destruct (IH (mkFP fr2 cs4) r4 M0 _ g rm gm bm n (i + 1)%Z Hz4 GC2 ltac:(clear - Hk; lia) ltac:(clear - Hi MORE; lia) Hn Hg Hg63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63
                SOK Ar Ag Ab APr APg APb RI1 (KEEPR r4 AG4)) as (fr5 & cs5 & r5 & M5 & RUN5 & Hz5 & RI5 & AG5).
    + rewrite Q11. f_equal. clear; lia.
    + exists fr5, cs5, r5, M5.
      split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact Hz5|]. split; [exact RI5|].
      intros r Hr. rewrite (AG5 r Hr). exact (AGALL r4 AG4 r Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Raster.
Context {fx : FPState}.
Variables (s g w h wqs wqd sbase slen dbase dlen : Z) (M0 : word -> option byte).
Definition RR : list (Z * Z) := [(dbase, dlen); ((s - 112)%Z, 4%Z)].
Hypothesis GEO : (4096 <= s - 272 /\ s <= 2 ^ 47 /\ 4096 <= g /\ g + 1024 <= s - 272 /\ g mod 4 = 0 /\ 4096 <= sbase /\ 0 <= slen /\ sbase + slen <= s - 272 /\ sbase + slen + 20000 < 2 ^ 47 /\
                  4096 <= dbase /\ 0 <= dlen /\ dbase + dlen <= s - 272 /\ dbase + dlen + 20000 < 2 ^ 47 /\ 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= 4 * wqs /\ w <= 4 * wqd /\
                  0 <= wqs <= 5000 /\ 0 <= wqd <= 5000 /\ wqs * h <= 16777216 /\ wqd * h <= 16777216)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat slen) = true.
Hypothesis SOKg : store_ok SEGS M0 (Z_to_bv 64 g) 1024 = true.
Hypothesis SOKd : store_ok SEGS M0 (Z_to_bv 64 dbase) (Z.to_nat dlen) = true.
Hypothesis SOKc : store_ok SEGS M0 (Z_to_bv 64 (s - 112)) 4 = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cd : rdn SEGS M0 (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 8).
Hypothesis Cwd : rdn SEGS M0 (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 wqd).
Hypothesis Cws : rdn SEGS M0 (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 wqs).
Hypothesis Cds : rdn SEGS M0 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 sbase).
Hypothesis Cdd : rdn SEGS M0 (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 dbase).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gg & Gg2 & ALg & Gsb & Gsl & Gsb2 & Gsb3 & Gdb & Gdl & Gdb2 & Gdb3 & Gw & Gh & Gws & Gwd & Gqs & Gqd & Gsh & Gdh).

(* [comment removed for export] *)
Lemma fcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RR M0 M -> (s - 272 <= a)%Z -> (a + Z.of_nat n <= s - 112)%Z ->
  rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn R. geo. rewrite <- R. apply (rinv_rdn SEGS RR M0 M a n RI); [lia | lia|].
  intros r Hr. unfold RR in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition rowok (srow drow : Z) : Prop :=
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + slen /\ drow mod 4 = 0 /\ dbase <= drow /\ drow + 4 * wqd <= dbase + dlen)%Z.

(* [comment removed for export] *)
Definition xregs (regs : bvmap 5 word) (srow drow : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 272) /\ getr regs 10 = Z_to_bv 64 g /\ getr regs 16 = Z_to_bv 64 (2 ^ 64 - 1 - g) /\
  getr regs 27 = Z_to_bv 64 srow /\ getr regs 23 = Z_to_bv 64 srow /\ getr regs 25 = Z_to_bv 64 drow /\ getr regs 24 = Z_to_bv 64 drow /\
  getr regs 14 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 31 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 3 /\
  getr regs 1 = Z_to_bv 64 (2 ^ 31).

Lemma xregs_agree : forall regs regs' srow drow (L : list reg), xregs regs srow drow -> regs_agree (fun r => In r L) regs regs' ->
  (forall r, In r [1; 2; 10; 14; 15; 16; 17; 21; 23; 24; 25; 27; 31]%bv -> ~ In r L) -> xregs regs' srow drow.
Proof.
  intros regs regs' srow drow L (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13) AG NI. unfold xregs.
  repeat split; (rewrite (AG _) by (apply NI; cbn [In]; tauto); assumption).
Qed.

(* [comment removed for export] *)
Lemma rmc_x4_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  rowok srow drow -> (w - j <= Z.of_nat k)%Z -> (0 <= j)%Z -> (j mod 4 = 0)%Z -> (j + 4 <= w)%Z -> rinv RR M0 M ->
  xregs regs srow drow -> getr regs 7 = Z_to_bv 64 j -> getr regs 28 = Z_to_bv 64 j ->
  exists regs' M' jend,
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1adac) M rom) (@mkst fx regs' (Z_to_bv 64 0x1b45c) M' rom)
    /\ rinv RR M0 M' /\ (0 <= jend <= w)%Z /\ getr regs' 28 = Z_to_bv 64 jend /\ getr regs' 7 = Z_to_bv 64 jend /\ getr regs' 5 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [5; 7; 8; 9; 18; 28; 29; 30]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj ALj Hj4 RI XR H7 H28; [lia|]. geo.
  pose proof RO as (As & Bs1 & Bs2 & Ad & Bd1 & Bd2).
  destruct (reg_read SEGS M0 M sbase (Z.to_nat slen) (srow + j + 0) 4 wr_readable_s15 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsw & Rw).
  destruct (rdn_word_val SEGS M _ bsw Rw) as (sw & Hsw & Csw).
  destruct (lut_o_range sw Hsw) as (O0 & _ & _ & O3). pose proof (lut_u_range 40 sw) as U2. pose proof (lut_u_range 48 sw) as U1.
  assert (LUT : forall o, (0 <= o <= 1020)%Z -> exists bs, rdn SEGS M (Z_to_bv 64 (g + o)) 4 = Some bs).
  { intros o Ho. apply (reg_read SEGS M0 M g 1024 (g + o) 4 wr_readable_s15 (proj1 RI) SOKg); cbn; lia. }
  destruct (LUT _ O3) as (bs3 & C3). destruct (LUT _ U2) as (bs2 & C2). destruct (LUT _ U1) as (bs1 & C1). destruct (LUT _ O0) as (bs0 & C0).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (drow + j)) 4 = true)
    by (apply (reg_sok SEGS M0 M dbase (Z.to_nat dlen) (drow + j) 4 (proj1 RI) SOKd); rewrite ?Z2Nat.id by lia; cbn; lia).
  pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  assert (RI1 : forall v : word, rinv RR M0 (wbytes M (Z_to_bv 64 (drow + j)) (word_to_le_bytes 4 v))).
  { intros v. apply (rinv_wbytes RR M0 M (drow + j) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists (dbase, dlen). split; [left; reflexivity | cbn [fst snd]; lia]. }
  pose proof XR as (X2 & X10 & X16 & X27 & X23 & X25 & X24 & X14 & X15 & X31 & X21 & X17 & X1).
  assert (NI : forall r : reg, In r [1; 2; 10; 14; 15; 16; 17; 21; 23; 24; 25; 27; 31]%bv -> ~ In r [5; 7; 8; 9; 18; 28; 29; 30]%bv).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [notin_list|]). destruct Hr. }
  destruct (Z_lt_ge_dec (j + 7) w) as [MORE|LAST].
  - destruct (rmc_B4 rom true fx regs M s g (2 ^ 64 - 1 - g) srow drow j w sw bs3 bs2 bs1 bs0 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALg ltac:(lia) ltac:(lia) As
                ltac:(lia) ltac:(lia) Ad Hj ALj ltac:(lia) Hsw Csw CwM C3 C2 C1 C0 SOKj ltac:(left; lia) ltac:(cbn; lia) X2 X10 X16 X27 X23 X25 X24 H7 H28 X14 X15 X31 X21 X1)
      as (r1 & v & RUN & F7 & F28 & F5 & AG).
    destruct (IH r1 _ srow drow (j + 4)%Z RO ltac:(lia) ltac:(lia) ltac:(clear - ALj; rewrite Z.add_mod by lia; rewrite ALj; reflexivity) ltac:(lia) (RI1 v)
                (xregs_agree _ _ _ _ _ XR AG NI) F7 F28) as (r2 & M2 & jend & RUN2 & RI2 & Hje & G28 & G7 & G5 & AG2).
    exists r2, M2, jend. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|]. split; [exact Hje|]. split; [exact G28|]. split; [exact G7|]. split; [exact G5|].
    intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
  - destruct (rmc_B4 rom false fx regs M s g (2 ^ 64 - 1 - g) srow drow j w sw bs3 bs2 bs1 bs0 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALg ltac:(lia) ltac:(lia) As
                ltac:(lia) ltac:(lia) Ad Hj ALj ltac:(lia) Hsw Csw CwM C3 C2 C1 C0 SOKj ltac:(left; lia) ltac:(cbn; lia) X2 X10 X16 X27 X23 X25 X24 H7 H28 X14 X15 X31 X21 X1)
      as (r1 & v & RUN & F7 & F28 & F5 & AG).
    exists r1, (wbytes M (Z_to_bv 64 (drow + j)) (word_to_le_bytes 4 v)), (j + 4)%Z.
    split; [exact RUN|]. split; [exact (RI1 v)|]. split; [lia|]. split; [exact F28|]. split; [exact F7|]. split; [exact F5 | exact AG].
Qed.

(* [comment removed for export] *)
Lemma rmc_tail_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  rowok srow drow -> (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RR M0 M ->
  xregs regs srow drow -> getr regs 7 = Z_to_bv 64 j ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b460) M rom) (@mkst fx regs' (Z_to_bv 64 0x1aa28) M' rom)
    /\ rinv RR M0 M' /\ regs_agree (fun r => In r [5; 7; 28; 29]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj RI XR H7; [lia|]. geo.
  pose proof RO as (As & Bs1 & Bs2 & Ad & Bd1 & Bd2).
  pose proof (bytea_bounds srow wqs (srow + j) As ltac:(lia)) as BS. pose proof (bytea_bounds drow wqd (drow + j) Ad ltac:(lia)) as BD.
  destruct (reg_read SEGS M0 M sbase (Z.to_nat slen) (bytea (srow + j)) 1 wr_readable_s15 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsb & Cb).
  pose proof (rdv_byte_range bsb (rdn_length _ _ _ _ _ Cb)) as Rb.
  destruct (reg_read SEGS M0 M g 1024 (g + 4 * rdv false 1 bsb) 4 wr_readable_s15 (proj1 RI) SOKg ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (bsl & Cl).
  pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  assert (SOKcM : store_ok SEGS M (Z_to_bv 64 (s - 112)) 4 = true) by (apply (reg_sok SEGS M0 M (s - 112) 4 (s - 112) 4 (proj1 RI) SOKc); cbn; lia).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (bytea (drow + j))) 1 = true)
    by (apply (reg_sok SEGS M0 M dbase (Z.to_nat dlen) (bytea (drow + j)) 1 (proj1 RI) SOKd); rewrite ?Z2Nat.id by lia; cbn; lia).
  assert (RI1 : rinv RR M0 (RMCT M s drow j (Z_to_bv 64 (rdv true 4 bsl)))).
  { unfold RMCT. apply (rinv_wbytes RR M0 _ (bytea (drow + j)) 1); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | ].
    - apply (rinv_wbytes RR M0 M (s - 112) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
      exists ((s - 112)%Z, 4%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
    - exists (dbase, dlen). split; [left; reflexivity | cbn [fst snd]; lia]. }
  pose proof XR as (X2 & X10 & X16 & X27 & X23 & X25 & X24 & X14 & X15 & X31 & X21 & X17 & X1).
  assert (NI : forall r : reg, In r [1; 2; 10; 14; 15; 16; 17; 21; 23; 24; 25; 27; 31]%bv -> ~ In r [5; 7; 28; 29]%bv).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [notin_list|]). destruct Hr. }
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (rmc_TB rom true fx regs M s g srow drow j w bsb bsl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALg ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia)
                Cb Cl CwM SOKcM SOKj ltac:(left; lia) ltac:(cbn; lia) X2 X10 X27 X23 X25 X24 H7 X14 X15 X17) as (r1 & RUN & F7 & AG).
    destruct (IH r1 _ srow drow (j + 1)%Z RO ltac:(lia) ltac:(lia) RI1 (xregs_agree _ _ _ _ _ XR AG NI) F7) as (r2 & M2 & RUN2 & RI2 & AG2).
    exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|].
    intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
  - destruct (rmc_TB rom false fx regs M s g srow drow j w bsb bsl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALg ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj ltac:(lia)
                Cb Cl CwM SOKcM SOKj ltac:(left; lia) ltac:(cbn; lia) X2 X10 X27 X23 X25 X24 H7 X14 X15 X17) as (r1 & RUN & F7 & AG).
    exists r1, (RMCT M s drow j (Z_to_bv 64 (rdv true 4 bsl))). split; [exact RUN|]. split; [exact RI1 | exact AG].
Qed.

(* [comment removed for export] *)
Definition rowregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 272) /\ getr regs 10 = Z_to_bv 64 g /\ getr regs 16 = Z_to_bv 64 (2 ^ 64 - 1 - g) /\ getr regs 13 = Z_to_bv 64 i /\
  getr regs 11 = Z_to_bv 64 (wqs * i) /\ getr regs 12 = Z_to_bv 64 (wqd * i) /\ getr regs 29 = Z_to_bv 64 wqs /\
  getr regs 14 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 31 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 3.

Hypothesis LEN : (slen = 4 * (wqs * h) /\ dlen = 4 * (wqd * h) /\ sbase mod 4 = 0 /\ dbase mod 4 = 0)%Z.

(* [comment removed for export] *)
Lemma rmc_row : forall regs (M : word -> option byte) (i : Z),
  (0 <= i < h)%Z -> rinv RR M0 M -> rowregs regs i ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1aa44) M rom) (@mkst fx regs' (Z_to_bv 64 0x1aa28) M' rom)
    /\ rinv RR M0 M' /\ regs_agree (fun r => In r [1; 5; 7; 8; 9; 18; 23; 24; 25; 26; 27; 28; 29; 30]%list) regs regs'.
Proof.
  intros regs M i Hi RI (H2 & H10 & H16 & H13 & H11 & H12 & H29 & H14 & H15 & H31 & H21 & H17). geo. destruct LEN as (Ls & Ld & As & Ad).
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  set (srow := (sbase + 4 * (wqs * i))%Z). set (drow := (dbase + 4 * (wqd * i))%Z).
  assert (RO : rowok srow drow).
  { unfold rowok, srow, drow. split; [apply al4_add; exact As|]. split; [lia|]. split; [lia|]. split; [apply al4_add; exact Ad|]. split; lia. }
  pose proof (fcell M (s - 128) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cd) as CdM. pose proof (fcell M (s - 120) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  pose proof (fcell M (s - 208) 8 _ RI ltac:(lia) ltac:(cbn; lia) Cwd) as CwdM. pose proof (fcell M (s - 184) 8 _ RI ltac:(lia) ltac:(cbn; lia) Cds) as CdsM.
  pose proof (fcell M (s - 200) 8 _ RI ltac:(lia) ltac:(cbn; lia) Cdd) as CddM.
  (* [comment removed for export] *)
  assert (TAIL : forall r1 M1 j, rinv RR M0 M1 -> (0 <= j <= w)%Z -> getr r1 28 = Z_to_bv 64 j -> getr r1 7 = Z_to_bv 64 j -> getr r1 5 = Z_to_bv 64 w -> xregs r1 srow drow ->
                   exists r2 M2, msteps SEGS (@mkst fx r1 (Z_to_bv 64 0x1b45c) M1 rom) (@mkst fx r2 (Z_to_bv 64 0x1aa28) M2 rom)
                                 /\ rinv RR M0 M2 /\ regs_agree (fun r => In r [5; 7; 28; 29]%list) r1 r2).
  { intros r1 M1 j RI1 Hj G28 G7 G5 XR1. destruct (Z_lt_ge_dec j w) as [LT|GE].
    - destruct (rmc_TH rom true fx r1 M1 j w ltac:(lia) ltac:(lia) ltac:(cbn; lia) G28 G5) as (r2 & RUN2 & AG2).
      assert (XR2 : xregs r2 srow drow).
      { apply (xregs_agree r1 r2 srow drow [] XR1 AG2). intros r _ []. }
      destruct (rmc_tail_loop (Z.to_nat w) r2 M1 srow drow j RO ltac:(lia) ltac:(lia) RI1 XR2 ltac:(rewrite (AG2 7%bv) by (intros []); exact G7)) as (r3 & M3 & RUN3 & RI3 & AG3).
      exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN2 RUN3)|]. split; [exact RI3|]. intros r Hr. rewrite (AG3 r Hr). apply AG2. intros [].
    - destruct (rmc_TH rom false fx r1 M1 j w ltac:(lia) ltac:(lia) ltac:(cbn; lia) G28 G5) as (r2 & RUN2 & AG2).
      exists r2, M1. split; [exact RUN2|]. split; [exact RI1|]. intros r Hr. apply AG2. intros []. }
  assert (XRH : forall r1, regs_agree (fun r => In r [1; 5; 7; 23; 24; 25; 26; 27; 28]%list) regs r1 -> getr r1 1 = Z_to_bv 64 (2 ^ 31) ->
                getr r1 27 = Z_to_bv 64 srow -> getr r1 23 = Z_to_bv 64 srow -> getr r1 25 = Z_to_bv 64 drow -> getr r1 24 = Z_to_bv 64 drow -> xregs r1 srow drow).
  { intros r1 AG1 E1 E27 E23 E25 E24. unfold xregs. repeat split; try assumption; (rewrite (AG1 _) by notin_list; assumption). }
  destruct (Z_lt_ge_dec w 4) as [SMALL|BIG].
  - destruct (rmc_RH rom false fx regs M s w i wqs wqd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                CdM CwM CwdM CdsM CddM ltac:(cbn; lia) H2 H13 H11 H12 H29 H14 H15 H17) as (r1 & RUN1 & F5 & F7 & F28 & F1 & F27 & F23 & F25 & F24 & AG1).
    destruct (TAIL r1 M 0%Z RI ltac:(lia) F28 F7 F5 (XRH r1 AG1 F1 F27 F23 F25 F24)) as (r2 & M2 & RUN2 & RI2 & AG2).
    exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (rmc_RH rom true fx regs M s w i wqs wqd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                CdM CwM CwdM CdsM CddM ltac:(cbn; lia) H2 H13 H11 H12 H29 H14 H15 H17) as (r1 & RUN1 & F5 & F7 & F28 & F1 & F27 & F23 & F25 & F24 & AG1).
    pose proof (XRH r1 AG1 F1 F27 F23 F25 F24) as XR1.
    destruct (rmc_x4_loop (Z.to_nat w) r1 M srow drow 0%Z RO ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) RI XR1 F7 F28)
      as (r2 & M2 & jend & RUN2 & RI2 & Hje & G28 & G7 & G5 & AG2).
    assert (XR2 : xregs r2 srow drow).
    { apply (xregs_agree r1 r2 srow drow _ XR1 AG2). intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [notin_list|]). destruct Hr. }
    destruct (TAIL r2 M2 jend RI2 Hje G28 G7 G5 XR2) as (r3 & M3 & RUN3 & RI3 & AG3).
    exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma rmc_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RR M0 M -> rowregs regs i ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1aa44) M rom) (@mkst fx regs' (Z_to_bv 64 0x1b540) M' rom)
    /\ rinv RR M0 M'
    /\ regs_agree (fun r => In r [1; 5; 7; 8; 9; 11; 12; 13; 18; 23; 24; 25; 26; 27; 28; 29; 30]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI RR0; [lia|]. geo.
  destruct (rmc_row regs M i Hi RI RR0) as (r1 & M1 & RUN1 & RI1 & AG1).
  destruct RR0 as (H2 & H10 & H16 & H13 & H11 & H12 & H29 & H14 & H15 & H31 & H21 & H17).
  pose proof (fcell M1 (s - 124) 4 _ RI1 ltac:(lia) ltac:(cbn; lia) Ch) as ChM. pose proof (fcell M1 (s - 208) 8 _ RI1 ltac:(lia) ltac:(cbn; lia) Cwd) as CwdM.
  pose proof (fcell M1 (s - 256) 8 _ RI1 ltac:(lia) ltac:(cbn; lia) Cws) as CwsM.
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  assert (Psi : (0 <= wqs * i <= 20000000)%Z) by lia. assert (Pdi : (0 <= wqd * i <= 20000000)%Z) by lia.
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (rmc_RL rom false fx r1 M1 s i h wqs wqd (wqs * i) (wqd * i) ltac:(lia) Hi ltac:(lia) Gqs Gqd Psi Pdi ChM CwdM CwsM ltac:(cbn; lia))
      as (r2 & RUN2 & F13 & F11 & F12 & F29 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    destruct (IH r2 M1 (i + 1)%Z ltac:(lia) ltac:(lia) RI1) as (r3 & M3 & RUN3 & RI3 & AG3).
    { unfold rowregs. replace (wqs * (i + 1))%Z with (wqs * i + wqs)%Z by ring. replace (wqd * (i + 1))%Z with (wqd * i + wqd)%Z by ring.
      repeat split; try assumption; (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; assumption). }
    exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|].
    intros r Hr. rewrite (AG3 r Hr). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (rmc_RL rom true fx r1 M1 s i h wqs wqd (wqs * i) (wqd * i) ltac:(lia) Hi ltac:(lia) Gqs Gqd Psi Pdi ChM CwdM CwsM ltac:(cbn; lia))
      as (r2 & RUN2 & F13 & F11 & F12 & F29 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    exists r2, M1. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI1|].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

End Raster.

End Loops.
