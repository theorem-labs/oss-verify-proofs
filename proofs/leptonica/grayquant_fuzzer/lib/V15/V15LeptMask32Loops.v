(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom DitherLib DitherLoop LeptCmapArr LeptRmcLib LeptMask32Lib LeptExec LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptMask32Segs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptMask32_iface.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_m32 : forall {fx : FPState}, wr_readable SEGS.
Proof.
  intros fx seg Hin Hw. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

Section Loops.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Band32.
Context {fx : FPState}.
Variables (s w h wqs wqd sbase dbase : Z) (M0 : word -> option byte).
Definition RB : list (Z * Z) := [(dbase, (4 * (wqd * h))%Z)].
Hypothesis GEO : (4096 <= s - 144 /\ s <= 2 ^ 47 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 144 /\ 4096 <= dbase /\ dbase + 4 * (wqd * h) <= s - 144 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ w <= 32 * wqd /\ wqd <= 20000 /\ sbase mod 4 = 0 /\ dbase mod 4 = 0 /\
                  wqs * h <= 16777216 /\ wqd * h <= 16777216 /\ 0 <= wqd)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKd : store_ok SEGS M0 (Z_to_bv 64 dbase) (Z.to_nat (4 * (wqd * h))) = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & Gwd2 & As & Ad & Gsh & Gdh & Gwd0).

(* [comment removed for export] *)
Lemma b32_fcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RB M0 M -> (s - 144 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn R. geo. rewrite <- R. apply (rinv_rdn SEGS RB M0 M a n RI); [lia | lia|].
  intros r Hr. unfold RB in Hr. cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition b32_fix (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 8 = Z_to_bv 64 sbase /\ getr regs 9 = Z_to_bv 64 wqs /\ getr regs 11 = Z_to_bv 64 wqd /\ getr regs 18 = Z_to_bv 64 dbase /\
  getr regs 30 = Z_to_bv 64 18446744071562067968 /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 1 /\ getr regs 29 = Z_to_bv 64 1 /\
  getr regs 6 = Z_to_bv 64 18446744073709551615 /\ getr regs 7 = Z_to_bv 64 18446744073709551615 /\ getr regs 28 = Z_to_bv 64 18446744073709551615 /\
  getr regs 16 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 1.
Lemma b32_fix_agree : forall regs regs' L, b32_fix regs -> regs_agree (fun r => In r L) regs regs' ->
  (forall r, In r [2; 8; 9; 11; 18; 30; 17; 5; 29; 6; 7; 28; 16; 15; 14]%list -> ~ In r L) -> b32_fix regs'.
Proof.
  intros regs regs' L (F2 & F8 & F9 & F11 & F18 & F30 & F17 & F5 & F29 & F6 & F7 & F28 & F16 & F15 & F14) AG N. unfold b32_fix.
  assert (K : forall r, In r [2; 8; 9; 11; 18; 30; 17; 5; 29; 6; 7; 28; 16; 15; 14]%list -> getr regs' r = getr regs r) by (intros r Hr; apply AG; apply N; exact Hr).
  rewrite !K by (cbn [In]; repeat (first [left; reflexivity | right])). repeat split; assumption.
Qed.
Ltac fixok := intros r0 Hr0; cbn [In] in Hr0; repeat (destruct Hr0 as [<- | Hr0]; [notin_list|]); destruct Hr0.

(* [comment removed for export] *)
Lemma b32_pix_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + 4 * (wqs * h) /\ drow mod 4 = 0 /\ dbase <= drow /\ drow + 4 * wqd <= dbase + 4 * (wqd * h))%Z ->
  (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RB M0 M -> b32_fix regs ->
  getr regs 24 = Z_to_bv 64 w -> getr regs 21 = Z_to_bv 64 j -> getr regs 20 = Z_to_bv 64 j -> getr regs 22 = Z_to_bv 64 (srow + 4 * j) -> getr regs 23 = Z_to_bv 64 (srow + 4 * j) ->
  getr regs 31 = Z_to_bv 64 srow -> getr regs 19 = Z_to_bv 64 drow ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e644) M rom) (@mkst fx regs' (Z_to_bv 64 0x1e598) M' rom)
    /\ rinv RB M0 M' /\ regs_agree (fun r => In r [20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj RI FX H24 H21 H20 H22 H23 H31 H19; [lia|]. geo.
  destruct RO as (Asr & Bs1 & Bs2 & Adr & Bd1 & Bd2).
  pose proof FX as (H2 & H8 & H9 & H11 & H18 & H30 & H17 & H5 & H29 & H6 & H7 & H28 & H16 & H15 & H14).
  pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as (D1 & D2).
  assert (Dw : (4 * (j / 32) + 4 <= 4 * wqd)%Z) by (clear - D2 Hj Gwd; lia).
  destruct (reg_read SEGS M0 M sbase (Z.to_nat (4 * (wqs * h))) (srow + 4 * j) 4 wr_readable_m32 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsw & Rw).
  destruct (rdn_word_val SEGS M _ bsw Rw) as (pw & Hpw & Cpw).
  destruct (reg_read SEGS M0 M dbase (Z.to_nat (4 * (wqd * h))) (drow + 4 * (j / 32)) 4 wr_readable_m32 (proj1 RI) SOKd ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsd & Cd).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (drow + 4 * (j / 32))) 4 = true)
    by (apply (reg_sok SEGS M0 M dbase (Z.to_nat (4 * (wqd * h))) (drow + 4 * (j / 32)) 4 (proj1 RI) SOKd); rewrite ?Z2Nat.id by lia; cbn; lia).
  pose proof (b32_fcell M (s - 124) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  destruct (b32_PX rom fx regs M s w j srow (srow + 4 * j) drow dbase pw bsd ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply al4_add; exact Asr)
              ltac:(lia) ltac:(lia) ltac:(lia) Adr Hpw Cpw Cd CwM SOKj ltac:(left; lia)
              H2 H24 H21 H20 H22 H23 H31 H19 H18 H30 H17 H5 H29 H6 H7 H28 H16 H15 H14) as (r1 & M1 & RUN1 & HM1 & F24 & AG1).
  assert (RI1 : rinv RB M0 M1).
  { destruct HM1 as [-> | (v & ->)]; [exact RI|].
    apply (rinv_wbytes RB M0 M (drow + 4 * (j / 32)) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists (dbase, (4 * (wqd * h))%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (FX1 : b32_fix r1) by (apply (b32_fix_agree regs r1 _ FX AG1); fixok).
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (b32_PL rom true fx r1 M1 w j (srow + 4 * j) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) F24)
      as (r2 & RUN2 & G21 & G20 & G22 & G23 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    assert (FX2 : b32_fix r2) by (apply (b32_fix_agree r1 r2 _ FX1 AG2); fixok).
    destruct (IH r2 M1 srow drow (j + 1)%Z ltac:(repeat split; assumption) ltac:(lia) ltac:(lia) RI1 FX2) as (r3 & M3 & RUN3 & RI3 & AG3).
    + rewrite (AG2 _) by notin_list. exact F24.
    + exact G21.
    + exact G20.
    + rewrite G22. f_equal. lia.
    + rewrite G23. f_equal. lia.
    + rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H31.
    + rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H19.
    + exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|].
      intros r Hr. rewrite (AG3 r Hr). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (b32_PL rom false fx r1 M1 w j (srow + 4 * j) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) F24)
      as (r2 & RUN2 & G21 & G20 & G22 & G23 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    exists r2, M1. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI1|].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma b32_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RB M0 M -> b32_fix regs ->
  getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (wqs * i) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e5a8) M rom) (@mkst fx regs' (Z_to_bv 64 0x1e368) M' rom)
    /\ rinv RB M0 M' /\ regs_agree (fun r => In r [12; 13; 19; 20; 21; 22; 23; 24; 25; 26; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI FX H13 H12; [lia|]. geo.
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  pose proof FX as (H2 & H8 & H9 & H11 & H18 & H30 & H17 & H5 & H29 & H6 & H7 & H28 & H16 & H15 & H14).
  pose proof (b32_fcell M (s - 124) 4 _ RI ltac:(lia) ltac:(cbn; lia) Cw) as CwM.
  destruct (b32_RH rom fx regs M s w i wqs wqd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) As ltac:(lia) ltac:(lia)
              CwM H2 H13 H12 H9 H11 H8 H18 H17 H5) as (r1 & RUN1 & F31 & F19 & F24 & F20 & F21 & F22 & F23 & AG1).
  assert (FX1 : b32_fix r1) by (apply (b32_fix_agree regs r1 _ FX AG1); fixok).
  destruct (b32_pix_loop (Z.to_nat w) r1 M (sbase + 4 * (wqs * i)) (dbase + 4 * (wqd * i)) 0%Z) as (r2 & M2 & RUN2 & RI2 & AG2); try assumption.
  { split; [apply al4_add; exact As|]. split; [lia|]. split; [lia|]. split; [apply al4_add; exact Ad|]. split; lia. }
  { lia. } { lia. }
  { rewrite F22. f_equal. lia. } { rewrite F23. f_equal. lia. }
  pose proof (b32_fcell M2 (s - 128) 4 _ RI2 ltac:(lia) ltac:(cbn; lia) Ch) as ChM.
  assert (FX2 : b32_fix r2) by (apply (b32_fix_agree r1 r2 _ FX1 AG2); fixok).
  pose proof FX2 as (G2 & _ & G9 & _).
  assert (G13 : getr r2 13 = Z_to_bv 64 i) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H13).
  assert (G12 : getr r2 12 = Z_to_bv 64 (wqs * i)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H12).
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (b32_RL rom true fx r2 M2 s h i (wqs * i) wqs ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G13 G12 G9)
      as (r3 & RUN3 & K13 & K12 & AG3).
    assert (FX3 : b32_fix r3) by (apply (b32_fix_agree r2 r3 _ FX2 AG3); fixok).
    destruct (IH r3 M2 (i + 1)%Z ltac:(lia) ltac:(lia) RI2 FX3) as (r4 & M4 & RUN4 & RI4 & AG4).
    + exact K13.
    + rewrite K12. f_equal. ring.
    + exists r4, M4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact RI4|].
      intros r Hr. rewrite (AG4 r Hr). rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (b32_RL rom false fx r2 M2 s h i (wqs * i) wqs ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G13 G12 G9)
      as (r3 & RUN3 & K13 & K12 & AG3).
    exists r3, M2. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI2|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma b32_all : forall regs (pixd : Z),
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wqd -> getr regs 8 = Z_to_bv 64 sbase -> getr regs 9 = Z_to_bv 64 wqs -> getr regs 18 = Z_to_bv 64 dbase ->
  getr regs 20 = Z_to_bv 64 pixd ->
  getr regs 22 = Z_to_bv 64 18446744073709551615 -> getr regs 24 = Z_to_bv 64 18446744073709551615 -> getr regs 25 = Z_to_bv 64 18446744073709551615 ->
  getr regs 21 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e54c) M0 rom) (@mkst fx regs' (Z_to_bv 64 0x1e368) M' rom)
    /\ rinv RB M0 M' /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs pixd H2 H10 H8 H9 H18 H20 H22 H24 H25 H21 H23 H26. geo.
  destruct (b32_P rom fx regs M0 s h wqd pixd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) ltac:(nia) ltac:(lia) ltac:(nia) Ch H2 H10 H8 H18 H20 H22 H24 H25 H21 H23 H26)
    as (r1 & RUN1 & F11 & F12 & F13 & F14 & F15 & F16 & F6 & F7 & F28 & F17 & F5 & F29 & F30 & F10 & AG1).
  assert (FX1 : b32_fix r1).
  { unfold b32_fix. rewrite F11, F30, F17, F5, F29, F6, F7, F28, F16, F15, F14. rewrite !(AG1 _) by notin_list. repeat split; assumption. }
  destruct (b32_rows (Z.to_nat h) r1 M0 0%Z ltac:(lia) ltac:(lia) (rinv_refl RB M0) FX1 F13) as (r2 & M2 & RUN2 & RI2 & AG2).
  { rewrite F12. f_equal. lia. }
  exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|]. split.
  - rewrite (AG2 _) by notin_list. exact F10.
  - intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Band32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_wb_other : forall {fx : FPState} (bs : list byte) (m : word -> option byte) (a b : Z) (n : nat),
  (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z ->
  (b + Z.of_nat n <= a \/ a + Z.of_nat (length bs) <= b)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) bs) (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof. intros fx bs m a b n Ha Ha2 Hb Hb2 D. apply rdn_wbytes_out; rewrite !u_Z2bv by lia; lia. Qed.
Lemma rdn_wb_hit8 : forall {fx : FPState} (m : word -> option byte) (a v : Z), (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 v).
Proof. intros fx m a v Ha Ha2 Hv. rewrite <- (w2b_Z 8 v Hv). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
Lemma rdn_wb_hit4z : forall {fx : FPState} (m : word -> option byte) (a v : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 4 v)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 v).
Proof.
  intros fx m a v Ha Ha2. pose proof (rdn_wbytes_hit SEGS (Z_to_le_bytes 4 v) m (Z_to_bv 64 a)) as H. rewrite length_Z_to_le_bytes in H. apply H.
  rewrite u_Z2bv by lia. cbn. lia.
Qed.

(* [comment removed for export] *)
Section Discr32Pix.
Context {fx : FPState}.
Variables (s w h wqs sbase : Z) (Mr : word -> option byte).
Definition RDp : list (Z * Z) := [((s - 152)%Z, 12%Z)].
Hypothesis GEOp : (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 208 /\
                   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ sbase mod 4 = 0)%Z.
Hypothesis SOKs : store_ok SEGS Mr (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKf : store_ok SEGS Mr (Z_to_bv 64 (s - 200)) 60 = true.
Hypothesis Cw : rdn SEGS Mr (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Cref : forall k, In k [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS Mr (Z_to_bv 64 (s - k)) 4 = Some (Z_to_le_bytes 4 0).

Lemma d32_pfcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RDp Mr M -> (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  (a + Z.of_nat n <= s - 152 \/ s - 140 <= a)%Z ->
  rdn SEGS Mr (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn Hout R. pose proof GEOp as (Gs & Gs47 & _). rewrite <- R. apply (rinv_rdn SEGS RDp Mr M a n RI); [lia | lia|].
  intros r Hr. unfold RDp in Hr. cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd]; lia.
Qed.

Lemma d32_pix_loop : forall (k : nat) regs (M : word -> option byte) (srow j : Z),
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + 4 * (wqs * h))%Z ->
  (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RDp Mr M ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 18446744071562067968 ->
  getr regs 25 = Z_to_bv 64 1 -> getr regs 27 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 srow ->
  getr regs 23 = Z_to_bv 64 j -> getr regs 19 = Z_to_bv 64 j -> getr regs 22 = Z_to_bv 64 (srow + 4 * j) -> getr regs 24 = Z_to_bv 64 (srow + 4 * j) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e9dc) M rom) (@mkst fx regs' (Z_to_bv 64 0x1e900) M' rom)
    /\ rinv RDp Mr M' /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 23; 24]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M srow j RO Hk Hj RI H2 H8 H9 H25 H27 H18 H23 H19 H22 H24; [lia|].
  pose proof GEOp as (Gs & Gs47 & Gs16 & Gsb & Gsb2 & Gw & Gh & Gws & As).
  destruct RO as (Asr & Bs1 & Bs2).
  destruct (reg_read SEGS Mr M sbase (Z.to_nat (4 * (wqs * h))) (srow + 4 * j) 4 wr_readable_m32 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsw & Rw).
  destruct (rdn_word_val SEGS M _ bsw Rw) as (pw & Hpw & Cpw).
  pose proof (px_r_range pw Hpw) as Rr. pose proof (px_m_range 40 pw) as Rg. pose proof (px_m_range 48 pw) as Rb.
  assert (SOKfM : store_ok SEGS M (Z_to_bv 64 (s - 200)) 60 = true) by (apply (reg_sok SEGS Mr M (s - 200) 60 (s - 200) 60 (proj1 RI) SOKf); cbn; lia).
  destruct (d32_PXa rom fx regs M s srow (srow + 4 * j) pw ltac:(lia) Gs16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply al4_add; exact Asr) Hpw Cpw SOKfM
              H2 H22 H24 H18 H25 H27) as (r1 & RUN1 & AG1).
  set (MX := D32C M s (px_r pw) (px_m 40 pw) (px_m 48 pw)) in *.
  assert (RI1 : rinv RDp Mr MX).
  { unfold MX, D32C. apply (rinv_wbytes RDp Mr _ (s - 152) 4); [ | rewrite length_Z_to_le_bytes; reflexivity | lia | lia | ].
    - apply (rinv_wbytes RDp Mr _ (s - 148) 4); [ | rewrite length_Z_to_le_bytes; reflexivity | lia | lia | ].
      + apply (rinv_wbytes RDp Mr M (s - 144) 4 _ RI); [rewrite length_Z_to_le_bytes; reflexivity | lia | lia|].
        exists ((s - 152)%Z, 12%Z). split; [left; reflexivity | cbn [fst snd]; lia].
      + exists ((s - 152)%Z, 12%Z). split; [left; reflexivity | cbn [fst snd]; lia].
    - exists ((s - 152)%Z, 12%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (CR : forall k0, In k0 [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS MX (Z_to_bv 64 (s - k0)) 4 = Some (Z_to_le_bytes 4 0)).
  { intros k0 Hk0. apply (d32_pfcell MX (s - k0) 4 _ RI1); [ | | | exact (Cref k0 Hk0)]; cbn [In] in Hk0; cbn; lia. }
  assert (Cvb : rdn SEGS MX (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 (px_m 48 pw))) by (unfold MX, D32C; apply rdn_wb_hit4z; lia).
  assert (Cvg : rdn SEGS MX (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 (px_m 40 pw))).
  { unfold MX, D32C. rewrite rdn_wb_other by (rewrite ?length_Z_to_le_bytes; cbn; lia). apply rdn_wb_hit4z; lia. }
  assert (Cvr : rdn SEGS MX (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 (px_r pw))).
  { unfold MX, D32C. rewrite !rdn_wb_other by (rewrite ?length_Z_to_le_bytes; cbn; lia). apply rdn_wb_hit4z; lia. }
  assert (E2 : getr r1 2 = Z_to_bv 64 (s - 208)) by (rewrite (AG1 _) by notin_list; exact H2).
  assert (E8 : getr r1 8 = Z_to_bv 64 1) by (rewrite (AG1 _) by notin_list; exact H8).
  assert (E9 : getr r1 9 = Z_to_bv 64 18446744071562067968) by (rewrite (AG1 _) by notin_list; exact H9).
  destruct (d32_PXr rom fx r1 MX s (px_r pw) ltac:(lia) Rr (CR 120%Z ltac:(cbn; tauto)) (CR 132%Z ltac:(cbn; tauto)) Cvr E2 E8 E9) as (r2 & RUN2 & F10 & F11 & AG2).
  destruct (d32_PXg rom fx r2 MX s (px_m 40 pw) ltac:(lia) Rg (CR 124%Z ltac:(cbn; tauto)) (CR 136%Z ltac:(cbn; tauto)) Cvg) as (r3 & RUN3 & F12 & F13 & AG3);
    try (rewrite (AG2 _) by notin_list; assumption).
  destruct (d32_PXb rom fx r3 MX s (px_m 48 pw) ltac:(lia) Rb (CR 128%Z ltac:(cbn; tauto)) (CR 140%Z ltac:(cbn; tauto)) Cvb) as (r4 & RUN4 & F14 & F16 & AG4);
    try (rewrite (AG3 _) by notin_list; rewrite (AG2 _) by notin_list; assumption).
  destruct (d32_PXf rom fx r4 MX (px_r pw) (px_m 40 pw) (px_m 48 pw) Rr Rg Rb) as (r5 & RUN5 & AG5).
  { rewrite (AG4 _) by notin_list. rewrite (AG3 _) by notin_list. exact F10. } { rewrite (AG4 _) by notin_list. rewrite (AG3 _) by notin_list. exact F11. }
  { rewrite (AG4 _) by notin_list. exact F12. } { rewrite (AG4 _) by notin_list. exact F13. } { exact F14. } { exact F16. }
  assert (AG15 : regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs r5).
  { intros r Hr. rewrite (AG5 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). rewrite (AG4 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto. }
  pose proof (d32_pfcell MX (s - 108) 4 _ RI1 ltac:(lia) ltac:(cbn; lia) ltac:(right; lia) Cw) as CwX.
  assert (RUN15 := msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5)))).
  assert (G2 : getr r5 2 = Z_to_bv 64 (s - 208)) by (rewrite (AG15 _) by notin_list; exact H2).
  assert (G23 : getr r5 23 = Z_to_bv 64 j) by (rewrite (AG15 _) by notin_list; exact H23).
  assert (G19 : getr r5 19 = Z_to_bv 64 j) by (rewrite (AG15 _) by notin_list; exact H19).
  assert (G22 : getr r5 22 = Z_to_bv 64 (srow + 4 * j)) by (rewrite (AG15 _) by notin_list; exact H22).
  assert (G24 : getr r5 24 = Z_to_bv 64 (srow + 4 * j)) by (rewrite (AG15 _) by notin_list; exact H24).
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (d32_PL rom true fx r5 MX s w j (srow + 4 * j) ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) CwX G2 G23 G19 G22 G24)
      as (r6 & RUN6 & K23 & K19 & K22 & K24 & AG6).
    destruct (IH r6 MX srow (j + 1)%Z ltac:(repeat split; assumption) ltac:(lia) ltac:(lia) RI1) as (r7 & M7 & RUN7 & RI7 & AG7).
    + rewrite (AG6 _) by notin_list. exact G2.
    + rewrite (AG6 _) by notin_list. rewrite (AG15 _) by notin_list. exact H8.
    + rewrite (AG6 _) by notin_list. rewrite (AG15 _) by notin_list. exact H9.
    + rewrite (AG6 _) by notin_list. rewrite (AG15 _) by notin_list. exact H25.
    + rewrite (AG6 _) by notin_list. rewrite (AG15 _) by notin_list. exact H27.
    + rewrite (AG6 _) by notin_list. rewrite (AG15 _) by notin_list. exact H18.
    + exact K23.
    + exact K19.
    + rewrite K22. f_equal. lia.
    + rewrite K24. f_equal. lia.
    + exists r7, M7. split; [exact (msteps_trans _ _ _ _ RUN15 (msteps_trans _ _ _ _ RUN6 RUN7))|]. split; [exact RI7|].
      intros r Hr. rewrite (AG7 r Hr). rewrite (AG6 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      apply AG15. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (d32_PL rom false fx r5 MX s w j (srow + 4 * j) ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) CwX G2 G23 G19 G22 G24)
      as (r6 & RUN6 & K23 & K19 & K22 & K24 & AG6).
    exists r6, MX. split; [exact (msteps_trans _ _ _ _ RUN15 RUN6)|]. split; [exact RI1|].
    intros r Hr. rewrite (AG6 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG15. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Discr32Pix.

(* [comment removed for export] *)
Section Discr32Rows.
Context {fx : FPState}.
Variables (s w h wqs wqd sbase dbase : Z) (M1 : word -> option byte).
Definition RDr : list (Z * Z) := [((s - 176)%Z, 8%Z); ((s - 160)%Z, 8%Z); ((s - 152)%Z, 12%Z)].
Hypothesis GEO : (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 208 /\ 4096 <= dbase /\ dbase + 4 * (wqd * h) <= s - 208 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ 0 <= wqd <= 20000 /\ sbase mod 4 = 0 /\
                  wqs * h <= 16777216 /\ wqd * h <= 16777216)%Z.
Hypothesis SOKs : store_ok SEGS M1 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKf : store_ok SEGS M1 (Z_to_bv 64 (s - 200)) 60 = true.
Hypothesis Cw : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cref : forall k, In k [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS M1 (Z_to_bv 64 (s - k)) 4 = Some (Z_to_le_bytes 4 0).
Hypothesis Cds : rdn SEGS M1 (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 sbase).
Hypothesis Cwd : rdn SEGS M1 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 wqd).
Hypothesis Cws : rdn SEGS M1 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 wqs).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gs16 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & As & Gsh & Gdh).

(* [comment removed for export] *)
Lemma d32_rfcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RDr M1 M -> (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  (a + Z.of_nat n <= s - 176 \/ (s - 168 <= a /\ a + Z.of_nat n <= s - 160) \/ s - 140 <= a)%Z ->
  rdn SEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn Hout R. geo. rewrite <- R. apply (rinv_rdn SEGS RDr M1 M a n RI); [lia | lia|].
  intros r Hr. unfold RDr in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd]; lia.
Qed.

Lemma d32_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RDr M1 M -> rdn SEGS M (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 (wqs * i)) ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 18446744071562067968 ->
  getr regs 25 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 1 -> getr regs 27 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 dbase ->
  getr regs 12 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 wqs ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e920) M rom) (@mkst fx regs' (Z_to_bv 64 0x1ebf0) M' rom)
    /\ rinv RDr M1 M' /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI Cacc H2 H8 H9 H25 H26 H27 H21 H12 H19; [lia|]. geo.
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  assert (FC : forall (a : Z) (n : nat) bs, (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
                (a + Z.of_nat n <= s - 176 \/ (s - 168 <= a /\ a + Z.of_nat n <= s - 160) \/ s - 140 <= a)%Z ->
                rdn SEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs) by (intros a n bs; apply d32_rfcell; exact RI).
  pose proof (FC (s - 108)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(right; right; lia) Cw) as CwM.
  pose proof (FC (s - 168)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(right; left; cbn; lia) Cds) as CdsM.
  pose proof (FC (s - 184)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(left; cbn; lia) Cwd) as CwdM.
  assert (SOKfM : store_ok SEGS M (Z_to_bv 64 (s - 200)) 60 = true) by (apply (reg_sok SEGS M1 M (s - 200) 60 (s - 200) 60 (proj1 RI) SOKf); cbn; lia).
  destruct (d32_RH rom fx regs M s w i wqs wqd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) As ltac:(lia) ltac:(lia)
              CwM CdsM CwdM Cacc SOKfM H2 H12 H19 H21 H25 H26) as (r1 & RUN1 & F18 & F20 & F19 & F23 & F22 & F24 & AG1).
  set (Ma := wbytes M (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 i))) in *.
  assert (RIa0 : rinv [((s - 160)%Z, 8%Z)] M Ma).
  { unfold Ma. apply (rinv_wbytes _ M M (s - 160) 8 _ (rinv_refl _ _)); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists ((s - 160)%Z, 8%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (RIa : rinv RDr M1 Ma).
  { apply (rinv_trans RDr M1 M Ma RI). apply (rinv_weaken _ RDr M Ma RIa0). intros r [<- | []].
    exists ((s - 160)%Z, 8%Z). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (FCa : forall (a : Z) (n : nat) bs, (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
                (a + Z.of_nat n <= s - 176 \/ (s - 168 <= a /\ a + Z.of_nat n <= s - 160) \/ s - 140 <= a)%Z ->
                rdn SEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn SEGS Ma (Z_to_bv 64 a) n = Some bs) by (intros a n bs; apply d32_rfcell; exact RIa).
  assert (Cia : rdn SEGS Ma (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 i)) by (unfold Ma; apply rdn_wb_hit8; lia).
  assert (Cacca : rdn SEGS Ma (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 (wqs * i))).
  { rewrite <- Cacc. apply (rinv_rdn SEGS _ M Ma (s - 176) 8 RIa0); [lia | cbn; lia|]. intros r [<- | []]. cbn [fst snd]. cbn. lia. }
  assert (GEOp : (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 208 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ sbase mod 4 = 0)%Z) by (repeat split; lia).
  assert (SOKsa : store_ok SEGS Ma (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true).
  { apply (reg_sok SEGS M1 Ma sbase (Z.to_nat (4 * (wqs * h))) sbase (Z.to_nat (4 * (wqs * h))) (proj1 RIa) SOKs); rewrite ?Z2Nat.id by lia; lia. }
  assert (SOKfa : store_ok SEGS Ma (Z_to_bv 64 (s - 200)) 60 = true) by (apply (reg_sok SEGS M1 Ma (s - 200) 60 (s - 200) 60 (proj1 RIa) SOKf); cbn; lia).
  destruct (@d32_pix_loop fx s w h wqs sbase Ma GEOp SOKsa SOKfa (FCa (s - 108)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(right; right; lia) Cw)
              (fun k0 Hk0 => FCa (s - k0)%Z 4%nat _ ltac:(cbn [In] in Hk0; lia) ltac:(cbn [In] in Hk0; cbn; lia) ltac:(right; right; cbn [In] in Hk0; lia) (Cref k0 Hk0))
              (Z.to_nat w) r1 Ma (sbase + 4 * (wqs * i))%Z 0%Z) as (r2 & Mb & RUN2 & RIb & AG2).
  { split; [apply al4_add; exact As|]. split; lia. }
  { lia. } { lia. } { apply rinv_refl. }
  { rewrite (AG1 _) by notin_list. exact H2. } { rewrite (AG1 _) by notin_list. exact H8. } { rewrite (AG1 _) by notin_list. exact H9. }
  { rewrite (AG1 _) by notin_list. exact H25. } { rewrite (AG1 _) by notin_list. exact H27. } { exact F18. } { exact F23. } { exact F19. }
  { rewrite F22. f_equal. lia. } { rewrite F24. f_equal. lia. }
  (* [comment removed for export] *)
  assert (KB : forall (a : Z) (n : nat), (s - 208 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> (a + Z.of_nat n <= s - 152 \/ s - 140 <= a)%Z ->
                rdn SEGS Mb (Z_to_bv 64 a) n = rdn SEGS Ma (Z_to_bv 64 a) n).
  { intros a n Ha Hn Hout. apply (rinv_rdn SEGS _ Ma Mb a n RIb); [lia | lia|]. intros r Hr. unfold RDp in Hr. cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd]. lia. }
  assert (Cib : rdn SEGS Mb (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 i)) by (rewrite KB by (cbn; lia); exact Cia).
  assert (Caccb : rdn SEGS Mb (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 (wqs * i))) by (rewrite KB by (cbn; lia); exact Cacca).
  assert (Chb : rdn SEGS Mb (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h)).
  { rewrite KB by (cbn; lia). exact (FCa (s - 112)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(right; right; lia) Ch). }
  assert (Cwsb : rdn SEGS Mb (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 wqs)).
  { rewrite KB by (cbn; lia). exact (FCa (s - 192)%Z 8%nat _ ltac:(lia) ltac:(cbn; lia) ltac:(left; cbn; lia) Cws). }
  assert (RIb1 : rinv RDr M1 Mb).
  { apply (rinv_trans RDr M1 Ma Mb RIa). apply (rinv_weaken _ RDr Ma Mb RIb). intros r Hr. unfold RDp in Hr. cbn [In] in Hr. destruct Hr as [<- | []].
    exists ((s - 152)%Z, 12%Z). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (SOKfb : store_ok SEGS Mb (Z_to_bv 64 (s - 200)) 60 = true) by (apply (reg_sok SEGS M1 Mb (s - 200) 60 (s - 200) 60 (proj1 RIb1) SOKf); cbn; lia).
  assert (G2 : getr r2 2 = Z_to_bv 64 (s - 208)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H2).
  set (Mc := wbytes Mb (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 (wqs * i + wqs)))).
  assert (RIc : rinv RDr M1 Mc).
  { unfold Mc. apply (rinv_wbytes RDr M1 Mb (s - 176) 8 _ RIb1); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists ((s - 176)%Z, 8%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (d32_RL rom true fx r2 Mb s h i (wqs * i) wqs ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Chb Cib Cwsb Caccb SOKfb ltac:(cbn; lia) G2)
      as (r3 & RUN3 & K12 & K19 & AG3). fold Mc in RUN3.
    destruct (IH r3 Mc (i + 1)%Z ltac:(lia) ltac:(lia) RIc) as (r4 & M4 & RUN4 & RI4 & AG4).
    + unfold Mc. replace (wqs * (i + 1))%Z with (wqs * i + wqs)%Z by ring. apply rdn_wb_hit8; lia.
    + rewrite (AG3 _) by notin_list. exact G2.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H8.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H9.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H25.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H26.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H27.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H21.
    + exact K12.
    + exact K19.
    + exists r4, M4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact RI4|].
      intros r Hr. rewrite (AG4 r Hr). rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (d32_RL rom false fx r2 Mb s h i (wqs * i) wqs ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Chb Cib Cwsb Caccb SOKfb ltac:(cbn; lia) G2)
      as (r3 & RUN3 & K12 & K19 & AG3). fold Mc in RUN3.
    exists r3, Mc. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RIc|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Discr32Rows.

(* [comment removed for export] *)
Section Discr32All.
Context {fx : FPState}.
Variables (s w h wqs wqd sbase dbase pixd : Z) (M0 : word -> option byte).
Definition RDA : list (Z * Z) := [((s - 200)%Z, 60%Z)].
Hypothesis GEO : (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 208 /\ 4096 <= dbase /\ dbase + 4 * (wqd * h) <= s - 208 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ 0 <= wqd <= 20000 /\ sbase mod 4 = 0 /\
                  wqs * h <= 16777216 /\ wqd * h <= 16777216)%Z.
Hypothesis Rpixd : (0 <= pixd < 2 ^ 64)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKf : store_ok SEGS M0 (Z_to_bv 64 (s - 200)) 60 = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cref : forall k, In k [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS M0 (Z_to_bv 64 (s - k)) 4 = Some (Z_to_le_bytes 4 0).

Lemma d32_all : forall regs,
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 10 = Z_to_bv 64 wqd -> getr regs 20 = Z_to_bv 64 sbase -> getr regs 19 = Z_to_bv 64 wqs -> getr regs 21 = Z_to_bv 64 dbase ->
  getr regs 18 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1e8c4) M0 rom) (@mkst fx regs' (Z_to_bv 64 0x1e808) M' rom)
    /\ rinv RDA M0 M' /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs H2 H10 H20 H19 H21 H18 H8.
  pose proof GEO as (Gs & Gs47 & Gs16 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & As & Gsh & Gdh).
  assert (Pwh : (0 <= wqs * h)%Z) by nia. assert (Pdh : (0 <= wqd * h)%Z) by nia.
  destruct (d32_P rom fx regs M0 s h wqd wqs pixd sbase dbase ltac:(lia) ltac:(lia) ltac:(lia) As ltac:(lia) Ch SOKf H2 H10 H20 H19 H21 H18)
    as (r1 & RUN1 & F12 & F25 & F26 & F27 & F9 & AG1).
  set (M1 := D32P M0 s wqd pixd sbase wqs) in *.
  assert (RI01 : rinv RDA M0 M1).
  { unfold M1, D32P. 
    repeat (apply (rinv_wbytes RDA M0 _ _ 8); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | exists ((s - 200)%Z, 60%Z); split; [left; reflexivity | cbn [fst snd]; lia] ]).
    apply rinv_refl. }
  assert (KEEP : forall (a : Z) (n : nat) bs, (s - 140 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Hn R. rewrite <- R. apply (rinv_rdn SEGS _ M0 M1 a n RI01); [lia | lia|]. intros r [<- | []]. cbn [fst snd]. lia. }
  assert (Cws1 : rdn SEGS M1 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 wqs)) by (unfold M1, D32P; apply rdn_wb_hit8; lia).
  assert (Cds1 : rdn SEGS M1 (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 sbase)).
  { unfold M1, D32P. rewrite rdn_wb_other by (rewrite ?length_N_to_le_bytes; cbn; lia). apply rdn_wb_hit8; lia. }
  assert (Cacc1 : rdn SEGS M1 (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 (wqs * 0))).
  { unfold M1, D32P. rewrite !rdn_wb_other by (rewrite ?length_N_to_le_bytes; cbn; lia). rewrite Z.mul_0_r. apply rdn_wb_hit8; lia. }
  assert (Cpx1 : rdn SEGS M1 (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 pixd)).
  { unfold M1, D32P. rewrite !rdn_wb_other by (rewrite ?length_N_to_le_bytes; cbn; lia). apply rdn_wb_hit8; lia. }
  assert (Cwd1 : rdn SEGS M1 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 wqd)).
  { unfold M1, D32P. rewrite !rdn_wb_other by (rewrite ?length_N_to_le_bytes; cbn; lia). apply rdn_wb_hit8; lia. }
  assert (SOKs1 : store_ok SEGS M1 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true).
  { apply (reg_sok SEGS M0 M1 sbase (Z.to_nat (4 * (wqs * h))) sbase (Z.to_nat (4 * (wqs * h))) (proj1 RI01) SOKs); rewrite ?Z2Nat.id by lia; lia. }
  assert (SOKf1 : store_ok SEGS M1 (Z_to_bv 64 (s - 200)) 60 = true) by (apply (reg_sok SEGS M0 M1 (s - 200) 60 (s - 200) 60 (proj1 RI01) SOKf); cbn; lia).
  assert (GEO1 := GEO).
  destruct (@d32_rows fx s w h wqs wqd sbase dbase M1 GEO1 SOKs1 SOKf1
              (KEEP (s - 108)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Cw) (KEEP (s - 112)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Ch)
              (fun k Hk => KEEP (s - k)%Z 4%nat _ ltac:(cbn [In] in Hk; lia) ltac:(cbn [In] in Hk; cbn; lia) (Cref k Hk))
              Cds1 Cwd1 Cws1 (Z.to_nat h) r1 M1 0%Z ltac:(lia) ltac:(lia) (rinv_refl _ _) Cacc1) as (r2 & M2 & RUN2 & RI2 & AG2).
  { rewrite (AG1 _) by notin_list. exact H2. } { rewrite (AG1 _) by notin_list. exact H8. } { exact F9. } { exact F25. } { exact F26. } { exact F27. }
  { rewrite (AG1 _) by notin_list. exact H21. } { exact F12. } { rewrite (AG1 _) by notin_list. exact H19. }
  assert (Cpx2 : rdn SEGS M2 (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 pixd)).
  { rewrite <- Cpx1. apply (rinv_rdn SEGS _ M1 M2 (s - 200) 8 RI2); [lia | cbn; lia|]. intros r Hr. unfold RDr in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd]; cbn; lia. }
  destruct (d32_EX rom fx r2 M2 s pixd ltac:(lia) Rpixd Cpx2) as (r3 & RUN3 & K10 & AG3).
  { rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H2. }
  exists r3, M2. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [|split; [exact K10|]].
  - apply (rinv_trans RDA M0 M1 M2 RI01). apply (rinv_weaken _ RDA M1 M2 RI2). intros r Hr. unfold RDr in Hr. cbn [In] in Hr.
    exists ((s - 200)%Z, 60%Z). split; [left; reflexivity|]. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd]; lia.
  - intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Discr32All.
End Loops.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hops.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma wpl32 : forall w, (0 <= w)%Z -> wpl_of w 32 = w.
Proof. intros w Hw. unfold wpl_of. Z.div_mod_to_equations. lia. Qed.
Lemma wpl1_bounds : forall w, (1 <= w <= 20000)%Z -> (w <= 32 * wpl_of w 1 /\ 1 <= wpl_of w 1 <= 20000 /\ wpl_of w 1 <= w)%Z.
Proof. intros w Hw. unfold wpl_of. Z.div_mod_to_equations. lia. Qed.

Theorem band32_loop_hop_W : band32_loop_hop.
Proof.
  unfold band32_loop_hop, band32_HEAD, band32_EXIT, band32_WIN, band32_CLOB.
  intros fx C A Ar M md regs s w h pixd datad datas S CK HW SUB Hlo Hhi Hs16 HOK Hw1 Hh1 Ldd LRdd L0dd Lds NEds Rdd Rds ALdd ALds
         H2 H10 H8 H9 H18 H20 H22 H24 H25 H21 H23 H26 Ch Cw HC.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  destruct HOK as (_ & Hw2 & Hh2 & Hraster).
  pose proof (wpl32 w ltac:(lia)) as E32. pose proof (wpl1_bounds w ltac:(lia)) as (Bw1 & Bw2 & Bw3).
  assert (Pd : (0 < 4 * (wpl_of w 1 * h))%Z) by nia. assert (Ps : (0 < 4 * (wpl_of w 32 * h))%Z) by (rewrite E32; nia).
  destruct (exW_blk_rng C A M md datad _ CK HW Ldd Rdd Pd) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A M md datas _ CK HW Lds Rds Ps) as (Gs1 & Gs2 & Gs3).
  assert (GEO : (4096 <= s - 144 /\ s <= 2 ^ 47 /\ 4096 <= datas /\ datas + 4 * (wpl_of w 32 * h) <= s - 144 /\ 4096 <= datad /\ datad + 4 * (wpl_of w 1 * h) <= s - 144 /\
                 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wpl_of w 32 <= 20000 /\ w <= 32 * wpl_of w 1 /\ wpl_of w 1 <= 20000 /\ datas mod 4 = 0 /\ datad mod 4 = 0 /\
                 wpl_of w 32 * h <= 16777216 /\ wpl_of w 1 * h <= 16777216 /\ 0 <= wpl_of w 1)%Z).
  { rewrite E32 in *. assert (wpl_of w 1 * h <= w * h)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
    clear - T1 T2 T3 Hlo Hhi LV Gd1 Gd2 Gs1 Gs2 Hw1 Hw2 Hh1 Hh2 Bw1 Bw2 ALdd ALds Hraster H. repeat split; try lia; Z.div_mod_to_equations; lia. }
  destruct (@b32_all al_rom fx s w h (wpl_of w 32) (wpl_of w 1) datas datad M GEO
              (blk_sok C A M _ datas _ CK HW Lds ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A M _ datad _ CK HW Ldd ltac:(lia) ltac:(lia) ltac:(lia))
              Cw Ch regs pixd) as (r' & M' & RUN & RI & F10 & AG); try assumption.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP C Ar A M _ M' (RB h (wpl_of w 1) datad) s CK HW SUB Hhi RI) as [HW' PM'].
  { unfold fresh_regions, RB. apply Forall_cons; [|apply Forall_nil]. exists (Z_to_bv 64 datad), (4 * (wpl_of w 1 * h))%Z. cbn [fst snd]. rewrite u_Z2bv by lia.
    split; [exact Ldd | split; [exact LRdd | split; [exact L0dd | lia]]]. }
  apply (HC r' M' HW' PM' AG F10).
  intros x Hx. apply (proj2 RI). intros r [<- | []]. unfold inreg. cbn [fst snd]. exact Hx.
Qed.

Theorem discr32_loop_hop_W : discr32_loop_hop.
Proof.
  unfold discr32_loop_hop, discr32_HEAD, discr32_EXIT, discr32_WIN, discr32_CLOB.
  intros fx C A Ar M md regs s w h pixd datad datas S CK HW SUB Hlo Hhi Hs16 HOK Hw1 Hh1 Ldd LRdd L0dd Lds NEds Rdd Rds ALdd ALds
         H2 H10 H20 H19 H21 H18 H8 Ch Cw C1 C2 C3 C4 C5 C6 HC.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  destruct HOK as (_ & Hw2 & Hh2 & Hraster).
  pose proof (wpl32 w ltac:(lia)) as E32. pose proof (wpl1_bounds w ltac:(lia)) as (Bw1 & Bw2 & Bw3).
  assert (Pd : (0 < 4 * (wpl_of w 1 * h))%Z) by nia. assert (Ps : (0 < 4 * (wpl_of w 32 * h))%Z) by (rewrite E32; nia).
  destruct (exW_blk_rng C A M md datad _ CK HW Ldd Rdd Pd) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A M md datas _ CK HW Lds Rds Ps) as (Gs1 & Gs2 & Gs3).
  assert (GEO : (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= datas /\ datas + 4 * (wpl_of w 32 * h) <= s - 208 /\ 4096 <= datad /\ datad + 4 * (wpl_of w 1 * h) <= s - 208 /\
                 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wpl_of w 32 <= 20000 /\ 0 <= wpl_of w 1 <= 20000 /\ datas mod 4 = 0 /\
                 wpl_of w 32 * h <= 16777216 /\ wpl_of w 1 * h <= 16777216)%Z).
  { rewrite E32 in *. assert (wpl_of w 1 * h <= w * h)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
    clear - T1 T2 T3 Hlo Hhi Hs16 LV Gd1 Gd2 Gs1 Gs2 Hw1 Hw2 Hh1 Hh2 Bw1 Bw2 ALdd ALds Hraster H. repeat split; try lia; Z.div_mod_to_equations; lia. }
  set (pz := bv_unsigned (Z_to_bv 64 pixd)).
  assert (Epz : Z_to_bv 64 pz = Z_to_bv 64 pixd) by (unfold pz; apply zbv_self).
  assert (Rpz : (0 <= pz < 2 ^ 64)%Z) by (unfold pz; apply u64_range).
  destruct (@d32_all al_rom fx s w h (wpl_of w 32) (wpl_of w 1) datas datad pz M GEO Rpz
              (blk_sok C A M _ datas _ CK HW Lds ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A M _ (s - 200) 60 CK HW ltac:(lia) ltac:(cbn; lia)) Cw Ch
              ltac:(intros k Hk; cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; assumption)
              regs) as (r' & M' & RUN & RI & F10 & AG); try assumption.
  { rewrite Epz. exact H18. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP2 C Ar A M _ M' (RDA s) s CK HW SUB Hhi RI) as [HW' PM'].
  { unfold local_regions, RDA. apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]. left. lia. }
  apply (HC r' M' HW' PM' AG ltac:(rewrite <- Epz; exact F10)).
  intros x Hx1 Hx2. apply (proj2 RI). intros r Hr. unfold RDA in Hr. cbn [In] in Hr. unfold inreg. destruct Hr as [<- | []]; cbn [fst snd]; lia.
Qed.
End Hops.
