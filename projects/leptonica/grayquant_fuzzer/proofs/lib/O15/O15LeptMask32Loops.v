(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom DitherLib DitherLoop LeptCmapArr LeptRmcLib LeptMask32Lib LeptExec LeptExecW.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15LeptBase.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL8a.
Import O15CL8a.O15LeptPixHdr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL10a.
Import O15CL10a.O15LeptCmapValid.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15LeptCmap2 O15LeptMask32Segs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL9a.
Import O15CL9a.O15LeptMask32_iface.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

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
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ w <= 32 * wqd /\ wqd <= 20000 /\ sbase mod 4 = 0 /\ dbase mod 4 = 0)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKd : store_ok SEGS M0 (Z_to_bv 64 dbase) (Z.to_nat (4 * (wqd * h))) = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 h).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & Gwd2 & As & Ad).

(* [comment removed for export] *)
Lemma b32_fcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RB M0 M -> (s - 144 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn R. geo. rewrite <- R. apply (rinv_rdn SEGS RB M0 M a n RI); [lia | lia|].
  intros r Hr. unfold RB in Hr. cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Definition b32_fix (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 13 = Z_to_bv 64 18446744071562067968 /\
  getr regs 20 = Z_to_bv 64 18446744073709551615 /\ getr regs 21 = Z_to_bv 64 18446744073709551615 /\ getr regs 22 = Z_to_bv 64 18446744073709551615 /\
  getr regs 23 = Z_to_bv 64 1 /\ getr regs 24 = Z_to_bv 64 1 /\ getr regs 25 = Z_to_bv 64 1.
Lemma b32_fix_agree : forall regs regs' L, b32_fix regs -> regs_agree (fun r => In r L) regs regs' ->
  ~ In 2%bv L -> ~ In 13%bv L -> ~ In 20%bv L -> ~ In 21%bv L -> ~ In 22%bv L -> ~ In 23%bv L -> ~ In 24%bv L -> ~ In 25%bv L -> b32_fix regs'.
Proof.
  intros regs regs' L (F2 & F13 & F20 & F21 & F22 & F23 & F24 & F25) AG N2 N13 N20 N21 N22 N23 N24 N25. unfold b32_fix.
  rewrite (AG _ N2), (AG _ N13), (AG _ N20), (AG _ N21), (AG _ N22), (AG _ N23), (AG _ N24), (AG _ N25). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma b32_pix_loop : forall (k : nat) regs (M : word -> option byte) (srow drow j : Z),
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + 4 * (wqs * h) /\ drow mod 4 = 0 /\ dbase <= drow /\ drow + 4 * wqd <= dbase + 4 * (wqd * h))%Z ->
  (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RB M0 M -> b32_fix regs ->
  getr regs 14 = Z_to_bv 64 w -> getr regs 16 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (srow + 4 * j) -> getr regs 17 = Z_to_bv 64 drow ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c594) M rom) (@mkst fx regs' (Z_to_bv 64 0x1c554) M' rom)
    /\ rinv RB M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 14; 15; 16]%list) regs regs' /\ getr regs' 14 = Z_to_bv 64 w.
Proof.
  induction k as [|k IH]; intros regs M srow drow j RO Hk Hj RI FX H14 H16 H15 H5 H17; [lia|]. geo.
  destruct RO as (Asr & Bs1 & Bs2 & Adr & Bd1 & Bd2).
  pose proof FX as (H2 & H13 & H20 & H21 & H22 & H23 & H24 & H25).
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
  destruct (b32_PX rom fx regs M s w j (srow + 4 * j) drow pw bsd ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hpw Cpw Cd CwM SOKj ltac:(left; lia)
              H2 H14 H16 H15 H5 H17 H13 H20 H21 H22 H23 H24 H25) as (r1 & M1 & RUN1 & HM1 & F14 & AG1).
  assert (RI1 : rinv RB M0 M1).
  { destruct HM1 as [-> | (v & ->)]; [exact RI|].
    apply (rinv_wbytes RB M0 M (drow + 4 * (j / 32)) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists (dbase, (4 * (wqd * h))%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (FX1 : b32_fix r1) by (apply (b32_fix_agree regs r1 _ FX AG1); notin_list).
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (b32_PL rom true fx r1 M1 w j (srow + 4 * j) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) F14)
      as (r2 & RUN2 & G16 & G15 & G5 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    assert (FX2 : b32_fix r2) by (apply (b32_fix_agree r1 r2 _ FX1 AG2); notin_list).
    destruct (IH r2 M1 srow drow (j + 1)%Z ltac:(repeat split; assumption) ltac:(lia) ltac:(lia) RI1 FX2) as (r3 & M3 & RUN3 & RI3 & AG3 & G14).
    + rewrite (AG2 _) by notin_list. exact F14.
    + exact G16.
    + exact G15.
    + rewrite G5. f_equal. lia.
    + rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H17.
    + exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|]. split; [|exact G14].
      intros r Hr. rewrite (AG3 r Hr). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (b32_PL rom false fx r1 M1 w j (srow + 4 * j) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) F14)
      as (r2 & RUN2 & G16 & G15 & G5 & AG2); try (rewrite (AG1 _) by notin_list; assumption).
    exists r2, M1. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI1|]. split.
    + intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
    + rewrite (AG2 _) by notin_list. exact F14.
Qed.

(* [comment removed for export] *)
Lemma b32_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RB M0 M -> b32_fix regs ->
  getr regs 14 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 wqd -> getr regs 9 = Z_to_bv 64 dbase ->
  getr regs 8 = Z_to_bv 64 (sbase + 4 * (wqs * i)) -> getr regs 18 = Z_to_bv 64 (4 * wqs) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c564) M rom) (@mkst fx regs' (Z_to_bv 64 0x1c414) M' rom)
    /\ rinv RB M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 8; 12; 14; 15; 16; 17]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI FX H14 H12 H11 H9 H8 H18; [lia|]. geo.
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  assert (Ei : (i * wqd = wqd * i)%Z) by ring.
  destruct (b32_RH rom fx regs M w i wqd dbase (sbase + 4 * (wqs * i)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Ei; lia) ltac:(lia) H14 H12 H11 H9 H8)
    as (r1 & RUN1 & F15 & F16 & F17 & F5 & AG1).
  assert (FX1 : b32_fix r1) by (apply (b32_fix_agree regs r1 _ FX AG1); notin_list).
  destruct (b32_pix_loop (Z.to_nat w) r1 M (sbase + 4 * (wqs * i)) (dbase + 4 * (i * wqd)) 0%Z) as (r2 & M2 & RUN2 & RI2 & AG2 & G14); try assumption.
  { rewrite Ei. split; [apply al4_add; exact As|]. split; [lia|]. split; [lia|]. split; [apply al4_add; exact Ad|]. split; lia. }
  { lia. } { lia. }
  { rewrite (AG1 _) by notin_list. exact H14. }
  { rewrite F5. f_equal. lia. }
  pose proof (b32_fcell M2 (s - 128) 4 _ RI2 ltac:(lia) ltac:(cbn; lia) Ch) as ChM.
  pose proof FX as (H2 & _).
  assert (G2 : getr r2 2 = Z_to_bv 64 (s - 144)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H2).
  assert (G12 : getr r2 12 = Z_to_bv 64 i) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H12).
  assert (G8 : getr r2 8 = Z_to_bv 64 (sbase + 4 * (wqs * i))) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H8).
  assert (G18 : getr r2 18 = Z_to_bv 64 (4 * wqs)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H18).
  assert (FX2 : b32_fix r2) by (apply (b32_fix_agree r1 r2 _ FX1 AG2); notin_list).
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (b32_RL rom true fx r2 M2 s h i (sbase + 4 * (wqs * i)) (4 * wqs) ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G12 G8 G18)
      as (r3 & RUN3 & K12 & K8 & AG3).
    assert (FX3 : b32_fix r3) by (apply (b32_fix_agree r2 r3 _ FX2 AG3); notin_list).
    destruct (IH r3 M2 (i + 1)%Z ltac:(lia) ltac:(lia) RI2 FX3) as (r4 & M4 & RUN4 & RI4 & AG4).
    + rewrite (AG3 _) by notin_list. exact G14.
    + exact K12.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H11.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H9.
    + rewrite K8. f_equal. ring.
    + rewrite (AG3 _) by notin_list. exact G18.
    + exists r4, M4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact RI4|].
      intros r Hr. rewrite (AG4 r Hr). rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (b32_RL rom false fx r2 M2 s h i (sbase + 4 * (wqs * i)) (4 * wqs) ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G12 G8 G18)
      as (r3 & RUN3 & K12 & K8 & AG3).
    exists r3, M2. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI2|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma b32_all : forall regs (pixd : Z),
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 wqd -> getr regs 8 = Z_to_bv 64 sbase -> getr regs 18 = Z_to_bv 64 wqs -> getr regs 9 = Z_to_bv 64 dbase ->
  getr regs 26 = Z_to_bv 64 pixd ->
  getr regs 20 = Z_to_bv 64 18446744073709551615 -> getr regs 21 = Z_to_bv 64 18446744073709551615 -> getr regs 22 = Z_to_bv 64 18446744073709551615 ->
  getr regs 23 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c530) M0 rom) (@mkst fx regs' (Z_to_bv 64 0x1c414) M' rom)
    /\ rinv RB M0 M' /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
Proof.
  intros regs pixd H2 H10 H8 H18 H9 H26 H20 H21 H22 H23 H24 H25. geo.
  destruct (b32_P rom fx regs M0 s w h wqd wqs pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch Cw H2 H10 H18 H26)
    as (r1 & RUN1 & F11 & F12 & F14 & F18 & F13 & F10 & AG1).
  assert (FX1 : b32_fix r1).
  { unfold b32_fix. rewrite F13. rewrite !(AG1 _) by notin_list. repeat split; assumption. }
  destruct (b32_rows (Z.to_nat h) r1 M0 0%Z ltac:(lia) ltac:(lia) (rinv_refl RB M0) FX1 F14 F12 F11) as (r2 & M2 & RUN2 & RI2 & AG2).
  { rewrite (AG1 _) by notin_list. exact H9. }
  { rewrite (AG1 _) by notin_list. rewrite H8. f_equal. lia. }
  { exact F18. }
  exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|]. split.
  - rewrite (AG2 _) by notin_list. exact F10.
  - intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Band32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Discr32.
Context {fx : FPState}.
Variables (s w h wqs wqd sbase dbase : Z) (M1 : word -> option byte).
Definition RD : list (Z * Z) := [(dbase, (4 * (wqd * h))%Z); ((s - 152)%Z, 12%Z)].
Hypothesis GEO : (4096 <= s - 160 /\ s <= 2 ^ 47 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 160 /\ 4096 <= dbase /\ dbase + 4 * (wqd * h) <= s - 160 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ w <= 32 * wqd /\ wqd <= 20000 /\ sbase mod 4 = 0 /\ dbase mod 4 = 0)%Z.
Hypothesis SOKs : store_ok SEGS M1 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKf : store_ok SEGS M1 (Z_to_bv 64 (s - 152)) 12 = true.
Hypothesis Cw : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cref : forall k, In k [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS M1 (Z_to_bv 64 (s - k)) 4 = Some (Z_to_le_bytes 4 0).

Ltac geo := pose proof GEO as (Gs & Gs47 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & Gwd2 & As & Ad).

(* [comment removed for export] *)
Lemma d32_fcell : forall (M : word -> option byte) (a : Z) (n : nat) bs, rinv RD M1 M -> (s - 160 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
  (a + Z.of_nat n <= s - 152 \/ s - 140 <= a)%Z ->
  rdn SEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs RI Ha Hn Hout R. geo. rewrite <- R. apply (rinv_rdn SEGS RD M1 M a n RI); [lia | lia|].
  intros r Hr. unfold RD in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Lemma d32_pix_loop : forall (k : nat) regs (M : word -> option byte) (srow j : Z),
  (srow mod 4 = 0 /\ sbase <= srow /\ srow + 4 * wqs <= sbase + 4 * (wqs * h))%Z ->
  (w - j <= Z.of_nat k)%Z -> (0 <= j < w)%Z -> rinv RD M1 M ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 26 = Z_to_bv 64 j -> getr regs 25 = Z_to_bv 64 j -> getr regs 18 = Z_to_bv 64 (srow + 4 * j) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c84c) M rom) (@mkst fx regs' (Z_to_bv 64 0x1c808) M' rom)
    /\ rinv RD M1 M' /\ regs_agree (fun r => In r [1; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17; 18; 25; 26]%list) regs regs' /\ getr regs' 10 = Z_to_bv 64 w.
Proof.
  induction k as [|k IH]; intros regs M srow j RO Hk Hj RI H2 H8 H22 H26 H25 H18; [lia|]. geo.
  destruct RO as (Asr & Bs1 & Bs2).
  destruct (reg_read SEGS M1 M sbase (Z.to_nat (4 * (wqs * h))) (srow + 4 * j) 4 wr_readable_m32 (proj1 RI) SOKs ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; cbn; lia)) as (bsw & Rw).
  destruct (rdn_word_val SEGS M _ bsw Rw) as (pw & Hpw & Cpw).
  assert (CR : forall k0, In k0 [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS M (Z_to_bv 64 (s - k0)) 4 = Some (Z_to_le_bytes 4 0)).
  { intros k0 Hk0. apply (d32_fcell M (s - k0) 4 _ RI); [ | | | exact (Cref k0 Hk0)]; cbn [In] in Hk0; cbn; lia. }
  assert (SOKfM : store_ok SEGS M (Z_to_bv 64 (s - 152)) 12 = true) by (apply (reg_sok SEGS M1 M (s - 152) 12 (s - 152) 12 (proj1 RI) SOKf); cbn; lia).
  pose proof (d32_fcell M (s - 108) 4 _ RI ltac:(lia) ltac:(cbn; lia) ltac:(right; lia) Cw) as CwM.
  destruct (d32_PX rom fx regs M s (srow + 4 * j) pw ltac:(lia) ltac:(lia) ltac:(lia) Hpw Cpw
              (CR 120%Z ltac:(cbn; tauto)) (CR 124%Z ltac:(cbn; tauto)) (CR 128%Z ltac:(cbn; tauto)) (CR 132%Z ltac:(cbn; tauto)) (CR 136%Z ltac:(cbn; tauto)) (CR 140%Z ltac:(cbn; tauto))
              SOKfM H2 H18 H8 H22) as (r1 & v1 & v2 & v3 & RUN1 & AG1).
  set (MX := wbytes (wbytes (wbytes M (Z_to_bv 64 (s - 144)) (word_to_le_bytes 4 v1)) (Z_to_bv 64 (s - 148)) (word_to_le_bytes 4 v2)) (Z_to_bv 64 (s - 152)) (word_to_le_bytes 4 v3)) in *.
  assert (RI1 : rinv RD M1 MX).
  { unfold MX. apply (rinv_wbytes RD M1 _ (s - 152) 4); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | ].
    - apply (rinv_wbytes RD M1 _ (s - 148) 4); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | ].
      + apply (rinv_wbytes RD M1 M (s - 144) 4 _ RI); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
        exists ((s - 152)%Z, 12%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
      + exists ((s - 152)%Z, 12%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
    - exists ((s - 152)%Z, 12%Z). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  pose proof (d32_fcell MX (s - 108) 4 _ RI1 ltac:(lia) ltac:(cbn; lia) ltac:(right; lia) Cw) as CwX.
  assert (G2 : getr r1 2 = Z_to_bv 64 (s - 160)) by (rewrite (AG1 _) by notin_list; exact H2).
  assert (G26 : getr r1 26 = Z_to_bv 64 j) by (rewrite (AG1 _) by notin_list; exact H26).
  assert (G25 : getr r1 25 = Z_to_bv 64 j) by (rewrite (AG1 _) by notin_list; exact H25).
  assert (G18 : getr r1 18 = Z_to_bv 64 (srow + 4 * j)) by (rewrite (AG1 _) by notin_list; exact H18).
  destruct (Z_lt_ge_dec (j + 1) w) as [MORE|LAST].
  - destruct (d32_PL rom true fx r1 MX s w j (srow + 4 * j) ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) CwX G2 G26 G25 G18)
      as (r2 & RUN2 & K26 & K25 & K18 & K10 & AG2).
    destruct (IH r2 MX srow (j + 1)%Z ltac:(repeat split; assumption) ltac:(lia) ltac:(lia) RI1) as (r3 & M3 & RUN3 & RI3 & AG3 & K10').
    + rewrite (AG2 _) by notin_list. exact G2.
    + rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H8.
    + rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H22.
    + exact K26.
    + exact K25.
    + rewrite K18. f_equal. lia.
    + exists r3, M3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|]. split; [|exact K10'].
      intros r Hr. rewrite (AG3 r Hr). rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (d32_PL rom false fx r1 MX s w j (srow + 4 * j) ltac:(lia) ltac:(lia) Hj ltac:(lia) ltac:(lia) ltac:(cbn; lia) CwX G2 G26 G25 G18)
      as (r2 & RUN2 & K26 & K25 & K18 & K10 & AG2).
    exists r2, MX. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI1|]. split; [|exact K10].
    intros r Hr. rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma d32_rows : forall (k : nat) regs (M : word -> option byte) (i : Z),
  Z.of_nat k = (h - i)%Z -> (0 <= i < h)%Z -> rinv RD M1 M ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 23 = Z_to_bv 64 i -> getr regs 20 = Z_to_bv 64 wqd -> getr regs 19 = Z_to_bv 64 dbase ->
  getr regs 21 = Z_to_bv 64 (sbase + 4 * (wqs * i)) -> getr regs 9 = Z_to_bv 64 (4 * wqs) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c818) M rom) (@mkst fx regs' (Z_to_bv 64 0x1c938) M' rom)
    /\ rinv RD M1 M' /\ regs_agree (fun r => In r [1; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17; 18; 21; 23; 25; 26; 27]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros regs M i Hk Hi RI H2 H8 H22 H10 H23 H20 H19 H21 H9; [lia|]. geo.
  pose proof (row_bounds wqs i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bs1 & Bs2). pose proof (row_bounds wqd i h ltac:(lia) ltac:(lia) ltac:(lia)) as (Bd1 & Bd2).
  assert (Ei : (i * wqd = wqd * i)%Z) by ring.
  destruct (d32_RH rom fx regs M w i wqd dbase (sbase + 4 * (wqs * i)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Ei; lia) ltac:(lia) H10 H23 H20 H19 H21)
    as (r1 & RUN1 & F25 & F26 & F27 & F18 & AG1).
  destruct (d32_pix_loop (Z.to_nat w) r1 M (sbase + 4 * (wqs * i)) 0%Z) as (r2 & M2 & RUN2 & RI2 & AG2 & G10); try assumption.
  { split; [apply al4_add; exact As|]. split; lia. }
  { lia. } { lia. }
  { rewrite (AG1 _) by notin_list. exact H2. } { rewrite (AG1 _) by notin_list. exact H8. } { rewrite (AG1 _) by notin_list. exact H22. }
  { rewrite F18. f_equal. lia. }
  pose proof (d32_fcell M2 (s - 112) 4 _ RI2 ltac:(lia) ltac:(cbn; lia) ltac:(right; lia) Ch) as ChM.
  assert (G2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H2).
  assert (G23 : getr r2 23 = Z_to_bv 64 i) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H23).
  assert (G21 : getr r2 21 = Z_to_bv 64 (sbase + 4 * (wqs * i))) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H21).
  assert (G9 : getr r2 9 = Z_to_bv 64 (4 * wqs)) by (rewrite (AG2 _) by notin_list; rewrite (AG1 _) by notin_list; exact H9).
  destruct (Z_lt_ge_dec (i + 1) h) as [MORE|LAST].
  - destruct (d32_RL rom true fx r2 M2 s h i (sbase + 4 * (wqs * i)) (4 * wqs) ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G23 G21 G9)
      as (r3 & RUN3 & K23 & K21 & AG3).
    destruct (IH r3 M2 (i + 1)%Z ltac:(lia) ltac:(lia) RI2) as (r4 & M4 & RUN4 & RI4 & AG4).
    + rewrite (AG3 _) by notin_list. exact G2.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H8.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H22.
    + rewrite (AG3 _) by notin_list. exact G10.
    + exact K23.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H20.
    + rewrite (AG3 _) by notin_list. rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H19.
    + rewrite K21. f_equal. ring.
    + rewrite (AG3 _) by notin_list. exact G9.
    + exists r4, M4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|]. split; [exact RI4|].
      intros r Hr. rewrite (AG4 r Hr). rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
      rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
  - destruct (d32_RL rom false fx r2 M2 s h i (sbase + 4 * (wqs * i)) (4 * wqs) ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ChM ltac:(cbn; lia) G2 G23 G21 G9)
      as (r3 & RUN3 & K23 & K21 & AG3).
    exists r3, M2. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI2|].
    intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Discr32.

(* [comment removed for export] *)
Section Discr32All.
Context {fx : FPState}.
Variables (s w h wqs wqd sbase dbase pixd : Z) (M0 : word -> option byte).
Definition RDA : list (Z * Z) := [(dbase, (4 * (wqd * h))%Z); ((s - 160)%Z, 20%Z)].
Hypothesis GEO : (4096 <= s - 160 /\ s <= 2 ^ 47 /\ 4096 <= sbase /\ sbase + 4 * (wqs * h) <= s - 160 /\ 4096 <= dbase /\ dbase + 4 * (wqd * h) <= s - 160 /\
                  1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wqs <= 20000 /\ w <= 32 * wqd /\ wqd <= 20000 /\ sbase mod 4 = 0 /\ dbase mod 4 = 0)%Z.
Hypothesis Rpixd : (0 <= pixd < 2 ^ 64)%Z.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true.
Hypothesis SOKf : store_ok SEGS M0 (Z_to_bv 64 (s - 160)) 20 = true.
Hypothesis Cw : rdn SEGS M0 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w).
Hypothesis Ch : rdn SEGS M0 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h).
Hypothesis Cref : forall k, In k [120; 124; 128; 132; 136; 140]%Z -> rdn SEGS M0 (Z_to_bv 64 (s - k)) 4 = Some (Z_to_le_bytes 4 0).

Lemma d32_all : forall regs,
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 wqd -> getr regs 21 = Z_to_bv 64 sbase -> getr regs 18 = Z_to_bv 64 wqs -> getr regs 19 = Z_to_bv 64 dbase ->
  getr regs 23 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 1 ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c7e4) M0 rom) (@mkst fx regs' (Z_to_bv 64 0x1c724) M' rom)
    /\ rinv RDA M0 M' /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs H2 H10 H21 H18 H19 H23 H8 H22. pose proof GEO as (Gs & Gs47 & Gsb & Gsb2 & Gdb & Gdb2 & Gw & Gh & Gws & Gwd & Gwd2 & As & Ad).
  assert (SOKp : store_ok SEGS M0 (Z_to_bv 64 (s - 160)) 8 = true) by (apply (reg_sok SEGS M0 M0 (s - 160) 20 (s - 160) 8 (mem_grows_refl _) SOKf); cbn; lia).
  destruct (d32_P rom fx regs M0 s w h wqd wqs pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch Cw SOKp H2 H10 H18 H23)
    as (r1 & RUN1 & F20 & F23 & F10 & F9 & F24 & AG1).
  set (M1 := wbytes M0 (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) in *.
  assert (RI01 : rinv [((s - 160)%Z, 8%Z)] M0 M1).
  { unfold M1. apply (rinv_wbytes _ M0 M0 (s - 160) 8 _ (rinv_refl _ _)); [rewrite length_N_to_le_bytes; reflexivity | lia | lia|].
    exists ((s - 160)%Z, 8%Z). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (KEEP : forall (a : Z) (n : nat) bs, (s - 152 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> rdn SEGS M0 (Z_to_bv 64 a) n = Some bs -> rdn SEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Hn R. rewrite <- R. apply (rinv_rdn SEGS _ M0 M1 a n RI01); [lia | lia|]. intros r [<- | []]. cbn [fst snd]. lia. }
  assert (Cp1 : rdn SEGS M1 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd)).
  { unfold M1. rewrite <- (w2b_Z 8 pixd Rpixd). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (GEO1 := GEO). assert (Pwh : (0 <= wqs * h)%Z) by nia.
  assert (SOKs1 : store_ok SEGS M1 (Z_to_bv 64 sbase) (Z.to_nat (4 * (wqs * h))) = true).
  { apply (reg_sok SEGS M0 M1 sbase (Z.to_nat (4 * (wqs * h))) sbase (Z.to_nat (4 * (wqs * h))) (proj1 RI01) SOKs); rewrite ?Z2Nat.id by lia; lia. }
  assert (SOKf1 : store_ok SEGS M1 (Z_to_bv 64 (s - 152)) 12 = true).
  { apply (reg_sok SEGS M0 M1 (s - 160) 20 (s - 152) 12 (proj1 RI01) SOKf); cbn; lia. }
  destruct (@d32_rows fx s w h wqs wqd sbase dbase M1 GEO1 SOKs1 SOKf1
              (KEEP (s - 108)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Cw) (KEEP (s - 112)%Z 4%nat _ ltac:(lia) ltac:(cbn; lia) Ch)
              (fun k Hk => KEEP (s - k)%Z 4%nat _ ltac:(cbn [In] in Hk; lia) ltac:(cbn [In] in Hk; cbn; lia) (Cref k Hk))
              (Z.to_nat h) r1 M1 0%Z ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r2 & M2 & RUN2 & RI2 & AG2).
  { rewrite (AG1 _) by notin_list. exact H2. } { rewrite (AG1 _) by notin_list. exact H8. } { rewrite (AG1 _) by notin_list. exact H22. }
  { exact F10. } { exact F23. } { exact F20. } { rewrite (AG1 _) by notin_list. exact H19. }
  { rewrite (AG1 _) by notin_list. rewrite H21. f_equal. lia. } { exact F9. }
  assert (Cp2 : rdn SEGS M2 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixd)).
  { rewrite <- Cp1. apply (rinv_rdn SEGS _ M1 M2 (s - 160) 8 RI2); [lia | cbn; lia|]. intros r Hr. unfold RD in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia. }
  destruct (d32_EX rom fx r2 M2 s pixd ltac:(lia) Rpixd Cp2) as (r3 & RUN3 & K10 & AG3).
  { rewrite (AG2 _) by notin_list. rewrite (AG1 _) by notin_list. exact H2. }
  exists r3, M2. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [|split; [exact K10|]].
  - apply (rinv_trans RDA M0 M1 M2).
    + apply (rinv_weaken _ RDA M0 M1 RI01). intros r [<- | []]. exists ((s - 160)%Z, 20%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
    + apply (rinv_weaken _ RDA M1 M2 RI2). intros r Hr. unfold RD in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]].
      * exists (dbase, (4 * (wqd * h))%Z). split; [left; reflexivity | cbn [fst snd]; lia].
      * exists ((s - 160)%Z, 20%Z). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - intros r Hr. rewrite (AG3 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto).
    rewrite (AG2 r) by (intros X; apply Hr; cbn [In] in X |- *; tauto). apply AG1. intros X; apply Hr; cbn [In] in X |- *; tauto.
Qed.
End Discr32All.
End Loops.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hops.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma wpl32 : forall w, (0 <= w)%Z -> wpl_of w 32 = w.
Proof. intros w Hw. unfold wpl_of. Z.div_mod_to_equations. lia. Qed.
Lemma wpl1_bounds : forall w, (1 <= w <= 20000)%Z -> (w <= 32 * wpl_of w 1 /\ 1 <= wpl_of w 1 <= 20000)%Z.
Proof. intros w Hw. unfold wpl_of. Z.div_mod_to_equations. lia. Qed.

Theorem band32_loop_hop_W : band32_loop_hop.
Proof.
  unfold band32_loop_hop, band32_HEAD, band32_EXIT, band32_WIN, band32_CLOB.
  intros fx C A Ar M md regs s w h pixd datad datas S CK HW SUB Hlo Hhi Hs16 HOK Hw1 Hh1 Ldd LRdd L0dd Lds NEds Rdd Rds ALdd ALds
         H2 H10 H8 H18 H9 H26 H20 H21 H22 H23 H24 H25 Ch Cw HC.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  destruct HOK as (_ & Hw2 & Hh2 & Hraster).
  pose proof (wpl32 w ltac:(lia)) as E32. pose proof (wpl1_bounds w ltac:(lia)) as (Bw1 & Bw2).
  assert (Pd : (0 < 4 * (wpl_of w 1 * h))%Z) by nia. assert (Ps : (0 < 4 * (wpl_of w 32 * h))%Z) by (rewrite E32; nia).
  destruct (exW_blk_rng C A M md datad _ CK HW Ldd Rdd Pd) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A M md datas _ CK HW Lds Rds Ps) as (Gs1 & Gs2 & Gs3).
  assert (GEO : (4096 <= s - 144 /\ s <= 2 ^ 47 /\ 4096 <= datas /\ datas + 4 * (wpl_of w 32 * h) <= s - 144 /\ 4096 <= datad /\ datad + 4 * (wpl_of w 1 * h) <= s - 144 /\
                 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wpl_of w 32 <= 20000 /\ w <= 32 * wpl_of w 1 /\ wpl_of w 1 <= 20000 /\ datas mod 4 = 0 /\ datad mod 4 = 0)%Z).
  { rewrite E32 in *. clear - T1 T2 T3 Hlo Hhi LV Gd1 Gd2 Gs1 Gs2 Hw1 Hw2 Hh1 Hh2 Bw1 Bw2 ALdd ALds. repeat split; try lia; Z.div_mod_to_equations; lia. }
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
         H2 H10 H21 H18 H19 H23 H8 H22 Ch Cw C1 C2 C3 C4 C5 C6 HC.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  destruct HOK as (_ & Hw2 & Hh2 & Hraster).
  pose proof (wpl32 w ltac:(lia)) as E32. pose proof (wpl1_bounds w ltac:(lia)) as (Bw1 & Bw2).
  assert (Pd : (0 < 4 * (wpl_of w 1 * h))%Z) by nia. assert (Ps : (0 < 4 * (wpl_of w 32 * h))%Z) by (rewrite E32; nia).
  destruct (exW_blk_rng C A M md datad _ CK HW Ldd Rdd Pd) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A M md datas _ CK HW Lds Rds Ps) as (Gs1 & Gs2 & Gs3).
  assert (GEO : (4096 <= s - 160 /\ s <= 2 ^ 47 /\ 4096 <= datas /\ datas + 4 * (wpl_of w 32 * h) <= s - 160 /\ 4096 <= datad /\ datad + 4 * (wpl_of w 1 * h) <= s - 160 /\
                 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ w <= wpl_of w 32 <= 20000 /\ w <= 32 * wpl_of w 1 /\ wpl_of w 1 <= 20000 /\ datas mod 4 = 0 /\ datad mod 4 = 0)%Z).
  { rewrite E32 in *. clear - T1 T2 T3 Hlo Hhi LV Gd1 Gd2 Gs1 Gs2 Hw1 Hw2 Hh1 Hh2 Bw1 Bw2 ALdd ALds. repeat split; try lia; Z.div_mod_to_equations; lia. }
  set (pz := bv_unsigned (Z_to_bv 64 pixd)).
  assert (Epz : Z_to_bv 64 pz = Z_to_bv 64 pixd) by (unfold pz; apply zbv_self).
  assert (Rpz : (0 <= pz < 2 ^ 64)%Z) by (unfold pz; apply u64_range).
  destruct (@d32_all al_rom fx s w h (wpl_of w 32) (wpl_of w 1) datas datad pz M GEO Rpz
              (blk_sok C A M _ datas _ CK HW Lds ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A M _ (s - 160) 20 CK HW ltac:(lia) ltac:(cbn; lia)) Cw Ch
              ltac:(intros k Hk; cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; assumption)
              regs) as (r' & M' & RUN & RI & F10 & AG); try assumption.
  { rewrite Epz. exact H23. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP2 C Ar A M _ M' (RDA s h (wpl_of w 1) datad) s CK HW SUB Hhi RI) as [HW' PM'].
  { unfold local_regions, RDA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    - right. exists (Z_to_bv 64 datad), (4 * (wpl_of w 1 * h))%Z. rewrite u_Z2bv by lia. split; [exact Ldd | split; [exact LRdd | split; [exact L0dd | lia]]].
    - left. lia. }
  apply (HC r' M' HW' PM' AG ltac:(rewrite <- Epz; exact F10)).
  intros x Hx1 Hx2. apply (proj2 RI). intros r Hr. unfold RDA in Hr. cbn [In] in Hr. unfold inreg. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia.
Qed.
End Hops.
