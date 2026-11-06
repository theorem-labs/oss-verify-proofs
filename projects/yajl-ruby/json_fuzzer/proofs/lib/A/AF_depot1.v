(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps AsanDepot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section IMC.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (S DA off n : Z) (src : list byte) (LD : Z).
(* [comment removed for export] *)
Hypothesis HS : bytes_at asegs m S src.
Hypothesis LS : Z.of_nat (length src) = n.
Hypothesis Hn : 0 <= n.
Hypothesis Hoff : 0 <= off /\ off + n <= LD.
Hypothesis SEP : S + n <= DA + off \/ DA + off + n <= S.
Hypothesis RS : 0 <= S /\ S + n < 2^63.
Hypothesis RD : 0 <= DA /\ DA + LD < 2^63.
Hypothesis PS : forall a k, S <= a -> a + Z.of_nat k <= S + n -> P (Z_to_bv 64 a, k).
Hypothesis PD : forall a k, DA + off <= a -> a + Z.of_nat k <= DA + off + n -> P (Z_to_bv 64 a, k).

Definition imc_post : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 : word) m' (db' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DA + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(DA + off, DA + off + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' DA db' /\ Z.of_nat (length db') = LD.

Notation ST pc mm x11 x12 x13 x14 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DA + off)) x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Lemma imc_loop : forall k mm (db : list byte) i x14,
  Z.to_nat (n - i) = k -> 0 <= i < n ->
  bytes_at asegs mm S src -> u8arr asegs mm DA db -> Z.of_nat (length db) = LD ->
  munch [(DA + off, DA + off + n)] m mm -> wmono asegs m mm -> mem_inv asegs mm ->
  evtA asegs P imc_post (ST 0x653ac mm (Z_to_bv 64 (S + i)) (Z_to_bv 64 (DA + off + n)) (Z_to_bv 64 (DA + off + i)) x14).
Proof. aceil.
  induction k as [|k IH]; intros mm db i x14 Hk Hi SRC DST LDB MU WM MI; [lia|].
  pose proof (bytes_at_read asegs mm S src i 1 SRC ltac:(lia) ltac:(lia)) as RD1.
  destruct (skipn (Z.to_nat i) src) as [|b rest] eqn:SK.
  { exfalso. pose proof (f_equal (@length byte) SK) as L0. rewrite length_skipn in L0. cbn in L0. lia. }
  cbn [firstn] in RD1.
  zstepA. clear RD1.   (* [comment removed for export] *)
  pose proof (u8arr_store_ok asegs mm DA db (off + i) (Z_to_bv 64 (DA + off + i)) DST ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  stepA.               (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PD; lia | _ => idtac end.
  change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite (le1_zxb b).
  match type of DST with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write asegs mx DA db (off + i) b DST ltac:(lia)) as DST' end.
  replace (wa (DA + (off + i))) with (wa (DA + off + i)) in DST' by (unfold wa; f_equal; lia).
  clear DST. store_done. rename DST' into DST.
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K.
  - replace (DA + off + i + 1) with (DA + off + (i + 1)) by lia. replace (S + i + 1) with (S + (i + 1)) by lia.
    eapply (IH _ (upd db (Z.to_nat (off + i)) b) (i + 1)); try eassumption; try lia. rewrite upd_length. exact LDB.
  - cstep. apply evtA_done. unfold imc_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact DST|]. rewrite upd_length. exact LDB.
Qed.

Lemma imc_walk : forall x11 x13 x14,
  mem_inv asegs m -> forall db, u8arr asegs m DA db -> Z.of_nat (length db) = LD ->
  x11 = Z_to_bv 64 S -> x13 = x13 ->
  evtA asegs P imc_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DA + off)) x11 (Z_to_bv 64 n) x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x653a0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros x11 x13 x14 MI db DST LDB -> _.
  assert (MU : munch [(DA + off, DA + off + n)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. if_cases K; zify_cond K.
  - cstep. apply evtA_done. unfold imc_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact DST| exact LDB].
  - zstepA. zstepA.
    pose proof (imc_loop (Z.to_nat (n - 0)) m db 0 x14 eq_refl ltac:(lia) HS DST LDB MU WM MI) as L.
    rewrite !Z.add_0_r in L. exact L.
Qed.
End IMC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LOCK.
Variable P : acc -> Prop.

Definition lock_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo EA v : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (EA, EA + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ exists w, rw_cells asegs m' EA [C4 w].     (* [comment removed for export] *)

Lemma lock_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo EA v : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 EA -> 0xa4000 <= EA -> EA + 4 <= 0x603000 -> EA mod 4 = 0 -> 0 <= v < 2^31 ->
  rw_cells asegs m EA [C4 (Z_to_bv 64 v)] ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (lock_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo EA v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x746f8) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until v. intros SK LOC LO SPH MI -> E1 E2 AL HV CE PSTK PDAT.
  aceil.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (EA, EA + 4)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 48%nat SK.
  do 6 cstep.   (* [comment removed for export] *)
  do 4 cstep.   (* [comment removed for export] *)
  zstepA.       (* [comment removed for export] *)
  assert (SX : sx32 (Z_to_bv 64 v) = Z_to_bv 64 v).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite SX.
  zstepA. if_cases K; zify_cond K. 2:{ exfalso. lia. }
  zstepA.       (* [comment removed for export] *)
  zstepA.       (* [comment removed for export] *)
  rewrite ?SX.
  zstepA. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA.       (* [comment removed for export] *)
  cstep.        (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  do 7 cstep.   (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp). unfold lock_post. finishA.
  eexists; exact CE.
Qed.
End LOCK.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section HASH.
Variable P : acc -> Prop.

Lemma kMurM_mod : kMurM mod 18446744073709551616 = kMurM. Proof. reflexivity. Qed.

Lemma mur_add_eq : forall h k,
  Z_to_bv 64 (Z.lxor ((Z.lxor (Z.shiftr ((k * kMurM) mod 18446744073709551616) 47) ((k * kMurM) mod 18446744073709551616) * kMurM) mod 18446744073709551616) h * kMurM)
  = Z_to_bv 64 (mur_add h k).
Proof. aceil.
  intros h k. unfold mur_add, mur_mix, w64. change (2^64) with 18446744073709551616.
  apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Zmod_mod. f_equal. f_equal.
  rewrite (Z.lxor_comm _ h). f_equal. f_equal. f_equal. apply Z.lxor_comm.
Qed.

Lemma mur_final_eq : forall HF,
  Z_to_bv 64 (Z.lxor
     (Z.shiftr ((Z.lxor (Z.shiftr ((HF * kMurM) mod 18446744073709551616) 47) ((HF * kMurM) mod 18446744073709551616) * kMurM) mod 18446744073709551616) 47)
     ((Z.lxor (Z.shiftr ((HF * kMurM) mod 18446744073709551616) 47) ((HF * kMurM) mod 18446744073709551616) * kMurM) mod 18446744073709551616))
  = Z_to_bv 64 (mur_get (mur_add HF 0)).
Proof. aceil.
  intros HF. unfold mur_get, mur_add, mur_mix, w64. change (2^64) with 18446744073709551616.
  replace ((Z.lxor ((0 * kMurM) mod 18446744073709551616) (((0 * kMurM) mod 18446744073709551616) ≫ 47) * kMurM) mod 18446744073709551616) with 0 by reflexivity.
  rewrite Z.lxor_0_r. f_equal. rewrite Z.lxor_comm. f_equal; [| f_equal]; f_equal; f_equal; apply Z.lxor_comm.
Qed.

Lemma mur_add_range : forall h k, 0 <= mur_add h k < 2^64.
Proof. aceil. intros. unfold mur_add, w64. apply Z.mod_pos_bound. lia. Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) i w, nth_error l i = Some w -> skipn i l = w :: skipn (S i) l.
Proof. aceil.
  induction l as [|x l IH]; intros [|i] w H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - exact (IH i w H).
Qed.

Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (ws : list word) (len : Z).
Hypothesis MI : mem_inv asegs m.
Hypothesis ARR : u64arr asegs m A ws.
Hypothesis LEN : 1 <= len <= Z.of_nat (length ws).
Hypothesis LWS : Z.of_nat (length ws) < 2^20.
Hypothesis RA : 0 <= A /\ A + 8 * Z.of_nat (length ws) < 2^47.
Hypothesis PA : forall a n, A <= a -> a + Z.of_nat n <= A + 8 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, n).

Definition keyZ : list Z := map bv_unsigned (firstn (Z.to_nat len) ws).

Notation ST pc x11 x12 x13 x15 x16 x19 x22 x23 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 kMurM) x11 x12 x13 (Z_to_bv 64 (A + 8 * len)) x15 x16 a7 s2 x19 s4 s5 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Lemma hash_loop : forall k i h x13 x15 x16 x19 x22 x23 (Q : machine_state -> Prop),
  Z.to_nat (len - i) = k -> 0 <= i < len -> 0 <= h < 2^64 ->
  (forall x15' x16', evtA asegs P Q (ST 0x74038 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 (fold_left mur_add (skipn (Z.to_nat i) keyZ) h)) x13 x15' x16' x19 x22 x23)) ->
  evtA asegs P Q (ST 0x74014 (Z_to_bv 64 (A + 8 * i)) (Z_to_bv 64 h) x13 x15 x16 x19 x22 x23).
Proof. aceil.
  induction k as [|k IH]; intros i h x13 x15 x16 x19 x22 x23 Q Hk Hi Hh CONT; [lia|].
  destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NTH.
  2:{ exfalso. apply nth_error_None in NTH. lia. }
  pose proof (u64arr_read asegs m A ws i w (Z_to_bv 64 (A + 8 * i)) ARR NTH ltac:(lia) ltac:(reflexivity)) as RD.
  zstepA. clear RD.
  do 7 zstepA.
  rewrite kMurM_mod, mur_add_eq.
  assert (SK : skipn (Z.to_nat i) keyZ = bv_unsigned w :: skipn (Z.to_nat (i + 1)) keyZ).
  { unfold keyZ. rewrite !skipn_map. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (skipn_cons_nth (firstn (Z.to_nat len) ws) (Z.to_nat i) w); [reflexivity|].
    rewrite <- NTH. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 (Z.to_nat i) (Z.to_nat len)); [reflexivity| exfalso; lia]. }
  zstepA. if_cases K; zify_cond K.
  - replace (A + 8 * i + 8) with (A + 8 * (i + 1)) by lia.
    eapply IH; [lia| lia| apply mur_add_range|]. intros x15' x16'. rewrite SK in CONT. cbn [fold_left] in CONT. apply CONT.
  - replace (i + 1) with len in SK by lia. rewrite SK in CONT. cbn [fold_left] in CONT.
    rewrite skipn_all2 in CONT by (unfold keyZ; rewrite length_map, length_firstn; lia). cbn [fold_left] in CONT.
    replace (A + 8 * i + 8) with (A + 8 * len) by lia. apply CONT.
Qed.

(* [comment removed for export] *)
Lemma hash_walk : forall (x10 x13 x14 x15 x16 x19 x22 x23 : word) (Q : machine_state -> Prop),
  (forall x10' x11' x12' x14' x15' x16',
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10' x11' x12' (Z_to_bv 64 0x400000) x14' x15' x16' a7 s2
                         (Z_to_bv 64 (depot_hash keyZ)) s4 s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x74078) fc None m (seg_rom asegs))) ->
  (forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x31000 -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 A) (Z_to_bv 64 len) x13 x14 x15 x16 a7 s2 x19 s4 s5 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x73fdc) fc None m (seg_rom asegs)).
Proof. aceil.
  intros x10 x13 x14 x15 x16 x19 x22 x23 Q CONT PRO.
  assert (L32 : Z.land len 4294967295 = len) by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; apply Z.mod_small; lia).

  assert (T0 : Z.shiftr len 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  do 13 zstepA. rewrite !L32, !T0.
  zstepA.   (* [comment removed for export] *)
  replace (Z_to_bv 64 (A + Z.shiftl len 3)) with (Z_to_bv 64 (A + 8 * len)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (h0 := Z.lxor (w64 (8 * len * kMurM)) kMurSeed).
  replace (Z_to_bv 64 (Z.lxor ((len * 3829533694005038248) mod 18446744073709551616) 10900877739976798860)) with (Z_to_bv 64 h0).
  2:{ subst h0. unfold w64, kMurSeed. change (2^64) with 18446744073709551616.
      replace 3829533694005038248 with ((8 * kMurM) mod 18446744073709551616) by reflexivity.
      rewrite Z.mul_mod_idemp_r by lia. do 2 f_equal. lia. }
  assert (H0 : 0 <= h0 < 2^64).
  { subst h0. unfold w64. pose proof (Z.mod_pos_bound (8 * len * kMurM) (2^64) ltac:(lia)). apply lxor_lt_pow2; [lia| exact H| unfold kMurSeed; lia]. }
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 8 * 0)) by (f_equal; lia).
  change (Z_to_bv 64 14313749767032793493) with (Z_to_bv 64 kMurM).
  eapply (hash_loop (Z.to_nat (len - 0)) 0 h0); [reflexivity| lia| exact H0|].
  intros x15' x16'. cbn [Z.to_nat skipn].
  set (HF := fold_left mur_add keyZ h0).
  assert (HFR : 0 <= HF < 2^64).
  { subst HF. destruct keyZ as [|z l] eqn:KZ; [cbn; exact H0|].
    assert (GEN : forall l' a, 0 <= a < 2^64 -> 0 <= fold_left mur_add l' a < 2^64).
    { induction l' as [|y l' IH]; intros a Ha; cbn; [exact Ha| apply IH; apply mur_add_range]. }
    apply GEN. exact H0. }
  do 16 zstepA.
  rewrite !kMurM_mod, !Z.mul_0_l. rewrite !Z.shiftr_0_l, !Z.lxor_0_l. rewrite ?Z.mul_0_l. rewrite ?Zmod_0_l, ?Z.lxor_0_l.
  replace (skipn (Z.to_nat 0) keyZ) with keyZ by reflexivity. fold HF. rewrite (mur_final_eq HF).
  replace (mur_get (mur_add HF 0)) with (depot_hash keyZ).
  2:{ unfold depot_hash. subst HF h0. unfold keyZ. rewrite length_map, length_firstn. replace (Z.of_nat (Z.to_nat len `min` length ws)) with len by lia. reflexivity. }
  apply CONT.
Qed.
End HASH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FIND.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (TD : Z) (NB : list Z) (HS : list Z) (N h : Z).
(* [comment removed for export] *)
Hypothesis MI : mem_inv asegs m.
Hypothesis HTD : 0xa4000 <= TD /\ TD + 0x440010 <= 0x603000.   (* [comment removed for export] *)
Hypothesis HN : 0 <= N < 2^31 /\ N = zlen HS.
Hypothesis Hh : 0 <= h < 2^64.
Hypothesis HSR : forall i, 0 <= nth_hash HS i < 2^64.
Hypothesis HM1 : forall k, 0 <= k < kNodesMap1 -> rw_cells asegs m (TD + 0x400010 + 8 * k) [C8 (Z_to_bv 64 (nthz NB k))].
Hypothesis HND : forall i, 1 <= i <= N -> exists sid,
  rw_cells asegs m (nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock))
           [C8 (Z_to_bv 64 (nth_hash HS i)); C4 (Z_to_bv 64 (node_link HS i)); C4 sid].
Hypothesis NBC : forall i, 1 <= i <= N -> i / kDepotNodesPerBlock < zlen NB.
Hypothesis NBR : forall b, In b NB -> placed b kDepotNodeBlockBytes.   (* [comment removed for export] *)
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PNB : forall b a n, In b NB -> b <= a -> a + Z.of_nat n <= b + kDepotNodeBlockBytes -> P (Z_to_bv 64 a, n).

Notation ST pc x10 x11 x12 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 h) s4 s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff)
           (Z_to_bv 64 (TD + 0x400010)) s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Lemma find_loop : forall n cur x10 x12 (Q : machine_state -> Prop),
  Z.to_nat cur = n ->
  (cur = 0 \/ (1 <= cur <= N /\ bucket_of (nth_hash HS cur) = bucket_of h)) ->
  (forall j, cur < j <= N -> bucket_of (nth_hash HS j) = bucket_of h -> nth_hash HS j <> h) ->
  (forall i x11 x12', 1 <= i <= N -> nth_hash HS i = h -> evtA asegs P Q (ST 0x741a8 (Z_to_bv 64 i) x11 x12')) ->
  ((forall j, 1 <= j <= N -> nth_hash HS j <> h) -> forall x10' x12', evtA asegs P Q (ST 0x740fc x10' (Z_to_bv 64 0) x12')) ->
  evtA asegs P Q (ST 0x740a4 x10 (Z_to_bv 64 cur) x12).
Proof. aceil.
  induction n as [n IH] using lt_wf_ind; intros cur x10 x12 Q Hn INV1 INV2 HIT MISS.
  destruct INV1 as [->|[Hc Hb]].
  { (* [comment removed for export] *)
    zstepA. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
    apply MISS. intros j Hj EQ. apply (INV2 j ltac:(lia)); [rewrite EQ; reflexivity| exact EQ]. }
  assert (KB : 0 <= cur / kDepotNodesPerBlock < kNodesMap1).
  { unfold kDepotNodesPerBlock, kNodesMap1. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  pose proof (HM1 _ KB) as M1. destruct (HND cur ltac:(lia)) as (sid & ND).
  pose proof (NBC cur ltac:(lia)) as BC.
  assert (BIN : In (nthz NB (cur / kDepotNodesPerBlock)) NB).
  { unfold nthz. replace ((0 <=? cur / kDepotNodesPerBlock) && (cur / kDepotNodesPerBlock <? zlen NB)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    apply nth_In. unfold zlen in BC. lia. }
  pose proof (NBR _ BIN) as BR. plopen BR. unfold kDepotNodeBlockBytes in BRc; aceil. unfold kDepotNodeBlockBytes in BRs.
  pose proof (Z.mod_pos_bound cur kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)) as MB.
  set (kb := cur / kDepotNodesPerBlock) in *. set (blk := nthz NB kb) in *.
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
  do 4 zstepA.
  assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 cur) 16) = kb).
  { rewrite bv_wrap_small by (change (bv_modulus 32) with (2^32); lia). rewrite Z.shiftr_div_pow2 by lia.
    subst kb. unfold kDepotNodesPerBlock. change (2^16) with 65536.
    apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [| apply Z.div_lt_upper_bound; lia].
    assert (0 <= cur / 65536) by (apply Z.div_pos; lia). lia. }
  rewrite !SW. rewrite (Z.mod_small kb 18446744073709551616) by (unfold kNodesMap1 in KB; lia).
  replace (Z_to_bv 64 (TD + 4194320 + Z.shiftl kb 3)) with (Z_to_bv 64 (TD + 0x400010 + 8 * kb)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (MA := TD + 0x400010 + 8 * kb) in *.
  zstepA.   (* [comment removed for export] *)
  1:{ subst MA. apply PDAT; unfold kNodesMap1 in KB; lia. }
  subst MA.
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
  do 4 zstepA.
  rewrite (Z.mod_small cur 4294967296) by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2^16) with kDepotNodesPerBlock.
  replace (Z_to_bv 64 (Z.shiftl (cur mod kDepotNodesPerBlock) 4)) with (Z_to_bv 64 (16 * (cur mod kDepotNodesPerBlock)))
    by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstepA.   (* [comment removed for export] *)
  set (NA := blk + 16 * (cur mod kDepotNodesPerBlock)) in *.
  Ltac polNB BIN := try lazymatch goal with |- P _ => eapply PNB; [exact BIN| unfold kDepotNodesPerBlock in *; lia| unfold kDepotNodesPerBlock, kDepotNodeBlockBytes in *; lia] end.
  zstepA; polNB BIN.   (* [comment removed for export] *)
  zstepA; polNB BIN.   (* [comment removed for export] *)
  pose proof (node_link_spec HS cur ltac:(lia)) as (L1 & L2 & L3). cbn zeta in L1, L2, L3.
  assert (SX : sx32 (Z_to_bv 64 (node_link HS cur)) = Z_to_bv 64 (node_link HS cur)).
  { unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity. }
  rewrite SX. pose proof (HSR cur) as HC.
  zstepA. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    assert (K2' : nth_hash HS cur <> h) by (intros EQ; apply K2; rewrite EQ; reflexivity).
    eapply (IH (Z.to_nat (node_link HS cur))); [lia| reflexivity| | | exact HIT| exact MISS].
    + destruct (Z.eq_dec (node_link HS cur) 0) as [->|NZ]; [left; reflexivity| right]. split; [lia|]. rewrite (L2 ltac:(lia)). exact Hb.
    + intros j Hj Hbj. destruct (Z_lt_le_dec cur j); [apply INV2; lia|].
      destruct (Z.eq_dec j cur) as [->|NE]; [exact K2'|].
      exfalso. pose proof (L3 j ltac:(lia) ltac:(rewrite Hbj, Hb; reflexivity)). lia.
  - (* [comment removed for export] *)
    zstepA. apply HIT; [lia| symmetry; exact K2].
Qed.
End FIND.

Lemma u8arr_write_bytes : forall segs m A cs (k : Z) bs,
  u8arr segs m A cs -> 0 <= k -> (Z.to_nat k + length bs <= length cs)%nat ->
  u8arr segs (write_to_mem m (wa (A + k)) bs) A (upd_bytes cs (Z.to_nat k) bs).
Proof. aceil.
  intros segs m A cs k bs [B W] Hk Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by exact Hl. apply wr_at_write. exact W.
Qed.

Lemma bytes_at_prefix : forall segs m A bs n, bytes_at segs m A bs -> (n <= length bs)%nat -> bytes_at segs m A (firstn n bs).
Proof. aceil.
  intros segs m A bs n (B0 & B1 & BR) Hn. split; [exact B0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite (BR i ltac:(lia)). rewrite nth_error_firstn.
  destruct (Nat.ltb_spec0 i n); [reflexivity| exfalso; lia].
Qed.

End RC__1.
