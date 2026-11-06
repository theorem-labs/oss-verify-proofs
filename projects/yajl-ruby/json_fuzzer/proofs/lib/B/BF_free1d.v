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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_poison BF_free_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

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

Section PUT2.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (lo T B cb g : Z) (b1 nhi nlo n : Z) (aidw : word) (shj : list byte).
Notation INST := 0xaaf58.
Notation CA := (T + 208).
Hypothesis Hn : n = nhi * 2^32 + nlo.
Definition l8 : Z := (n + 7) / 8.                  (* [comment removed for export] *)
Notation L := (8 * l8).                            (* [comment removed for export] *)
Hypothesis Hg : 8 * g = cb + 16.                   (* [comment removed for export] *)
Notation SHa := (0x7fff8000 + g).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis HTp : placed_s T 4096.
Hypothesis HCB : 0x603000 <= cb /\ cb + 16 + L <= alloc_ceiling /\ cb mod 16 = 0.   (* [comment removed for export] *)
Hypothesis HCBP : cb + 16 + L <= 0x7fff7000 \/ kHighMemBeg <= cb.                (* [comment removed for export] *)
Hypothesis HNHI : 0 <= nhi < 256. Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HN : n <= 2^27.
Hypothesis HCBT : cb + 16 + L <= T \/ T + 4096 <= cb.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 16 -> P (Z_to_bv 64 a, k).
Hypothesis PSH : forall a k, SHa <= a -> a + Z.of_nat k <= SHa + l8 -> P (Z_to_bv 64 a, k).

Definition put_frame (mx : mem) : Prop :=
  rw_cells bsegs mx (bv_unsigned sp - 80) [C8 (Z_to_bv 64 CA); C8 (Z_to_bv 64 B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition put_front_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x36ebc) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80))
                  (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a5' a6' a7'
                  (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 CA) (Z_to_bv 64 cb) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x36ec8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (SHa, SHa + l8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 80) /\ put_frame m'
    /\ rw_cells bsegs m' SHa [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfd) (Z.to_nat l8))] /\ poison_globals m'
    /\ rw_cells bsegs m' cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw].

Lemma put_front :
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv bsegs m ->
  rw_cells bsegs m 0xab270 (* [comment removed for export] *) [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 kQuarantineMin); C8 (Z_to_bv 64 0x100000)] ->
  rw_cells bsegs m 0xa5598 [C8 (Z_to_bv 64 0xabdb8)] ->                     (* [comment removed for export] *)
  rw_cells bsegs m 0xabde8 (* [comment removed for export] *) [C4 (Z_to_bv 64 0)] ->    (* [comment removed for export] *)
  poison_globals m ->
  rw_cells bsegs m cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  rw_cells bsegs m SHa [CB (Z.to_nat l8) shj] ->
  evtA bsegs P put_front_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36d18) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros SK LO MI QMAX GFL FFS PG HDR SH.
  pose proof HTp as HT. plopen HT. assert (HT : 0x1000 <= T /\ T + 4096 <= alloc_ceiling) by (split; assumption).
  pose proof HCBP as HCBP'. rewrite kHighMemBeg_val in HCBP'.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (HL8 : 0 <= l8 /\ n <= L < n + 8) by (unfold l8; Z.div_mod_to_equations; lia).
  assert (HG2 : kShadowBase + (cb + 16) / 8 = SHa) by (unfold kShadowBase; Z.div_mod_to_equations; lia).
  assert (HL82 : L / 8 = l8) by (Z.div_mod_to_equations; lia).
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  assert (MU : munch [(bv_unsigned sp - 144, bv_unsigned sp); (SHa, SHa + l8)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 80%nat SK.
  do 9 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; lia]. clear K0.
  do 3 zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  cstep. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite fzx16_small by lia.
  zstepA. (* [comment removed for export] *) rewrite fzx32_small' by lia.
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl nhi nlo 32) by lia. rewrite <- Hn.
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.land (n + 7) 18446744073709551608) with L.
  2:{ change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. unfold l8. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  call_spA (poison_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (cb + 16) L 253 shj);
    [exact SK| exact LOC0| lia| lia| eassumption| exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
    | Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia| lia| aceil; lia
    | rewrite kHighMemBeg_val; clear -CEILB HCBP' HCB; lia| lia| left; lia
    | rewrite HG2, HL82; exact SH| intros; apply PSTK; lia| exact PDAT| rewrite HG2, HL82; exact PSH|].
  rename PC into SK. rewrite HG2, HL82 in PC0. rename PC0 into SH'. clear G1 G2 G3 G4 G5 G6 G7.
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
  apply evtA_done. unfold put_front_post, put_frame. do 10 eexists. exists mZ.
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv bsegs mZ |- _ => exact H end|].
  split; [exact SK|]. split; [exact FR|]. split; [exact SH'|]. split; [exact POST| exact HDR].
Qed.

(* [comment removed for export] *)
Definition put_ret_post (mu : list (Z * Z)) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (a0v : Z) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a0v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch mu m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma put_back_ret :
  forall (qb' cnt' first' last' : Z) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  stk bsegs m lo (bv_unsigned sp - 80) -> lo <= bv_unsigned sp - 80 -> mem_inv bsegs m -> put_frame m ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt'); C8 (Z_to_bv 64 first'); C8 (Z_to_bv 64 last'); C8 (Z_to_bv 64 qb')] ->
  0 <= qb' <= 0x100000 ->
  evtA bsegs P (put_ret_post [] t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' qb')
    (MS (mkR (Z_to_bv 64 0x36ebc) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80))
              a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 CA) (Z_to_bv 64 cb) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
         F (Z_to_bv 64 0x36ebc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until t6'. intros SK LO MI FR QC HQB.
  pose proof HTp as HT. plopen HT.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold put_frame in FR.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases KD; zify_cond KD. { exfalso. revert KD. rewrite ?unsigned_lit by lia. lia. }
  zstepA. (* [comment removed for export] *)
  do 9 zstepA. (* [comment removed for export] *)
  rewrite ?Hsp. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  apply evtA_done. unfold put_ret_post. exists m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  first [exact SK | rewrite Hsp in SK; replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) in SK by lia; exact SK].
Qed.

Definition put_drain_post (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (qb' : Z) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR (Z_to_bv 64 0x36df4) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80))
                  (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 CA) (Z_to_bv 64 B) a4' a5' a6' a7'
                  (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 CA) (Z_to_bv 64 cb) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x34620) fc None m (seg_rom bsegs).

Lemma put_back_drain :
  forall (qb' cnt' first' last' : Z) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  stk bsegs m lo (bv_unsigned sp - 80) -> lo <= bv_unsigned sp - 80 -> mem_inv bsegs m -> put_frame m ->
  rw_cells bsegs m (T + 80) [C8 (Z_to_bv 64 cnt'); C8 (Z_to_bv 64 first'); C8 (Z_to_bv 64 last'); C8 (Z_to_bv 64 qb')] ->
  0x100000 < qb' < 2^64 ->
  evtA bsegs P (put_drain_post t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' qb')
    (MS (mkR (Z_to_bv 64 0x36ebc) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80))
              a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 CA) (Z_to_bv 64 cb) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
         F (Z_to_bv 64 0x36ebc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until t6'. intros SK LO MI FR QC HQB.
  pose proof HTp as HT. plopen HT.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  unfold put_frame in FR.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases KD; zify_cond KD. 2:{ exfalso. revert KD. rewrite ?unsigned_lit by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  apply evtA_done. unfold put_drain_post. rewrite ?Hsp. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma put_epi :
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (a0v : Z),
  stk bsegs m lo (bv_unsigned sp - 80) -> lo <= bv_unsigned sp - 80 -> mem_inv bsegs m -> put_frame m ->
  evtA bsegs P (put_ret_post [] t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' a0v)
    (MS (mkR (Z_to_bv 64 0x36df4) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80))
              (Z_to_bv 64 a0v) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 CA) (Z_to_bv 64 cb) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
         F (Z_to_bv 64 0x36df4) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until a0v. intros SK LO MI FR.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold put_frame in FR.
  do 9 zstepA. (* [comment removed for export] *)
  rewrite ?Hsp. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  apply evtA_done. unfold put_ret_post. exists m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  first [exact SK | rewrite Hsp in SK; replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) in SK by lia; exact SK].
Qed.
End PUT2.
(* [comment removed for export] *)
Section FEPI.
Variable P : acc -> Prop.
Variables (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (s0x s1x s2x s3x s4x s5x : word).
Variable Q : machine_state -> Prop.
Variables (m : mem) (usp lo : Z) (ow0 bpw : word) (ow1 ow2 : word) (ws : list word) (j1800 j8 : list byte).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 2128.
Hypothesis SPH : usp <= 2^47.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).

Lemma free_epi :
  mem_inv bsegs m -> stk bsegs m lo (usp + -2128) ->
  rw_cells bsegs m (usp + -2128) [C8 ow0; C4 ow1; C4 ow2] ->
  u64arr bsegs m (usp + -2112) ws -> length ws = 30%nat ->
  rw_cells bsegs m (usp + -1872) [CB 1800 j1800] -> rw_cells bsegs m (usp + -72) [C8 bpw] -> rw_cells bsegs m (usp + -64) [CB 8 j8] ->
  rw_cells bsegs m (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (stk bsegs m lo usp ->
   evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc ra) fc None m (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 0x54058) (Z_to_bv 64 (usp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x54058) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros MI SK OBJ TR LEN FJ1800 FBP FJ8 FRX CONT.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  do 7 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  pose proof (cb_of_u64arr bsegs _ _ _ TR) as FBUF. rewrite LEN in FBUF. clear TR.
  release_frame OBJ SK (usp + -2112). release_frame FBUF SK (usp + -1872). release_frame FJ1800 SK (usp + -72).
  release_frame FBP SK (usp + -64). release_frame FJ8 SK (usp + -56). release_frame FRX SK usp.
  zstepA. (* [comment removed for export] *)
  apply CONT. exact SK.
Qed.
End FEPI.
End RC__1.
