(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_unwind BF_primary1b.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanClassSwar.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cstep := stepA; try first [if_true | if_false].
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
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
Section CA.
Variable P : acc -> Prop.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo SB CA sz : Z).
#[local] Notation c := (class_id sz).
#[local] Notation PCB := (CA + 80 * class_id sz).
#[local] Notation INST := 700248.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis SZ : 1 <= sz <= 65536.
Hypothesis SBR : 0 <= SB < 2^47.
Hypothesis SBM : SB mod 2^16 = 0.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PCA : forall a n, CA <= a -> a + Z.of_nat n <= CA + 2584 -> P (Z_to_bv 64 a, n).

Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
Notation CFRAME m s0 s1 s2 s3 s4 := (rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

(* [comment removed for export] *)
Definition ca_at_refill (t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a4 a5 a6 a7 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x3735c) SP' gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 PCB) (Z_to_bv 64 CA) (Z_to_bv 64 PCB) (Z_to_bv 64 INST) (Z_to_bv 64 c)
                 a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 CA) (Z_to_bv 64 INST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x377fc) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -48)
    /\ CFRAME m' s0 s1 s2 s3 s4.

Lemma ca_front_miss :
  forall (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) (maxc csz : word),
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)] ->
  rw_cells bsegs m PCB [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  evtA bsegs P (ca_at_refill t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf58) (Z_to_bv 64 CA) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x370ac) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until csz. intros SK MI ISB PC.
  pose proof LOC as LOC0. pose proof LOC as LOC1. aceil.
  pose proof HCA as (CA1 & CA2 & CA8). aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (class_id_spec sz SZ) as CSPEC. destruct CSPEC as (HC & CSZ1 & _).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in *; lia)) as [_ CSZ].
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  Ltac arith := repeat match goal with
                | H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                | H : mem_inv _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H
                | H : forall a n, _ -> _ -> P _ |- _ => clear H end; lia.
  Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by arith; intros K; arith.
  Ltac br1 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill K|]).
  Ltac br2 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [| kill K]).
  set (cc := c) in *.
  carve_frame 48%nat SK.
  do 7 cstep.                     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace (sz <? 1) with false by (symmetry; apply Z.ltb_ge; clear -CEILB SZ; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small sz 18446744073709551616) by (clear -CEILB SZ; lia).
  rewrite lnot_mod64 by (clear -CEILB SZ; lia). unfold Z.lnot. change (Z.pred (- sz)) with (- sz - 1) || idtac.
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by arith. clear -CEILB SZ. intros K0. Z.div_mod_to_equations. lia. }
  do 2 zstepA. br2.               (* [comment removed for export] *)
  zstepA. cstep.                  (* [comment removed for export] *)
  br1.                            (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ ?Q (MS _ _ _ _ _ ?mx _) =>
  assert (JOIN : forall (x12 x14 x15 x16 x17 x5 x6 : word),
    evtA bsegs P Q
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 t2 (Z_to_bv 64 cc) s1 (Z_to_bv 64 700248) (Z_to_bv 64 CA) x12 (Z_to_bv 64 8) x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x37240) fc None mx (seg_rom bsegs))) end.
  2:{ zstepA; if_cases KB; zify_cond KB.
      - do 29 zstepA. lazymatch goal with |- context [Z.lxor ?e 18446744073709551615] => set (sm := e) in * end.
        do 14 zstepA. lazymatch goal with |- context [Z.shiftr ?e 56] => set (pz := e) in * end.
        do 12 zstepA.
        match goal with |- context [Z_to_bv 64 (?e + -2)] => replace (e + -2) with cc by (transitivity (swar_class sz); [symmetry; subst cc; apply swar_class_ok; unfold kMidSize, kMaxSize; revert KB; rewrite ?unsigned_lit by lia; intros KB; lia| subst pz sm; reflexivity]) end.
        eapply JOIN.
      - do 2 zstepA.
        replace ((sz + 31) ≫ 5) with cc by (subst cc; unfold class_id, kMidSize, kMinSize; replace (sz <=? 512) with true by (symmetry; apply Z.leb_le; revert KB; rewrite ?unsigned_lit by lia; intros KB; lia); rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; f_equal; lia).
        cstep.
        eapply JOIN. }
  intros x12 x14 x15 x16 x17 x5 x6.
  br1.                            (* [comment removed for export] *)
  zstepA. br1.                    (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace (CA + cc * 80) with (CA + 80 * cc) by (clear; lia). set (PB := CA + 80 * cc) in *.
  zstepA. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).   (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 8 zstepA.                    (* [comment removed for export] *)
  subst PB cc. finishA.
Qed.

(* [comment removed for export] *)
Definition ca_ret (res : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (W : list (Z * Z)) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ((bv_unsigned sp - 48, bv_unsigned sp) :: W) m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Definition ca_ret_ok (res : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) (maxc : word) (ds : list word) (alloc' : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (CA + 80 * c, CA + 80 * c + 4); (CA + 2576, CA + 2584)] m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' PCB [C4 (Z_to_bv 64 (hint c - 1)); C4 maxc; C8 (Z_to_bv 64 (class_size c))]
    /\ u32arr bsegs m' (PCB + 16) ds
    /\ rw_cells bsegs m' (CA + 2576) [C8 (Z_to_bv 64 alloc')].

(* [comment removed for export] *)
Lemma ca_back_ok :
  forall (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 : word)
         (m : mem) (maxc : word) (ds : list word) (x alloc : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -48) ->
  CFRAME m s0 s1 s2 s3 s4 ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)] ->
  rw_cells bsegs m PCB [C4 (Z_to_bv 64 (hint c)); C4 maxc; C8 (Z_to_bv 64 (class_size c))] ->
  u32arr bsegs m (PCB + 16) ds -> length ds = 16%nat -> nth_error ds (Z.to_nat (hint c - 1)) = Some (Z_to_bv 64 x) -> 0 <= x < 2^32 ->
  rw_cells bsegs m (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  evtA bsegs P (ca_ret_ok (SB + c * 2^32 + 16 * x) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m maxc ds (alloc + class_size c))
    (MS (mkR (Z_to_bv 64 0x3735c) SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 c) (Z_to_bv 64 PCB) (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 8) (Z_to_bv 64 CA) (Z_to_bv 64 INST) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x3735c) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until alloc. intros MI SK FR ISB PC ARR LEN NTH XR STA.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (CA + 80 * c, CA + 80 * c + 4); (CA + 2576, CA + 2584)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof LOC as LOC1. aceil.
  pose proof HCA as (CA1 & CA2 & CA8). aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (class_id_spec sz SZ) as CSPEC. destruct CSPEC as (HC & CSZ1 & _).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in *; lia)) as [_ CSZ].
  pose proof (hint_range c HC) as CNT.
  set (cc := c) in *. set (PB := CA + 80 * cc) in *.
  cstep.                          (* [comment removed for export] *)
  zstepA. rewrite fsx32_small by (clear -CEILB CNT; lia).   (* [comment removed for export] *)
  do 3 zstepA. cstep.             (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  replace (((hint cc + -1) ≪ 32 mod 18446744073709551616) ≫ 30) with (4 * (hint cc - 1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by (clear -CEILB CNT; lia); clear -CEILB CNT; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  pose proof (u32arr_read bsegs _ _ ds (hint cc - 1) (Z_to_bv 64 x) (Z_to_bv 64 (PB + 4 * (hint cc - 1) + 16)) ARR NTH ltac:(clear -CEILB CNT; lia)
                ltac:(unfold wa; f_equal; clear; lia)) as RD.
  zstepA. clear RD.               (* [comment removed for export] *)
  rewrite fzx32_small by (clear -CEILB XR; lia).
  assert (AL8 : (CA + 2576) mod 8 = 0) by (clear -CEILB CA8; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  do 5 zstepA.                    (* [comment removed for export] *)
  zstepA. cstep.                  (* [comment removed for export] *)
  do 7 cstep.                     (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  cstep.                          (* [comment removed for export] *)
  replace (x ≪ 4 + (cc ≪ 32 + SB)) with (SB + cc * 2^32 + 16 * x) by (rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
  replace (hint cc + -1) with (hint cc - 1) in * by (clear; lia).
  change 18446744073709551616 with (2^64) in *. rewrite ?ZBridge.Z_to_bv_mod64 in *.
  subst PB cc. finishA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CA.
End RC__1.
