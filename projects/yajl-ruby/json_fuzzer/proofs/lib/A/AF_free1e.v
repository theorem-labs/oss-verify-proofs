(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_free_kit AF_free1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

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

Section DEALLOC2.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo cb B : Z) (b1 nhi nlo frees freed : Z) (aidw uw : word) (TSD CTX T : Z).
Notation INST := 0xaa518.
Definition hk : Z := b1 + 256 * nhi.          (* [comment removed for export] *)
Definition n : Z := nhi * 2^32 + nlo.          (* [comment removed for export] *)

Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis HCB : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HB1 : 0 <= b1 < 256 /\ Z.land b1 3 = 1.          (* [comment removed for export] *)
Hypothesis HNHI : 0 <= nhi < 256.                           (* [comment removed for export] *)
Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HDR : rw_cells asegs m cb [C4 (Z_to_bv 64 (2 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw].   (* [comment removed for export] *)
Hypothesis UW : rw_cells asegs m (cb + 16) [C8 uw].                                               (* [comment removed for export] *)
Hypothesis HK1 : rw_cells asegs m 0x13f648 [C8 (Z_to_bv 64 0)].                                 (* [comment removed for export] *)
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis HT1 : 0x5cfdd0 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
Hypothesis HC : placed_s CTX 4096.        (* [comment removed for export] *)
Hypothesis HTp : placed_s T 4096.         (* [comment removed for export] *)
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis STATS : rw_cells asegs m (T + 2824) [C8 (Z_to_bv 64 frees); C8 (Z_to_bv 64 freed)].   (* [comment removed for export] *)
Hypothesis HCBT : cb + 24 <= T \/ T + 4096 <= cb.
Hypothesis HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma dealloc_walk2 :
  (forall m' (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' ->
     munch [(bv_unsigned sp - 96, bv_unsigned sp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840)] m m' ->
     rw_cells asegs m' cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
     rw_cells asegs m' (cb + 16) [C8 (Z_to_bv 64 kInvalidTidShifted)] ->
     rw_cells asegs m' (T + 2824) [C8 (Z_to_bv 64 (frees + 1)); C8 (Z_to_bv 64 (freed + n))] ->
     thread_cells m' tp TSD CTX T ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 cb) (Z_to_bv 64 (cb + 16)) (Z_to_bv 64 B) a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x36d94) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 (cb + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 B) (Z_to_bv 64 1) a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x328ec) fc None m (seg_rom asegs)).
Proof. aceil.
  intros CONT.
  destruct HC as (HC1 & HC2 & HCg & HCs). destruct HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  assert (MU : munch [(bv_unsigned sp - 96, bv_unsigned sp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 64%nat SK.
  do 9 zstepA. (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0. (* [comment removed for export] *)
  do 8 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 32%nat SK.
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  do 5 zstepA. (* [comment removed for export] *)
  release_frame FR0 SK (bv_unsigned sp + -64).
  zstepA. (* [comment removed for export] *) ret_pc_lit.
  cstep. (* [comment removed for export] *)
  do 8 zstepA. (* [comment removed for export] *)
  replace (Z.land cb 18446744073709551612) with cb.
  2:{ change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia. change (2^2) with 4. Z.div_mod_to_equations. lia. }
  replace ((Z.shiftl cb 3 mod 18446744073709551616) mod 32) with 0.
  2:{ rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  assert (HKR : 0 <= hk < 2^16) by (unfold hk; lia).
  zstepA.
  rewrite (fsx32_small' (2 + 256 * hk)) by lia.
  zstepA. (* [comment removed for export] *)
  replace (Z.land (2 + 256 * hk) 255) with 2.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256. Z.div_mod_to_equations. lia. }
  cstep. (* [comment removed for export] *)
  do 3 zstepA. (* [comment removed for export] *)
  replace (2 + 256 * hk) with (256 * hk + 2) by lia. rewrite (hdr_cas_val hk) by lia.
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (HDRB : rw_cells asegs mx cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw]) end.
  { eapply rw_cells_reshape; [| | exact HDR]; [first [cells_wf_triv | cbn; tauto]|].   (* [comment removed for export] *)
    cbn [cells_bytes cbytes map app]. unfold le4, le2. rewrite !Z_to_bv_unsigned. cbn [Z_to_le_bytes map app].
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
    unfold hk. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite ?app_nil_r.
    rewrite !(Z.mod_small _ (2^64)) by lia.
    repeat (apply f_equal2; [Z.div_mod_to_equations; lia|]). reflexivity. }
  clear HDR.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  rewrite (u8_lit b1) by lia.
  replace (Z.land b1 3) with 1 by (symmetry; exact (proj2 HB1)).
  cstep. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  call_spA (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [exact SK| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| exact HT2| lia| exact HC2| lia
    | lia| intros; apply PSTK; lia| exact PDAT| exact PCTX|].
  rename POST into SK.
  zstepA. (* [comment removed for export] *) rewrite fzx16_small by lia.
  zstepA. (* [comment removed for export] *) rewrite fzx32_small' by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z.lor (Z.shiftl nhi 32) nlo) with n by (unfold n; symmetry; apply lor_shiftl; lia).
  do 2 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 4 zstepA. (* [comment removed for export] *)
  do 9 zstepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  change (18446744073709551615 ≪ 32 mod 18446744073709551616) with kInvalidTidShifted in UW.
  eapply CONT; [exact MI0| exact SK| exact WM| exact MU| exact HDRB| exact UW| | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))].
  replace (freed + n) with (n + freed) by lia. exact STATS.
Qed.
End DEALLOC2.
End RC__1.
