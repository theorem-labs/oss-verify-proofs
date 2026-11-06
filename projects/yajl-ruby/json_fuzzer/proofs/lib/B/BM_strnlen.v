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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2 BI_region_is_poisoned BI_memchr_icp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition strnlen_entry : Z := 0x9f158.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A SB : Z) (str slack ws : list byte) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' A (str ++ Z_to_bv 8 0 :: slack)
    /\ icp_globals bsegs m' SB /\ icp_globals2 bsegs m'
    /\ shadow_window bsegs m' SB A (Z.of_nat (length str) + 1) ws.

Lemma strnlen_cstr_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A cnt SB : Z) (str slack ws : list byte) (lo : Z) (P : acc -> Prop),
  let n := Z.of_nat (length str) + 1 in
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2240 -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 cnt ->
  n <= cnt < 2^63 -> ~ In (Z_to_bv 8 0) str -> (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  n < 2^40 -> range_in_mem SB A n -> A + n + Z.of_nat (length slack) < 2^47 ->
  (A + n + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= A) ->
  bytes_at bsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals bsegs m SB -> icp_globals2 bsegs m ->
  shadow_window bsegs m SB A n ws -> range_clean SB A n ws ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, A <= a -> a + Z.of_nat k <= A + n + Z.of_nat (length slack) -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, bv_unsigned sp - 2240 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A SB str slack ws m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strnlen_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until P. cbv zeta. intros SK LOC LO MI -> -> HCNT NONUL PAD HN40 RIM HAN HDISJ STR G G2 SHW RC PSH PSTR PIMG PSTK.
  unfold strnlen_entry. unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof RIM as RIM'. unfold range_in_mem in RIM'.
  assert (MU : munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  pose proof (shw_geom SB A (Z.of_nat (length str) + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as GE; cbv zeta in GE.
  hideH HDISJ. hideH RIM. hideH STR. destruct SHW as [SHB SHL]. hideH SHB.
  carve_frame 32%nat SK.
  do 4 stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  unhideH HDISJ. unhideH RIM. unhideH STR. unhideH SHB.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport bsegs) in G; [ | exact MU | exact WM | cbn; lia ];
    eapply (icp_globals2_transport bsegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ];
    eapply (bytes_at_transport bsegs) in STR; [ | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia ];
    eapply (bytes_at_transport bsegs) in SHB; [ | exact MU | cbn; lia ] end.
  callA (memchr_icp_cstr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A cnt SB str slack ws lo P).
  1:{ rewrite USP. exact SK. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ assumption. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ lia. } 1:{ exact RIM. } 1:{ lia. }
  1:{ rewrite USP. lia. }
  1:{ exact STR. } 1:{ exact G. } 1:{ exact G2. }
  1:{ split; [exact SHB | exact SHL]. } 1:{ exact RC. }
  1:{ exact PSH. } 1:{ exact PSTR. } 1:{ exact PIMG. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  ret_pc_lit.
  lazymatch goal with H : stk bsegs ?mx lo _ |- _ => rename H into SK2; rewrite USP in SK2 end.
  hideH HDISJ. hideH RIM.
  zstepA. (* [comment removed for export] *) if_cases KZ; zify_cond KZ. { exfalso. lia. }
  zstepA. (* [comment removed for export] *) replace (A + Z.of_nat (length str) - A) with (Z.of_nat (length str)) by lia.
  zstepA. (* [comment removed for export] *)
  do 4 stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  release_frame FR SK2 (bv_unsigned sp).
  apply evtA_done. unfold strnlen_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End RC__1.
