(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm4RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_memcpy F_frexpl F_fmt_fp_calls.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMX Require Import ShZero IcptCells RdnCells ShLoads IcptTryinitC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Section FX.

Variable K : Z.
Variables ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q P X E : Z) (rest : list cell).
Hypothesis ST : stk rsegs m (q - K) q.
Hypothesis MI : mem_inv rsegs m.
Hypothesis CE : rw_cells rsegs m P (C4 (Z_to_bv 64 E) :: rest).
Hypothesis SEP : (P + 4 + Z.of_nat (cells_size rest) <= q - K \/ q <= P)%Z.
Hypothesis HK : (2176 <= K)%Z.
Hypothesis HQ : (0x10007fff8000 + K <= q <= 0x7fffffffff00)%Z.
Hypothesis HP : (0x10007fff8000 <= P /\ P + 4 + Z.of_nat (cells_size rest) <= 0x7fffffffff00)%Z.
Hypothesis PRE : (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z).
Hypothesis AE : aenv m.
Hypothesis ZP : zsh m P (P + 4).

Definition icpt_frexpl_postq : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - K, q); (P, P + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - K) q
    /\ rw_cells rsegs m' P (C4 (Z_to_bv 64 e') :: rest)
    /\ frexpl FREXPL_FUEL (canon X) E = Some (x', e').

Theorem icpt_frexpl_callq : evt rsegs icpt_frexpl_postq
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6b938) fc None m (seg_rom rsegs)).
Proof.
  pose proof (aenv_rt _ AE) as (G1 & G2 & _). pose proof (aenv_fx _ AE) as HGF. unfold fx_got in HGF.
  replace (0x160c18 : word) with (Z_to_bv 64 0x160c18) in G1 by (apply bv_eq; reflexivity).
  replace (0x169ef8 : word) with (Z_to_bv 64 0x169ef8) in G2 by (apply bv_eq; reflexivity).
  replace (0x162a90 : word) with (Z_to_bv 64 0x162a90) in HGF by (apply bv_eq; reflexivity).
  pose proof (ro8_of_rdn rsegs m 0x160c18 _ G1 ltac:(lia) ltac:(lia)) as RG1.
  pose proof (ro8_of_rdn rsegs m 0x169ef8 _ G2 ltac:(lia) ltac:(lia)) as RG2.
  pose proof (ro8_of_rdn rsegs m 0x162a90 _ HGF ltac:(lia) ltac:(lia)) as RG3.
  pose proof (munch_refl [(q - K, q); (P, P + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose_word_ranges.
  zstep.
  carve_frame 64%nat ST.
  do 12 zstep.
  do 3 zstep.
  destruct (stk_split rsegs _ (q - K) (q + -2144) (q + -64) ST ltac:(lia)) as [ST1 ST2]. clear ST.
  replace (q - K)%Z with (q + -2144 - (K - 2144))%Z in ST1 by lia.
  assert (HWx : high_all [(q - K, q); (P, P + 4)]%Z) by (cbn; lia).
  call (tryinit_callZ (K - 2144)).
  1:{ assumption. } 1:{ lia. } 1:{ exact ST1. } 1:{ lia. } 1:{ reflexivity. }
  1:{ lazymatch goal with Hm : munch _ m _ |- _ => exact (ai_byte_munch _ _ _ HWx Hm (aenv_ai _ AE)) end. }
  zstep. lit_branch. zstep. zstep. zstep. zstep.
  if_cases Kc; zify_cond Kc.
  { exfalso. revert Kc. rewrite ?unsigned_lit by lia. lia. }
  do 10 zstep.
  lazymatch goal with Hm : munch _ m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ZP1 : zsh mm P (P + 4)) by (eapply zsh_transport; [exact ZP | exact Hm | apply high_in_app_all, HWx | unfold app; right; lia | lia]);
    destruct (zsh_qwords rsegs mm P 4 ZP1 ltac:(lia) ltac:(lia) ltac:(lia)) as [RW0 RW1];
    replace (P + 4 - 1)%Z with (P + 3)%Z in RW1 by lia;
    change 2147450880%Z with Pm4RegionPoisoned.SB in RW0, RW1
  end.
  zstep. zstep. zstep. zstep. lit_branch.
  do 6 zstep.
  lazymatch goal with Hs : stk _ _ (q + -2144 - (K - 2144))%Z (q + -2144)%Z |- _ =>
    destruct (stk_split rsegs _ _ (q + -2144 - 32) _ Hs ltac:(lia)) as [ST3 ST4]; clear Hs end.
  call frexpl_callq.
  1:{ exact ST4. } 1:{ assumption. } 1:{ exact CE. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact PRE. }
  do 11 zstep.
  lazymatch goal with
  | A : stk _ _ (q + -2144 - (K - 2144))%Z (q + -2144 - 32)%Z, B : stk _ _ (q + -2144 - 32)%Z (q + -2144)%Z, C : stk _ _ (q + -2144)%Z (q + -64)%Z |- _ =>
      pose proof (stk_merge rsegs _ _ _ _ (stk_merge rsegs _ _ _ _ A B ltac:(lia)) C ltac:(lia)) as STm; clear A B C
  end.
  replace (q + -2144 - (K - 2144))%Z with (q - K)%Z in STm by lia.
  release_frame FR STm q.
  finish. all: eassumption.
Qed.
End FX.
