(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths and module names changed; 45 of its 97 lines of code are new or changed and 3487 lines of the source are left out. *)
(* lib/A/Prog/asan_stack_malloc_cF_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane 11:49Z / 11:50Z; writer a Theorem Labs lane): the
   ADDITIVE `_on` form of asan_stack_malloc_cF.v's FOOTPRINT contract, STATEMENT ONLY, plus two bridges.
   asan_stack_malloc_cF.v and asan_stack_malloc_c_on.v stay byte-identical apart from comment text. Twin of image B's
   lib/B/Prog/asan_stack_malloc_cF_on.v (a Theorem Labs lane): the two texts are to stay twins.

   PRE: `shadow_rw m` becomes `shadow_rw_on (asan_stack_malloc_shadow_R FS c) m`, the class-c BLOCK shadow of
   asan_stack_malloc_c_on.v by name (the region, its reads-and-stores derivation and the load-bearing FS + 96 = 0
   premise are documented there). Every other premise, the rng premises included, is asan_stack_malloc_cF.v's text.
   POST: unchanged. asan_stack_malloc_post states no shadow fact (no `shadow_rw m'`), so there is nothing to turn into
   the `forall P, shadow_rw_on P m -> shadow_rw_on P m'` form; the same holds for asan_stack_malloc_contract_on.
   BRIDGES (proved here; they assume nothing):
   - asan_stack_malloc_contract_F_of_F_on: the _F_on form gives the old _F form (shadow_rw gives shadow_rw_on).
   - asan_stack_malloc_contract_on_of_F_on: the _F_on form gives the plain _on form at RNG_all, for c <= 10; every
     rng bound comes from a premise the _on contract already carries, by asan_stack_malloc_1_contract_of_F's script
     (reac_ctrl_parseF.v:98-132) with the class generic.
   No proof of the contract itself is here; the proofs are a Theorem Labs lane's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c ImgBounds
  asan_stack_malloc_c_on asan_stack_malloc_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition asan_stack_malloc_contract_F_on (c : nat) (entry K : Z) : Prop :=
  (c <= 10)%nat ->
  forall (RNG : lib.Lib.ExecF.footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw_on (asan_stack_malloc_shadow_R FS c) m -> mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= c)%nat -> bytes_at rsegs m (CF + 120) (le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs m (fs_hint FS c) (le8 h) ->
  bytes_at rsegs m (fs_flag FS c 0) flags -> Z.of_nat (length flags) = fs_M c ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K -> (forall a, S0 - K <= a < S0 -> app_mem a) ->
  disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)] (S0 - K) K ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (S0 - K) K ->
  rng RNG (bv_unsigned DT + 8) 8 -> rng RNG (bv_unsigned TS + 8 * k) 8 -> rng RNG (bv_unsigned C + 152) 8 ->
  rng RNG (bv_unsigned T + 48) 16 -> rng RNG (bv_unsigned DB + 24) 8 ->
  rng RNG FS (fs_frame FS 0 0 - FS) -> rng RNG (fs_frame FS c 0) (2 ^ 20) ->
  rng RNG (shadow_addr (fs_frame FS c 0)) (fs_shadow_area c) ->
  rng RNG (TP - 88) 8 -> rng RNG (TP - 8) 24 ->
  evtF rsegs RNG (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_malloc_0_contract_F_on : Prop :=
  asan_stack_malloc_contract_F_on 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_1_contract_F_on : Prop :=
  asan_stack_malloc_contract_F_on 1 ASAN_STACK_MALLOC_1 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_2_contract_F_on : Prop :=
  asan_stack_malloc_contract_F_on 2 ASAN_STACK_MALLOC_2 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_6_contract_F_on : Prop :=
  asan_stack_malloc_contract_F_on 6 ASAN_STACK_MALLOC_6 ASAN_STACK_MALLOC_K.

(* The old footprint form from the region form: the old premise `shadow_rw m` gives every region. *)
Lemma asan_stack_malloc_contract_F_of_F_on : forall c entry K,
  asan_stack_malloc_contract_F_on c entry K -> asan_stack_malloc_contract_F c entry K.
Proof.
  unfold asan_stack_malloc_contract_F_on, asan_stack_malloc_contract_F. cbv zeta.
  intros c entry K H Hc RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
    t6 F fc m lo FS h DT TS C T DB k flags HL HL8 HC HSW.
  exact (H Hc RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           lo FS h DT TS C T DB k flags HL HL8 HC (shadow_rw_on_of_shadow_rw _ m HSW)).
Qed.

(* The plain region form from the footprint region form at RNG_all (classes 0..10): asan_stack_malloc_1_contract_of_F's
   script (reac_ctrl_parseF.v:98-132) with the class generic. The class-c frame area ends at or below FS + FS_SIZE
   (36864 + (c + 1) * 2^20 <= 11571200 for c <= 10) and its shadow is 2^20 / 8 = 131072 bytes for every c <= 10. *)
Lemma asan_stack_malloc_contract_on_of_F_on : forall c entry K, (c <= 10)%nat ->
  asan_stack_malloc_contract_F_on c entry K -> asan_stack_malloc_contract_on c entry K.
Proof.
  intros c entry K Hc10.
  unfold asan_stack_malloc_contract_F_on, asan_stack_malloc_contract_on. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS h DT TS C T DB k flags HL HL8 HC HSW MI HT H7 HTP HP H88 H96 HH HFl HFln HFb ST HLK HFS HAPP HDJ.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
  pose proof HT as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
                    & A18 & A19).
  assert (Hcz : 0 <= Z.of_nat c <= 10) by lia.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (Ec : fs_frame FS c 0 = FS + 36864 + Z.of_nat c * 2 ^ 20) by (unfold fs_frame; lia).
  assert (SA : fs_shadow_area c = 131072)
    by (do 11 (destruct c as [|c]; [reflexivity|]); lia).
  (* the side stack lies in application memory (fs_place), so it ends below 2^64 whatever K is *)
  assert (FSB : FS + 11571200 <= 2 ^ 64).
  { pose proof (P4 (FS + 11571199) ltac:(lia)) as Hm. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hm.
    lia. }
  apply (evtF_evt rsegs RNG_all).
  apply (HF Hc10 RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags); try assumption.
  - (* image *) apply rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* stack window *) apply rng_all; lia.
  - (* DT + 8 *) destruct A4 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* TS + 8 k *) destruct A9 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* C + 152 *) destruct A10 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* T + 48 *) destruct A11 as (tb & te & (Ha & Hb & _)).
    rewrite length_app, !length_le8 in Hb. apply rng_all; lia.
  - (* DB + 24 *) destruct A19 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* side-stack header *) apply rng_all; rewrite ?E0; lia.
  - (* class-c frame area *) apply rng_all; rewrite ?Ec; lia.
  - (* shadow of the class-c frame area *)
    rewrite SA, Ec. unfold shadow_addr, ASAN_K.
    pose proof (Z.div_mod (FS + 36864 + Z.of_nat c * 2 ^ 20) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (FS + 36864 + Z.of_nat c * 2 ^ 20) 8 ltac:(lia)) as M.
    apply rng_all; lia.
  - (* TS cell at TP - 88 *) destruct A8 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* DT, side-stack and DB cells at TP - 8 .. TP + 16 *)
    destruct A3 as (Ha & _). destruct A17 as (_ & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
Qed.

Print Assumptions asan_stack_malloc_contract_F_of_F_on.
Print Assumptions asan_stack_malloc_contract_on_of_F_on.
