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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_poison BF_allocA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.

Ltac cstep := stepA; try first [if_true | if_false].
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ True => split; [lia| exact I] | |- _ /\ _ => split; [lia| first [exact I| lia]] end | lia ].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.



(* [comment removed for export] *)
Lemma land_m48 : forall k, 0 <= k < 2^48 -> Z.land k 281474976710648 = 8 * (k / 8).
Proof.
  intros k Hk. change 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)).
  rewrite Z.ldiff_land. rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. lia.
Qed.

(* [comment removed for export] *)
Lemma land_round_up : forall x j, 0 <= x -> 1 <= j <= 40 -> x < 2^62 -> Z.land (x + (2^j - 1)) (2^64 - 2^j) = round_up x (2^j).
Proof.
  intros x j Hx Hj Hx2.
  assert (HP : 0 < 2^j <= 2^40) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
  rewrite land_align_down by lia. unfold round_up.
  replace (x + 2^j - 1) with (x + (2^j - 1)) by lia.
  pose proof (Z.div_mod (x + (2^j - 1)) (2^j) ltac:(lia)). lia.
Qed.
Lemma rounded_alt : forall n, 1 <= n -> round_up (n + 0) 8 = rounded n.
Proof.
  intros n Hn. unfold rounded, round_up, kChunkHeader2Size. rewrite Z.add_0_r.
  destruct (Z.le_gt_cases n 8) as [L|G].
  - rewrite Z.max_r by lia. replace ((n + 8 - 1) / 8) with 1; [reflexivity|].
    pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)). lia.
  - rewrite Z.max_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_user_end : forall u n, u = 8 * (u / 8) -> 1 <= n -> 0 <= u -> u + n + 7 < 2^64 ->
  Z.land (u + n + 7) 18446744073709551608 = u + rounded n.
Proof.
  intros u n U8 Hn U0 UB.
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. change (2^3) with 8.
  rewrite <- (rounded_alt n) by lia. unfold round_up.
  pose proof (Z.div_mod (u + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (u + n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (n + 0 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 0 + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ALLOC.
Variable P : acc -> Prop.
Variables (xra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (lo hi n B : Z) (T ab id b1 SB SPAN : Z).
Variables (j0 : bv 8) (j4 : word) (shl shr : list byte).
Definition INST : Z := 0xaaf58.
Definition rz : Z := rz_size n.
Definition ub : Z := ab + rz.                 (* [comment removed for export] *)
Definition cb : Z := ab + rz + -16.           (* [comment removed for export] *)
Definition n8 : Z := n / 8.                   (* [comment removed for export] *)
Definition ALSZ : Z := round_up (needed n) 4096.          (* [comment removed for export] *)
Definition RL : Z := ab + ALSZ - (ub + rounded n).        (* [comment removed for export] *)
#[local] Notation usp := (bv_unsigned sp).

Hypothesis SK : stk bsegs m lo (bv_unsigned sp + -128).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 512.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hn : 1 <= n <= 2^27.
Hypothesis HID : 1 <= id < 2^31.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HDR : rw_cells bsegs m cb [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 j4].
Hypothesis PG : poison_globals m.
Hypothesis HAB : 0x603000 <= ab /\ ab + SPAN <= alloc_ceiling /\ ab mod 8 = 0.
Hypothesis HSPAN : needed n <= SPAN.
Hypothesis APP : ab + SPAN <= 0x7fff7000 \/ kHighMemBeg <= ab.              (* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PBLK : forall a k, ab <= a -> a + Z.of_nat k <= ab + needed n -> P (Z_to_bv 64 a, k).
Hypothesis PBSH : forall a k, kShadowBase + ab / 8 <= a -> a + Z.of_nat k <= kShadowBase + (ab + SPAN) / 8 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition segC5_regs (ms : machine_state) (m' : mem) : Prop :=
  exists (t0' t1' t2' a3' a4' a5' a6' a7' s0' s9' t3' t4' t5' t6' : word),
     (8 <= n /\ ms = MS (mkR (Z_to_bv 64 0x32ec4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n)
                              (Z_to_bv 64 ub) (Z_to_bv 64 (8 * n8)) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                              (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 ub) (Z_to_bv 64 cb) (Z_to_bv 64 (8 * n8)) (Z_to_bv 64 B)
                              (Z_to_bv 64 0) s9' (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                         F (Z_to_bv 64 0x55090) fc None m' (seg_rom bsegs))
  \/ (n < 8 /\ exists (xra' a0' a1' a2' : word),
                 ms = MS (mkR xra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n)
                              a0' a1' a2' a3' a4' a5' a6' a7'
                              (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 ub) (Z_to_bv 64 cb) (Z_to_bv 64 0) (Z_to_bv 64 B)
                              (Z_to_bv 64 0) s9' (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                         F (Z_to_bv 64 0x32ec4) fc None m' (seg_rom bsegs)).

Definition segC5p_post : machine_state -> Prop :=
  fun ms => exists m', segC5_regs ms m'
    /\ munch [(cb + 8, cb + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m' cb [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].


Definition entryC : machine_state :=
  MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n)
           (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 ub) (Z_to_bv 64 cb) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0)
           (Z_to_bv 64 (ub + n)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 0x32db8) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Ltac joinC :=
  do 3 zstepA;                        (* [comment removed for export] *)
  try rewrite (Z.mod_small n 18446744073709551616) by arith; rewrite (land_m48 n) by arith; change (n / 8) with n8;
  zstepA; let K8 := fresh "K8" in if_cases K8; zify_cond K8;
  [ (* [comment removed for export] *)
  | do 3 zstepA; cstep ].
(* [comment removed for export] *)
Ltac regsC_lt := unfold segC5_regs; do 14 eexists; right; split; [arith|]; do 4 eexists; replace (8 * n8) with 0 by arith; reflexivity.
Ltac regsC_ge := unfold segC5_regs; do 14 eexists; left; split; [arith| reflexivity].

Section Prim.
Hypothesis FP : from_primary n = true.
Hypothesis BSH : rw_cells bsegs m (kShadowBase + ab / 8) [C1 (Z_to_bv 8 0xfa)].     (* [comment removed for export] *)

Lemma alloc5_segCp : evtA bsegs P segC5p_post entryC.
Proof.
  unfold entryC. rewrite FP. cbn [Z.b2z].
  pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rz_size_pos n) as RZP. change (rz_size n) with rz in RZP.
  pose proof (needed_range n Hn) as NR. assert (N1 : needed1 n = rounded n + rz) by reflexivity.
  pose proof (rounded_ge n) as (RG1 & RG2 & _).
  assert (N8R : 0 <= n8 /\ 8 * n8 <= n < 8 * n8 + 8) by (unfold n8; clear -Hn; pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia).
  assert (SH8 : (ab + SPAN) / 8 >= ab / 8 + 2)
    by (destruct HAB as (_ & _ & M8); clear -M8 HSPAN NR Hn; pose proof (Z.div_mod ab 8 ltac:(lia)); pose proof (Z.div_mod (ab + SPAN) 8 ltac:(lia));
        pose proof (Z.mod_pos_bound (ab + SPAN) 8 ltac:(lia)); lia).
  assert (A8 : ab = 8 * (ab / 8)) by (destruct HAB as (_ & _ & M8); clear -M8; pose proof (Z.div_mod ab 8 ltac:(lia)); lia).
  pose proof APP as APP'. rewrite kHighMemBeg_val in APP'.
  unfold INST, cb, ub in *. unfold kShadowBase in *.
  pose proof PG as (PG1 & Gx2 & PG3 & Gx4 & Gx5 & Gx6 & Gx7). clear Gx2 Gx4 Gx5 Gx6 Gx7. unfold kShadowBase in PG3.
  assert (MU : munch [(ab + rz + -16 + 8, ab + rz + -16 + 16)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  do 3 zstepA.                        (* [comment removed for export] *)
  rewrite ?Z.lor_0_l. try rewrite (Z.mod_small id 18446744073709551616) by arith. try rewrite (Z.mod_small id 4294967296) by arith.
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  do 3 zstepA.                        (* [comment removed for export] *)
  do 2 zstepA.                        (* [comment removed for export] *)
  try rewrite (Z.mod_small ab 18446744073709551616) by arith. rewrite (Z.shiftr_div_pow2 ab 3) by (clear; lia). change (2 ^ 3) with 8.
  set (sha := 2147450880 + ab / 8) in *.
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  joinC.
  - apply evtA_done. unfold segC5p_post. eexists. split; [regsC_lt|]. repeat match goal with |- _ /\ _ => split end; eassumption.
  - apply evtA_done. unfold segC5p_post. eexists. split; [regsC_ge|]. repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End Prim.

(* [comment removed for export] *)
Section Sec.
Hypothesis FPs : from_primary n = false.
Hypothesis ISB : rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)].                 (* [comment removed for export] *)
Hypothesis IPS : rw_cells bsegs m 0xaaf98 [C8 (Z_to_bv 64 4096)].               (* [comment removed for export] *)
Hypothesis SHDR : rw_cells bsegs m (ab - 4096 + 16) [C8 (Z_to_bv 64 (needed n))].   (* [comment removed for export] *)
Hypothesis SHL : rw_cells bsegs m (kShadowBase + ab / 8) [CB (Z.to_nat (rz / 8)) shl].
Hypothesis SHR : rw_cells bsegs m (kShadowBase + (ub + rounded n) / 8) [CB (Z.to_nat (RL / 8)) shr].
Hypothesis HAB4 : ab mod 4096 = 0.
Hypothesis HSPAN2 : ALSZ <= SPAN.
Hypothesis SBR : 0 <= SB /\ SB + 2^37 <= alloc_ceiling.
Hypothesis DSB : ab + ALSZ <= SB \/ SB + 2^37 <= ab.                    (* [comment removed for export] *)
Hypothesis PSEC : forall a k, ab - 4096 <= a -> a + Z.of_nat k <= ab - 4096 + 32 -> P (Z_to_bv 64 a, k).

Definition WCs : list (Z * Z) :=
  [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (cb + 8, cb + 16);
   (kShadowBase + ab / 8, kShadowBase + ab / 8 + rz / 8);
   (kShadowBase + (ub + rounded n) / 8, kShadowBase + (ub + rounded n) / 8 + RL / 8)].
Definition segC5s_post : machine_state -> Prop :=
  fun ms => exists m', segC5_regs ms m'
    /\ munch WCs m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m' cb [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (kShadowBase + ab / 8) [CB (Z.to_nat (rz / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (rz / 8)))]
    /\ rw_cells bsegs m' (kShadowBase + (ub + rounded n) / 8) [CB (Z.to_nat (RL / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (RL / 8)))]
    /\ poison_globals m'.

(* [comment removed for export] *)
Definition qa : Z := ab / 8.
Definition qr : Z := rz / 8.
Definition qo : Z := rounded n / 8.
Definition qR : Z := RL / 8.
Definition qS : Z := (ab + SPAN) / 8.
Definition shaL : Z := 2147450880 + qa.                  (* [comment removed for export] *)
Definition shaR : Z := 2147450880 + qa + qr + qo.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition NUMS : Prop :=
     (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 512 /\ bv_unsigned sp <= hi /\ hi < 2^47
  /\ (0 <= bv_unsigned sp < 2^64) /\ (1 <= n <= 2^27) /\ (1 <= id < 2^31) /\ (0 <= b1 < 256)
  /\ 0x603000 <= ab /\ ab + SPAN <= alloc_ceiling /\ needed n <= SPAN /\ ALSZ <= SPAN
  /\ (16 <= rz <= 2048) /\ n <= rounded n /\ 8 <= rounded n /\ rounded n <= n + 15
  /\ needed1 n = rounded n + rz /\ needed n = needed1 n + rz /\ needed n <= ALSZ /\ ALSZ < needed n + 4096
  /\ ab = 8 * qa /\ rz = 8 * qr /\ rounded n = 8 * qo /\ RL = 8 * qR /\ RL = ab + ALSZ - (ab + rz + rounded n)
  /\ (0 <= n8 /\ 8 * n8 <= n < 8 * n8 + 8) /\ qa + qr + qo + qR <= qS
  /\ (0 <= SB /\ SB + 2^37 <= alloc_ceiling) /\ ab = 4096 * (ab / 4096)
  /\ 8 * qS <= ab + SPAN /\ (ab + SPAN <= 0x7fff7000 \/ 0x10007fff8000 <= ab).
Lemma nums : NUMS.
Proof.
  pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rz_size_pos n) as RZP. change (rz_size n) with rz in RZP.
  pose proof (rz_size_mod16 n) as RZ16. change (rz_size n) with rz in RZ16.
  pose proof (needed_range n Hn) as NR. assert (N1 : needed1 n = rounded n + rz) by reflexivity.
  assert (NV : needed n = needed1 n + rz) by (unfold needed; rewrite FPs; reflexivity).
  pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  assert (N8R : 0 <= n8 /\ 8 * n8 <= n < 8 * n8 + 8) by (unfold n8; clear -Hn; pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia).
  pose proof (round_up_ge (needed n) 4096 ltac:(lia)) as AL1. pose proof (round_up_lt (needed n) 4096 ltac:(lia)) as AL2.
  pose proof (round_up_mod (needed n) 4096 ltac:(lia)) as AL3. change (round_up (needed n) 4096) with ALSZ in AL1, AL2, AL3.
  assert (A8 : ab = 8 * qa) by (unfold qa; destruct HAB as (_ & _ & M8); clear -M8; pose proof (Z.div_mod ab 8 ltac:(lia)); lia).
  assert (RZ8 : rz = 8 * qr) by (unfold qr; clear -RZ16 RZP; pose proof (Z.div_mod rz 16 ltac:(lia)); pose proof (Z.div_mod rz 8 ltac:(lia)); lia).
  assert (RO8 : rounded n = 8 * qo) by (unfold qo; clear -RG3 RG1; pose proof (Z.div_mod (rounded n) 8 ltac:(lia)); lia).
  assert (RLV : RL = ab + ALSZ - (ab + rz + rounded n)) by reflexivity.
  assert (RL8 : RL = 8 * qR)
    by (unfold qR; rewrite RLV at 2; clear -RLV AL3 AL1 A8 RZ8 RO8 NR Hn; pose proof (Z.div_mod ALSZ 4096 ltac:(lia));
        pose proof (Z.div_mod (ab + ALSZ - (ab + rz + rounded n)) 8 ltac:(lia)); lia).
  assert (SH8 : qa + qr + qo + qR <= qS)
    by (unfold qS; clear -HSPAN2 AL1 NR Hn A8 RZ8 RO8 RL8 RLV; pose proof (Z.div_mod (ab + SPAN) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (ab + SPAN) 8 ltac:(lia)); lia).
  assert (A4K : ab = 4096 * (ab / 4096)) by (clear -HAB4; pose proof (Z.div_mod ab 4096 ltac:(lia)); lia).
  assert (QS8 : 8 * qS <= ab + SPAN) by (unfold qS; clear -HAB HSPAN NR; pose proof (Z.div_mod (ab + SPAN) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (ab + SPAN) 8 ltac:(lia)); lia).
  pose proof APP as APP'. rewrite kHighMemBeg_val in APP'.
  unfold NUMS. repeat match goal with |- _ /\ _ => split end; (first [assumption| lia]).
Qed.
(* [comment removed for export] *)
Ltac open_nums :=
  let NF' := fresh "NF'" in
  pose proof nums as NF; pose proof NF as NF'; unfold NUMS in NF';
  destruct NF' as (CEI & LOC' & LO' & SPH' & HI' & SPR & Hn' & HID' & HB1' & AB0 & ABS & NSP & ALS & RZP & RG1 & RG8 & RG2
                  & N1 & NV & AL1 & AL2 & A8 & RZ8 & RO8 & RL8 & RLV & N8R & SH8 & SBR' & A4K & QS8 & APP').
(* [comment removed for export] *)
Ltac nlia := lazymatch goal with NF : NUMS |- _ => clear -NF; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia end.
Ltac nlia1 K := lazymatch goal with NF : NUMS |- _ => clear -NF K; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia end.
Ltac nlia2 K1 K2 := lazymatch goal with NF : NUMS |- _ => clear -NF K1 K2; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia end.
Tactic Notation "nliaK" ne_hyp_list(l) :=
  lazymatch goal with NF : NUMS |- _ => clear -NF l; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia end.
Ltac kill1 K := exfalso; revert K; nlia.

(* [comment removed for export] *)
Definition storeC_post : machine_state -> Prop :=
  fun ms => exists m0,
    ms = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) (Z_to_bv 64 700248) (Z_to_bv 64 B) (Z_to_bv 64 0)
                 (Z_to_bv 64 (ab + rz + n)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x32de8) fc None m0 (seg_rom bsegs)
    /\ munch [(ab + rz + -16 + 8, ab + rz + -16 + 16)] m m0 /\ wmono bsegs m m0 /\ mem_inv bsegs m0
    /\ rw_cells bsegs m0 (ab + rz + -16) [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Lemma secC_store : evtA bsegs P storeC_post entryC.
Proof.
  unfold entryC. rewrite FPs. cbn [Z.b2z]. open_nums.
  clear ISB IPS SHDR SHL SHR PSEC PSTK PDAT PBSH SK PG APP DSB SBR HAB4 HSPAN2.
  unfold INST, cb, ub in *.
  assert (MU : munch [(ab + rz + -16 + 8, ab + rz + -16 + 16)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  do 3 zstepA.                        (* [comment removed for export] *)
  rewrite ?Z.lor_0_l. try rewrite (Z.mod_small id 18446744073709551616) by nlia. try rewrite (Z.mod_small id 4294967296) by nlia.
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  apply evtA_done. unfold storeC_post. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

(* [comment removed for export] *)
Lemma sec_range_check :
  forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' s3' s4' s5' s7' s8' s9' s10' s11' t0' t1' t2' t3' t4' t5' t6' : word) (m0 : mem),
  mem_inv bsegs m0 -> rw_cells bsegs m0 0xaaf78 [C8 (Z_to_bv 64 SB)] ->
  evtA bsegs P
    (fun ms => exists a1x : word,
       ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n) (Z_to_bv 64 SB) a1x a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 ab) s3' s4' s5' (Z_to_bv 64 INST) s7' s8' s9' s10' s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x32e24) fc None m0 (seg_rom bsegs))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) s3' s4' s5' (Z_to_bv 64 INST) s7' s8' s9' s10' s11' t3' t4' t5' t6')
        F (Z_to_bv 64 0x32de8) fc None m0 (seg_rom bsegs)).
Proof.
  intros until m0. intros MI0 ISB0. pose proof LOC as LOCu. aceil.
  pose proof (needed_range n Hn) as NR. pose proof (round_up_ge (needed n) 4096 ltac:(lia)) as AL1. change (round_up (needed n) 4096) with ALSZ in AL1.
  unfold INST in *.
  zstepA.                             (* [comment removed for export] *)
  zstepA; if_cases K1; zify_cond K1.
  - apply evtA_done. eexists. reflexivity.
  - do 3 (zstepA; litc).              (* [comment removed for export] *)
    try rewrite (Z.mod_small (SB + 137438953472) 18446744073709551616) by arith.
    zstepA; if_cases K2; zify_cond K2; [clear K2| kill K2].   (* [comment removed for export] *)
    apply evtA_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma secC_alsz :
  forall (ra' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m0 : mem),
  mem_inv bsegs m0 -> rw_cells bsegs m0 0xaaf98 [C8 (Z_to_bv 64 4096)] -> rw_cells bsegs m0 (ab - 4096 + 16) [C8 (Z_to_bv 64 (needed n))] ->
  evtA bsegs P
    (fun ms => ms = MS (mkR (Z_to_bv 64 0x32e90) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ALSZ) (Z_to_bv 64 n)
                            (Z_to_bv 64 ab) (Z_to_bv 64 rz) (Z_to_bv 64 250) a3' a4' a5' a6' a7'
                            (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) (Z_to_bv 64 (ab + rz + rounded n))
                            (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (ab + rz + n + 7)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x55090) fc None m0 (seg_rom bsegs))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n) (Z_to_bv 64 SB) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0)
             (Z_to_bv 64 (ab + rz + n)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
        F (Z_to_bv 64 0x32e24) fc None m0 (seg_rom bsegs)).
Proof.
  intros until m0. intros MI0 IPS0 SHDR0. open_nums.
  clear ISB IPS SHDR SHL SHR HDR PSTK PBSH PBLK SK PG MI APP DSB SBR.
  unfold INST in *.
  assert (MU : munch [] m0 m0) by apply munch_refl.
  assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
  zstepA.                             (* [comment removed for export] *)
  (zstepA; litc).                     (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  replace (Z.land 4095 ab) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by nlia; change (2^12) with 4096; clear -HAB4; lia).
  cstep.                              (* [comment removed for export] *)
  (zstepA; litc).                     (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  change 18446744073709547520 with (2^64 - 2^12). change 4095 with (2^12 - 1). rewrite (land_round_up (needed n) 12) by nlia.
  change (2^12) with 4096. change (round_up (needed n) 4096) with ALSZ.
  cstep.                              (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  rewrite (land_user_end (ab + rz) n) by nlia.
  zstepA.                             (* [comment removed for export] *)
  try replace (ab + rz - ab) with rz by (clear; lia).
  zstepA. zstepA.                     (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pz_post (raw s0' s6' s9' : word) (mk : mem) (qA qL : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
    ms' = MS (mkR raw (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
                  s9' (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (ret_pc raw) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (2147450880 + qA, 2147450880 + qA + qL)] mk m' /\ wmono bsegs mk m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m' (2147450880 + qA) [CB (Z.to_nat qL) (repeat (Z_to_bv 8 250) (Z.to_nat qL))]
    /\ poison_globals m'.

Lemma poisonC_call :
  forall (raw s0' s6' s9' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mk : mem) (A L qA qL : Z) (junk : list byte),
  mem_inv bsegs mk -> stk bsegs mk lo (bv_unsigned sp + -128) -> poison_globals mk ->
  A = 8 * qA -> L = 8 * qL -> 0 <= qL -> 0x603000 <= A -> A + L <= alloc_ceiling ->
  (A + L <= 0x7fff7000 \/ (0x10007fff8000 <= A /\ (0x10007fff8000 + 8 <= A \/ 8 <= L))) ->
  qa <= qA -> qA + qL <= qS ->
  rw_cells bsegs mk (2147450880 + qA) [CB (Z.to_nat qL) junk] ->
  evtA bsegs P (pz_post raw s0' s6' s9' mk qA qL)
    (MS (mkR raw (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 250) a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
             s9' (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
        F (Z_to_bv 64 0x55090) fc None mk (seg_rom bsegs)).
Proof.
  intros until junk. intros MIk SKk PGk HA HL HqL A0 AC APL Q1 Q2 SHk. open_nums.
  clear ISB IPS SHDR SHL SHR HDR PBLK PSEC SK PG MI APP DSB SBR.
  pose proof LOC as LOC0.
  remember (Z_to_bv 64 (bv_unsigned sp + -128)) as sp1 eqn:Esp.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -128) by (rewrite Esp; apply unsigned_lit; nlia).
  assert (E1 : kShadowBase + A / 8 = 2147450880 + qA) by (unfold kShadowBase; rewrite HA, Z.mul_comm, Z.div_mul by (clear; lia); reflexivity).
  assert (E2 : L / 8 = qL) by (rewrite HL, Z.mul_comm, Z.div_mul by (clear; lia); reflexivity).
  pose proof PBSH as PBSH'. unfold kShadowBase in PBSH'. change (ab / 8) with qa in PBSH'. change ((ab + SPAN) / 8) with qS in PBSH'.
  eapply evtA_mono.
  { eapply (poison_walk P raw sp1 gp tp t0' t1' t2' s0' (Z_to_bv 64 n) a3' a4' a5' a6' a7'
              (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
              s9' (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6' F fc mk lo A L 250 junk);
    [ rewrite Hsp; exact SKk| exact LOC0| rewrite Hsp; nlia| rewrite Hsp; nlia| exact MIk| exact PGk
    | rewrite HA, Z.mul_comm; apply Z_mod_mult| rewrite HL, Z.mul_comm; apply Z_mod_mult| clear -HL HqL; lia
    | exact A0| exact AC| rewrite kHighMemBeg_val; exact APL| clear; lia
    | left; clear; lia
    | rewrite E1, E2; exact SHk
    | rewrite Hsp; intros; apply PSTK; nlia2 H H0| exact PDAT
    | rewrite E1, E2; intros; apply PBSH'; nliaK H H0 Q1 Q2 ]. }
  cbv beta. intros ms' PO. unfold poison_post in PO. rewrite E1, E2, Hsp in PO. destruct_exs PO.
  destruct PO as (E & MU' & WM' & MI' & SK' & SHZ & PG'). unfold pz_post. subst sp1.
  repeat (lazymatch goal with |- ex _ => eexists end). split; [exact E|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Ltac xport H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W ma mb A cs) in H; [| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; nlia]
    end end.
Ltac xport_stk H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with stk _ _ ?l ?h =>
      apply (stk_transport_disjoint bsegs W ma mb l h) in H; [| exact MU| exact WM| cbn [disjoint_from]; nlia]
    end end.
Ltac xport_pg H MU :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    apply (poison_globals_agree ma mb) in H;
    [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MU; rewrite wa_unsigned by (clear -Ha; lia); cbn [outside]; nliaK Ha]
  end.

Lemma alloc5_segCs : evtA bsegs P segC5s_post entryC.
Proof.
  open_nums.
  pose proof SHL as SHL0. unfold kShadowBase in SHL0. change (ab / 8) with qa in SHL0. change (rz / 8) with qr in SHL0.
  pose proof SHR as SHR0. unfold kShadowBase, ub in SHR0. change (RL / 8) with qR in SHR0.
  replace ((ab + rz + rounded n) / 8) with (qa + qr + qo) in SHR0
    by (replace (ab + rz + rounded n) with ((qa + qr + qo) * 8) by nlia; rewrite Z.div_mul by (clear; lia); reflexivity).
  pose proof SK as SK0. pose proof PG as PG0. pose proof ISB as ISB0. pose proof IPS as IPS0. pose proof SHDR as SHDR0.
  (* [comment removed for export] *)
  eapply evtA_cut; [apply secC_store|]. cbv beta. intros ms' (m0 & -> & MU0 & WM0 & MI0 & HDR0).
  xport ISB0 MU0 WM0. xport IPS0 MU0 WM0. xport SHDR0 MU0 WM0. xport SHL0 MU0 WM0. xport SHR0 MU0 WM0.
  xport_stk SK0 MU0 WM0. xport_pg PG0 MU0.
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply sec_range_check; [exact MI0| exact ISB0]|]. cbv beta. intros ms' (a1x & ->).
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply secC_alsz; [exact MI0| exact IPS0| exact SHDR0]|]. cbv beta. intros ms' ->.
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (poisonC_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 ab rz qa qr shl);
      [exact MI0| exact SK0| exact PG0| exact A8| exact RZ8| nlia| nlia| nlia| clear -NF APP; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia
      | clear; lia| nlia| exact SHL0]. }
  cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU1 & WM1 & MI1 & SK1 & SHL1 & PG1). ret_pc_lit.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m1 end.
  xport HDR0 MU1 WM1. xport SHR0 MU1 WM1.
  (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  replace (ab - (ab + rz + rounded n) + ALSZ) with RL by nlia.
  zstepA. zstepA.                     (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (poisonC_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (ab + rz + rounded n) RL (qa + qr + qo) qR shr);
      [exact MI1| exact SK1| exact PG1| nlia| exact RL8| nlia| nlia| nlia| clear -NF APP; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia
      | nlia| nlia| exact SHR0]. }
  cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU2 & WM2 & MI2 & SK2 & SHR2 & PG2). ret_pc_lit.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m2 end.
  xport HDR0 MU2 WM2. xport SHL1 MU2 WM2.
  (* [comment removed for export] *)
  assert (MU : munch WCs m m2).
  { unfold WCs, cb, ub, kShadowBase.
    eapply munch_trans; [| eapply munch_trans]; [eapply munch_weaken; [| exact MU0] | eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]];
      unfold sub_fp; cbn [outside]; (let xo := fresh "xo" in let Hx := fresh "Hxo" in intros xo Hx; nliaK Hx). }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM1| exact WM2]).
  clear MU0 MU1 MU2 WM0 WM1 WM2 MI0 MI1 SK0 SK1 PG0 PG1.
  joinC.
  - apply evtA_done. unfold segC5s_post. exists m2. split; [regsC_lt|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact SK2|]. split; [exact HDR0|]. split; [exact SHL1|].
    split; [| exact PG2]. unfold ub. replace ((ab + rz + rounded n) / 8) with (qa + qr + qo); [exact SHR2|].
    replace (ab + rz + rounded n) with ((qa + qr + qo) * 8) by nlia; rewrite Z.div_mul by (clear; lia); reflexivity.
  - apply evtA_done. unfold segC5s_post. exists m2. split; [regsC_ge|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact SK2|]. split; [exact HDR0|]. split; [exact SHL1|].
    split; [| exact PG2]. unfold ub. replace ((ab + rz + rounded n) / 8) with (qa + qr + qo); [exact SHR2|].
    replace (ab + rz + rounded n) with ((qa + qr + qo) * 8) by nlia; rewrite Z.div_mul by (clear; lia); reflexivity.
Qed.
End Sec.
End ALLOC.
End RC__1.
