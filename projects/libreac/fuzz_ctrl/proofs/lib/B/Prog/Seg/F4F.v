(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F4.v seg_F4 (the two inline c_run_lib runs of the segment proof, F4.v lines
     333-370 and 376-396; c_run_lib is lib/B/Prog/Seg/F5.v:891) at a working branch 3803efccea0
     (blob 44f46f16817accf46824082fab41755a1ffa35b6);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: seg_F4_eq88_run / seg_F4_ne88_run (evtF_evt + rng_all) re-derive the source statements; the stretch
     0x81fbc -> 0x82098 has no call, so there is no _pre_F / _post_F split. *)

(* The footprint twins of segment F4 (S_F4), 0x81fbc (the return point of the first reac_ctrl_parse call) to
   0x82098 (the head of the 32-byte block-sum loop). Two runs, one per arm of `bne a0,a1` at 0x81fe8:
     seg_F4_eq88_F  record byte 12 = 0x88: reads the shadow bytes of Phi+12 and Phi+13 and the record bytes
                    Phi+12 and Phi+13, writes the spill word [A+272, A+280);
     seg_F4_ne88_F  record byte 12 <> 0x88: reads the shadow byte of Phi+12 and the record byte Phi+12, writes
                    the spill word [A+272, A+280).
   The source proof's own premises are kept (the cut's register values as `rg` facts, the shadow bytes 0, the
   record bytes, the Phi bound, the store_ok of the spill word); `rng` premises are added one per access. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F5 F4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE4 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The loop set-up 0x8206c-0x82094 and the landing at 0x82098, both arms (F4.v's Local Ltac f4_tail, replayed
   with StepF's step; it touches no memory, so every access side goal is `Forall _ nil`). *)
Local Ltac f4F_tail p Hphib :=
  step; step; step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  step; step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  step;
  rewrite f4_sltiu17; [ | reflexivity | clear - Hphib; f4_mlia ];
  step; step; rewrite ?f4_land_ones_w;
  step; step;
  finish.

Section F4F.

Variables (Fr : bvmap 5 word) (fc : bv 32).

(* ---- arm 1: record byte 12 = 0x88 (F4.v:333-370) ---- *)
Lemma seg_F4_eq88_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (A p k8 : Z) (b12 b13 : byte),
    rg regs 10 k8 -> rg regs 18 p -> rg regs 9 A -> rg regs 26 ASAN_K ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    bytes_at rsegs mem (Z.shiftr (p + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 12) [b12] -> bv_unsigned b12 = 136 ->
    bytes_at rsegs mem (Z.shiftr (p + 13) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 13) [b13] -> 0 <= bv_unsigned b13 < 256 ->
    store_ok rsegs mem (wa (A + 272)) 8 = true ->
    rng RNG (Z.shiftr (p + 12) 3 + ASAN_K) 1 -> rng RNG (p + 12) 1 ->
    rng RNG (Z.shiftr (p + 13) 3 + ASAN_K) 1 -> rng RNG (p + 13) 1 ->
    rng RNG (A + 272) 8 ->
    evtF rsegs RNG
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82098 /\
          mem' = write_to_mem mem (wa (A + 272))
                   (le8 (Z_to_bv 64 (if bv_unsigned b13 =? 25 then 1 else 0))) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 24 = Z_to_bv 64 k8 /\ getr R 10 = Z_to_bv 64 (p + 18) /\
          getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 (p + 18) /\
          getr R 13 = Z_to_bv 64 (- (p + 18)) /\ getr R 14 = Z_to_bv 64 32 /\
          getr R 17 = Z_to_bv 64 32 /\ getr R 5 = Z_to_bv 64 (p + 18)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81fbc) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem A p k8 b12 b13 Ha0 Hs2 Hr9 Hr26 Hphib Hsh12 Hb12 H12eq Hsh13 Hb13 Hv13 HS272
    Rs12 R12 Rs13 R13 R272.
  pose proof (f4_rd1 mem _ _ Hsh12) as RDs12.
  pose proof (f4_rd1 mem _ _ Hsh13) as RDs13.
  pose proof (f4_rd1 mem _ _ Hb12) as RD12.
  pose proof (f4_rd1 mem _ _ Hb13) as RD13.
  rewrite c_mkR_expand. c_slot Ha0. c_slot Hs2. c_slot Hr9. c_slot Hr26.
  (* 0x81fbc mv s8,a0 ; 0x81fc0 li a0,-13 ; 0x81fc4 bgeu a0,s2 : taken *)
  step. step. step.
  rewrite (f4_ltu_false _ p) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
  (* 0x81fcc addi a0,s2,12 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a1 : shadow 0 ; bnez a1 : not taken *)
  step. rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia).
  step. step. rewrite ?(MState.unsigned_lit (p + 12)) by (clear - Hphib; lia).
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x81fe0 lbu a0,0(a0) ; li a1,136 ; bne a0,a1 : not taken *)
  step. step. step.
  rewrite (f4_zxb_eq b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
  cbn [negb]. cbv iota.
  (* 0x81fec li a0,-14 ; bgeu a0,s2 : taken *)
  step. step.
  rewrite (f4_ltu_false _ p) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
  (* 0x81ff8 addi a0,s2,13 ; srli ; add ; lb : shadow 0 ; bnez : not taken *)
  step. rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia).
  step. step. rewrite ?(MState.unsigned_lit (p + 13)) by (clear - Hphib; lia).
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x8200c lbu a0,0(a0) ; addi a0,a0,-25 ; seqz a0,a0 *)
  step.
  rewrite (f4_zxb_eq b13 (bv_unsigned b13)) by reflexivity.
  step. rewrite ?(MState.unsigned_lit (bv_unsigned b13)) by lia.
  step. rewrite f4_seqz.
  (* 0x82018 sd a0,272(s1) ; 0x8201c j 8206c *)
  step. step.
  f4F_tail p Hphib.
  all: try (rewrite (f4_sub25b (bv_unsigned b13)) by lia; reflexivity).
  all: try (symmetry; first [exact Hs2 | exact Hr9 | exact Hr26]).
  all: try (apply f4_word_eq; clear - Hphib; f4_mlia).
  all: try reflexivity.
Qed.

(* ---- arm 2: record byte 12 <> 0x88 (F4.v:376-396) ---- *)
Lemma seg_F4_ne88_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (A p k8 : Z) (b12 : byte),
    rg regs 10 k8 -> rg regs 18 p -> rg regs 9 A -> rg regs 26 ASAN_K ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    bytes_at rsegs mem (Z.shiftr (p + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 12) [b12] -> bv_unsigned b12 <> 136 -> 0 <= bv_unsigned b12 < 256 ->
    store_ok rsegs mem (wa (A + 272)) 8 = true ->
    rng RNG (Z.shiftr (p + 12) 3 + ASAN_K) 1 -> rng RNG (p + 12) 1 ->
    rng RNG (A + 272) 8 ->
    evtF rsegs RNG
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82098 /\
          mem' = write_to_mem mem (wa (A + 272)) (le8 (Z_to_bv 64 0)) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 24 = Z_to_bv 64 k8 /\ getr R 10 = Z_to_bv 64 (p + 18) /\
          getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 (p + 18) /\
          getr R 13 = Z_to_bv 64 (- (p + 18)) /\ getr R 14 = Z_to_bv 64 32 /\
          getr R 17 = Z_to_bv 64 32 /\ getr R 5 = Z_to_bv 64 (p + 18)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81fbc) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem A p k8 b12 Ha0 Hs2 Hr9 Hr26 Hphib Hsh12 Hb12 H12ne Hv12 HS272 Rs12 R12 R272.
  pose proof (f4_rd1 mem _ _ Hsh12) as RDs12.
  pose proof (f4_rd1 mem _ _ Hb12) as RD12.
  rewrite c_mkR_expand. c_slot Ha0. c_slot Hs2. c_slot Hr9. c_slot Hr26.
  step. step. step.
  rewrite (f4_ltu_false _ p) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
  step. rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia).
  step. step. rewrite ?(MState.unsigned_lit (p + 12)) by (clear - Hphib; lia).
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  step. step. step.
  rewrite (f4_zxb_eq b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
  cbn [negb]. cbv iota.
  (* 0x82068 sd zero,272(s1) *)
  step.
  f4F_tail p Hphib.
  all: try (symmetry; first [exact Hs2 | exact Hr9 | exact Hr26]).
  all: try (apply f4_word_eq; clear - Hphib; f4_mlia).
  all: try reflexivity.
Qed.

(* ---- the source runs (lib.Lib Exec.evt, the form c_run_lib consumes): the `_of_F` compares ---- *)
Lemma seg_F4_eq88_run :
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A p k8 : Z) (b12 b13 : byte),
    rg regs 10 k8 -> rg regs 18 p -> rg regs 9 A -> rg regs 26 ASAN_K ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    0 <= A /\ A + 280 <= 2 ^ 64 ->
    bytes_at rsegs mem (Z.shiftr (p + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 12) [b12] -> bv_unsigned b12 = 136 ->
    bytes_at rsegs mem (Z.shiftr (p + 13) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 13) [b13] -> 0 <= bv_unsigned b13 < 256 ->
    store_ok rsegs mem (wa (A + 272)) 8 = true ->
    LE4.evt rsegs
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82098 /\
          mem' = write_to_mem mem (wa (A + 272))
                   (le8 (Z_to_bv 64 (if bv_unsigned b13 =? 25 then 1 else 0))) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 24 = Z_to_bv 64 k8 /\ getr R 10 = Z_to_bv 64 (p + 18) /\
          getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 (p + 18) /\
          getr R 13 = Z_to_bv 64 (- (p + 18)) /\ getr R 14 = Z_to_bv 64 32 /\
          getr R 17 = Z_to_bv 64 32 /\ getr R 5 = Z_to_bv 64 (p + 18)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81fbc) fc None mem (seg_rom rsegs)).
Proof.
  intros regs mem A p k8 b12 b13 Ha0 Hs2 Hr9 Hr26 Hphib HA Hsh12 Hb12 H12eq Hsh13 Hb13 Hv13 HS272.
  assert (Hs12 : 0 <= Z.shiftr (p + 12) 3 <= 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  assert (Hs13 : 0 <= Z.shiftr (p + 13) 3 <= 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  apply (evtF_evt rsegs RNG_all). eapply seg_F4_eq88_F; try eassumption;
    apply rng_all; unfold ASAN_K in *; lia.
Qed.

Lemma seg_F4_ne88_run :
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A p k8 : Z) (b12 : byte),
    rg regs 10 k8 -> rg regs 18 p -> rg regs 9 A -> rg regs 26 ASAN_K ->
    0 < p /\ p + 64 <= 2 ^ 64 ->
    0 <= A /\ A + 280 <= 2 ^ 64 ->
    bytes_at rsegs mem (Z.shiftr (p + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs mem (p + 12) [b12] -> bv_unsigned b12 <> 136 -> 0 <= bv_unsigned b12 < 256 ->
    store_ok rsegs mem (wa (A + 272)) 8 = true ->
    LE4.evt rsegs
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         (pc' = Z_to_bv 64 0x82098 /\
          mem' = write_to_mem mem (wa (A + 272)) (le8 (Z_to_bv 64 0)) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 24 = Z_to_bv 64 k8 /\ getr R 10 = Z_to_bv 64 (p + 18) /\
          getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 (p + 18) /\
          getr R 13 = Z_to_bv 64 (- (p + 18)) /\ getr R 14 = Z_to_bv 64 32 /\
          getr R 17 = Z_to_bv 64 32 /\ getr R 5 = Z_to_bv 64 (p + 18)))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81fbc) fc None mem (seg_rom rsegs)).
Proof.
  intros regs mem A p k8 b12 Ha0 Hs2 Hr9 Hr26 Hphib HA Hsh12 Hb12 H12ne Hv12 HS272.
  assert (Hs12 : 0 <= Z.shiftr (p + 12) 3 <= 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  apply (evtF_evt rsegs RNG_all). eapply seg_F4_ne88_F; try eassumption;
    apply rng_all; unfold ASAN_K in *; lia.
Qed.

End F4F.
