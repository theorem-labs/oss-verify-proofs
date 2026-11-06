(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.

Module AIcpjcb.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcpm9j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)

Definition mem_is_zero_entry := 0x6a7c0%Z.
(* [comment removed for export] *)
Definition mem_is_zero_stack := 16%Z.

Definition mem_is_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (k : nat) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (zeros k).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (k : nat) (lo : Z) (junk : list byte).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m0.
  Hypothesis ZS : bytes_at rsegs m0 (bv_unsigned a0) (zeros k).
  Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m0.
  Hypothesis WM : wmono rsegs m m0.
  Hypothesis ST : stk rsegs m0 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells rsegs m0 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis LO : (0 <= lo)%Z.
  Hypothesis LOLE : (lo <= bv_unsigned sp - 16)%Z.
  Hypothesis NW : (bv_unsigned a0 + Z.of_nat k + 8 <= 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (Z.of_nat k).
  Notation POST := (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k lo m).
  (* [comment removed for export] *)
  Notation AT pc x10 x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m0 (seg_rom rsegs)).

  #[using="NW ZS m0"] Lemma A_bound : (0 <= A /\ A + n <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ ZS) as B. rewrite zeros_length in B. lia. Qed.

  (* [comment removed for export] *)
  #[using="LOLE FR ST WM MU ZS MI junk"] Lemma miz_exit : forall x10 x12 x13 x14 x15 x16,
    evt rsegs POST (AT 0x6a84c x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16).
  Proof.
    intros. do 4 zstep. change (Z.b2z (0 <? 1)) with 1%Z.
    pose proof FR as FRl; pose proof ST as STl.
    release_frame FRl STl (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="NW LOLE FR ST WM MU ZS MI junk"] Lemma miz_loop3 : forall (c : nat) (j : Z) x10 x13 x15 x16,
    (1 <= Z.of_nat c)%Z -> (0 <= j)%Z -> (j + Z.of_nat c <= n)%Z ->
    evt rsegs POST (AT 0x6a838 x10 (Z_to_bv 64 0) (Z_to_bv 64 (A + j)) x13 (Z_to_bv 64 (Z.of_nat c)) x15 x16).
  Proof.
    induction c as [|c IH]; intros j x10 x13 x15 x16 Hc Hj Hjc; [lia|].
    pose proof A_bound as AB.
    pose proof (u8ro_read rsegs m0 A (zeros k) j (Z_to_bv 8 0) _ ZS (zeros_nth k (Z.to_nat j) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    do 4 zstep.
    zstep. if_cases K; zify_cond K.
    - replace (A + j + 1)%Z with (A + (j + 1))%Z by lia.
      replace (Z.of_nat (S c) + -1)%Z with (Z.of_nat c) by lia.
      apply IH; lia.
    - apply miz_exit.
  Qed.

  Notation E := (A + n)%Z.
  Notation AB := (Z.land (A + 7) 18446744073709551608).
  Notation AE := (Z.land (A + n) 18446744073709551608).

  #[using="NW ZS k m0"] Lemma HAB : (AB = A + 7 - (A + 7) mod 8)%Z.
  Proof. pose proof A_bound. apply land_m8. lia. Qed.
  #[using="NW ZS m0"] Lemma HAE : (AE = A + n - (A + n) mod 8)%Z.
  Proof. pose proof A_bound. apply land_m8. lia. Qed.

  (* [comment removed for export] *)
  #[using="NW LOLE FR ST WM MU ZS MI junk"] Lemma miz_after : forall x13 x15 x16,
    evt rsegs POST (AT 0x6a82c a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 E) x15 x16).
  Proof.
    intros. pose proof A_bound as AB0. pose proof HAE as HAE'.
    zstep. if_cases K1; zify_cond K1. { apply miz_exit. }
    zstep. if_cases K2; zify_cond K2. { apply miz_exit. }
    zstep.
    replace (Z_to_bv 64 AE) with (Z_to_bv 64 (A + (AE - A))) by (f_equal; lia).
    replace (A + n - AE)%Z with (Z.of_nat (Z.to_nat (A + n - AE))) by mlia.
    apply miz_loop3; mlia.
  Qed.

  (* [comment removed for export] *)
  #[using="NW LOLE FR ST WM MU ZS MI junk"] Lemma miz_loop2 : forall (w : nat) (p : Z) x13 x16,
    (0 <= p)%Z -> (A + p + 8 * (Z.of_nat w + 1) = AE)%Z ->
    evt rsegs POST (AT 0x6a81c a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 E) (Z_to_bv 64 (A + p)) x16).
  Proof.
    induction w as [|w IH]; intros p x13 x16 Hp Hw; pose proof A_bound as AB0; pose proof HAE as HAE'.
    - pose proof (bytes_at_read rsegs m0 A (zeros k) p 8 ZS ltac:(lia) ltac:(rewrite zeros_length; mlia)) as RD.
      rewrite zeros_window in RD by mlia.
      do 4 zstep. rewrite load8_zeros. zsimp.
      if_cases K; zify_cond K. { exfalso. lia. }
      replace (Z_to_bv 64 (A + p + 8)) with (Z_to_bv 64 AE) by (f_equal; lia).
      apply miz_after.
    - pose proof (bytes_at_read rsegs m0 A (zeros k) p 8 ZS ltac:(lia) ltac:(rewrite zeros_length; mlia)) as RD.
      rewrite zeros_window in RD by mlia.
      do 4 zstep. rewrite load8_zeros. zsimp.
      if_cases K; zify_cond K. 2:{ exfalso. lia. }
      replace (A + p + 8)%Z with (A + (p + 8))%Z by lia.
      apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NW LOLE FR ST WM MU ZS MI junk"] Lemma miz_mid : forall x13 x16,
    evt rsegs POST (AT 0x6a818 a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 E) (Z_to_bv 64 AB) x16).
  Proof.
    intros. pose proof A_bound as AB0. pose proof HAE as HAE'. pose proof HAB as HAB'.
    zstep. if_cases K; zify_cond K. { apply miz_after. }
    replace (Z_to_bv 64 AB) with (Z_to_bv 64 (A + (AB - A))) by (f_equal; lia).
    apply (miz_loop2 (Z.to_nat ((AE - AB) / 8 - 1)) (AB - A)); mlia.
  Qed.

  (* [comment removed for export] *)
  #[using="NW LOLE FR ST WM MU ZS MI junk"] Lemma miz_loop1 : forall (c : nat) (i : Z) x16,
    (Z.to_nat (AB - A - i) = c) -> (0 <= i)%Z -> (A + i < AB)%Z -> (i < n)%Z ->
    evt rsegs POST (AT 0x6a800 a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 E) (Z_to_bv 64 AB) x16).
  Proof.
    induction c as [|c IH]; intros i x16 Hc Hi Hlt Hin; pose proof A_bound as AB0; pose proof HAE as HAE'; pose proof HAB as HAB'; [mlia|].
    pose proof (u8ro_read rsegs m0 A (zeros k) i (Z_to_bv 8 0) _ ZS (zeros_nth k (Z.to_nat i) ltac:(lia)) ltac:(lia)
                  ltac:(f_equal; lia)) as RD.
    do 3 zstep.
    zstep. if_cases K1; zify_cond K1. { apply miz_mid. }
    zstep. zstep. if_cases K2; zify_cond K2.
    - replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
      apply (IH (i + 1)%Z); mlia.
    - apply miz_mid.
  Qed.
End Proofs.

Lemma mem_is_zero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (k : nat) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (zeros k) ->
  bv_unsigned a1 = Z.of_nat k ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length (zeros k)) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat k + 8 <= 2^64)%Z ->
  (Z.of_nat k <= 2^40)%Z ->
  evt rsegs (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 k lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a7c0) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ZS A1 MI LOLE SEP NW KMAX.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ ZS) as AB0. rewrite zeros_length in AB0.
  assert (LO : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST.
  do 7 zstep.
  if_cases K; zify_cond K. { exfalso. rewrite A1 in K. lia. }
  do 6 zstep.
  rewrite A1. try rewrite !(Z.mod_small (bv_unsigned a0 + 7) 18446744073709551616) by lia.
  try rewrite !(Z.mod_small (bv_unsigned a0 + Z.of_nat k) 18446744073709551616) by lia.
  pose proof (land_m8 (bv_unsigned a0 + 7) ltac:(lia)) as HAB'.
  if_cases K2; zify_cond K2.
  - eapply miz_mid; try eassumption; rewrite ?zeros_length in SEP; lia.
  - zstep. if_cases K3; zify_cond K3.
    + replace a1 with (Z_to_bv 64 0) by (symmetry; apply bv_eq; rewrite unsigned_lit by lia; lia).
      eapply miz_mid; try eassumption; rewrite ?zeros_length in SEP; lia.
    + zstep. zstep.
      replace (bv_unsigned a0 + 1)%Z with (bv_unsigned a0 + 0 + 1)%Z by lia.
      eapply (miz_loop1 _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z); try eassumption; try reflexivity; rewrite ?zeros_length in SEP; rewrite ?A1 in *; mlia.
Qed.
End AIcpjcb.

Module AIcpxbj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition map_cells (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa9190 [C8 (Z_to_bv 64 0xb53b8)]
  /\ ro_cells rsegs m 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells rsegs m 0xa9198 [C8 (Z_to_bv 64 0xb60a8)]
  /\ ro_cells rsegs m 0xb60a8 [C8 (Z_to_bv 64 0)]
  /\ ro_cells rsegs m 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)]
  /\ ro_cells rsegs m 0xb60b0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells rsegs m 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)]
  /\ ro_cells rsegs m 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].

Ltac open_map_cells H :=
  let G1 := fresh "Gsh" in let C1 := fresh "Csh" in let G2 := fresh "Gmb" in let C2 := fresh "Cmb" in
  let G3 := fresh "Gme" in let C3 := fresh "Cme" in let G4 := fresh "Ghe" in let C4 := fresh "Che" in
  destruct H as (G1 & C1 & G2 & C2 & G3 & C3 & G4 & C4).

(* [comment removed for export] *)
Definition inmem (x : Z) : Prop := (0 <= x <= 0x7fff7fff)%Z \/ (0x10007fff8000 <= x <= 0x7fffffffffff)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memtoshadow_entry := 0x5a290%Z.

Definition memtoshadow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (2147450880 + Z.shiftr (bv_unsigned a0) 3)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Lemma memtoshadow_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  map_cells m ->
  inmem (bv_unsigned a0) ->
  mem_inv rsegs m ->
  evt rsegs (memtoshadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a290) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MC IM MI. open_map_cells MC.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R0.
  do 7 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879%Z
    by (vm_compute; reflexivity).
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *) do 3 zstep. finish.
  - do 7 zstep.
    replace ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z by (vm_compute; reflexivity).
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
    do 6 zstep. if_cases K3; zify_cond K3. { exfalso. unfold inmem in IM. lia. }
    zstep. if_cases K4; zify_cond K4.
    { exfalso. unfold inmem in IM. rewrite ?Z.shiftr_div_pow2 in K4 by lia. change (2^3)%Z with 8%Z in K4. lia. }
    do 3 zstep. finish.
Qed.
End AIcpxbj.


Module AIcp6d9.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Definition region_is_poisoned_entry := 0x5a71c%Z.
Definition region_is_poisoned_stack := 80%Z.

(* [comment removed for export] *)
Definition inmem_range (beg size : Z) : Prop :=
  (0 <= beg /\ beg + size + 8 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= beg /\ beg + size + 8 <= 0x800000000000)%Z.

Definition region_is_poisoned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Section Proofs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo : Z) (ng : nat) (lastb : Z) (junk : list byte).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m0.
  Hypothesis Gsh : ro_cells rsegs m0 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
  Hypothesis Csh : ro_cells rsegs m0 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
  Hypothesis Gmb : ro_cells rsegs m0 0xa9198 [C8 (Z_to_bv 64 0xb60a8)].
  Hypothesis Cmb : ro_cells rsegs m0 0xb60a8 [C8 (Z_to_bv 64 0)].
  Hypothesis Gme : ro_cells rsegs m0 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)].
  Hypothesis Cme : ro_cells rsegs m0 0xb60b0 [C8 (Z_to_bv 64 0)].
  Hypothesis Ghe : ro_cells rsegs m0 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)].
  Hypothesis Che : ro_cells rsegs m0 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
  Let MC : map_cells m0 := conj Gsh (conj Csh (conj Gmb (conj Cmb (conj Gme (conj Cme (conj Ghe Che)))))).
  Hypothesis MU : munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m0.
  Hypothesis WM : wmono rsegs m m0.
  Hypothesis ST : stk rsegs m0 lo (bv_unsigned sp + -64).
  Hypothesis FR : rw_cells rsegs m0 (bv_unsigned sp + -64)
                    [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis LOLE : (lo <= bv_unsigned sp - 80)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Hypothesis N1 : (1 <= n <= 2^32)%Z.
  Hypothesis IR : inmem_range A n.
  Hypothesis NG : ((A + n - 1) / 8 - A / 8 = Z.of_nat ng)%Z.
  Hypothesis SH : bytes_at rsegs m0 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
  Hypothesis LB : (lastb = 0 \/ ((A + n - 1) mod 8 < lastb <= 7))%Z.

  Notation POST := (region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation AT pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 a0 a1 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 0xb53b8) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m0 (seg_rom rsegs)).

  #[using="IR ng"] Lemma A_facts : (0 <= A /\ A + n + 8 <= 0x800000000000)%Z.
  Proof. unfold inmem_range in IR. pose proof (bv_unsigned_in_range 64 a0). lia. Qed.

  (* [comment removed for export] *)
  #[using="LOLE ng"] Lemma rip_exit : forall m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    mem_inv rsegs m1 -> munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells rsegs m1 (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 a0 a1 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 0xb53b8) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x5a894) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros MI1 MU1 WM1 ST1 FR1. do 11 zstep.
    release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Notation SB := (2147450880 + Z.shiftr (Z.land (A + 7) 18446744073709551608) 3)%Z.
  Notation SE := (2147450880 + Z.shiftr (Z.land (A + n) 18446744073709551608) 3)%Z.

  #[using="IR N1 ng a1"] Lemma HAB : (Z.land (A + 7) 18446744073709551608 = A + 7 - (A + 7) mod 8)%Z.
  Proof. pose proof A_facts. apply land_m8. lia. Qed.
  #[using="IR N1 ng"] Lemma HAE : (Z.land (A + n) 18446744073709551608 = A + n - (A + n) mod 8)%Z.
  Proof. pose proof A_facts. apply land_m8. lia. Qed.

  (* [comment removed for export] *)
  #[using="LB SH NG IR N1 CEIL LOLE FR ST WM MU MI junk lastb ng Clg"] Lemma rip_interior : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
    evt rsegs POST (AT 0x5a880 x1 x5 x6 x7 (Z_to_bv 64 SE) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 SB)
                       (Z_to_bv 64 (Z.land (A + n) 18446744073709551608)) x28 x29 x30 x31).
  Proof.
    intros. pose proof A_facts as AF. pose proof HAB as HAB'. pose proof HAE as HAE'.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    zstep. if_cases K1; zify_cond K1.
    { apply rip_exit; assumption. }
    rewrite !Z.shiftr_div_pow2 in K1 by lia. change (2^3)%Z with 8%Z in K1.
    zstep. zstep. zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    (* [comment removed for export] *)
    assert (ZW : bytes_at rsegs m0 (2147450880 + (A + 7 - (A + 7) mod 8) / 8)
                   (zeros (Z.to_nat ((A + n - (A + n) mod 8) / 8 - (A + 7 - (A + 7) mod 8) / 8)))).
    { replace (2147450880 + (A + 7 - (A + 7) mod 8) / 8)%Z
        with (A / 8 + shadow_off + Z.of_nat (Z.to_nat ((A + 7 - (A + 7) mod 8) / 8 - A / 8)))%Z by (unfold shadow_off; mlia).
      apply (shadow_zero_window m0 _ ng lastb). { exact SH. }
      destruct (Z.eq_dec ((A + n) mod 8) 0) as [E0|E0].
      - right. split; [mlia|]. destruct LB as [LB0|LB1]; [exact LB0|]. exfalso. mlia.
      - left. mlia. }
    rewrite HAB', HAE'.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Che); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Cmb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Cme); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Csh); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Ghe); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Gmb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Gme); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Gsh); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ZW); call_lit mem_is_zero_spec by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by mlia; exact ZW
      | |- mem_inv _ _ => exact MI
      | |- _ => rewrite ?unsigned_lit by mlia; rewrite ?zeros_length; mlia
      end).
    zstep. if_cases K2; zify_cond K2. { exfalso. try (generalize alloc_ceiling_val); clear -K2; try pose proof alloc_ceiling_val. cbv in K2. lia. }
    apply rip_exit; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="LB SH NG IR N1 CEIL LOLE FR ST WM MU MI junk lastb ng Clg"] Lemma rip_last : forall x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt rsegs POST (AT 0x5a82c x1 x5 x6 x7 (Z_to_bv 64 SE) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (A + n)) (Z_to_bv 64 SB) (Z_to_bv 64 (Z.land (A + n) 18446744073709551608)) x28 x29 x30 x31).
  Proof.
    intros. pose proof A_facts as AF.
    assert (LBR : (0 <= lastb < 128)%Z) by lia.
    pose proof (u8ro_read rsegs m0 (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                  (Z_to_bv 64 (2147450880 + Z.shiftr (A + n + -1) 3)) SH) as RD.
    specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                   ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
    do 4 zstep. rewrite sxb_small by lia.
    zstep. if_cases K1; zify_cond K1.
    { apply rip_interior. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { apply rip_interior. }
    exfalso. revert K2. zb_masks. intros K2. rewrite !signed_small in K2 by mlia. destruct LB as [LB0|LB1]; [lia|]. mlia.
  Qed.

  (* [comment removed for export] *)
  #[using="LB SH NG IR N1 CEIL LOLE FR ST WM MU MC Che Ghe Cme Gme Cmb Gmb Csh Gsh MI junk lastb ng Clg"] Lemma rip_core : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
    evt rsegs POST (AT 0x5a7f0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (A + n)) x19 x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof A_facts as AF.
    pose proof HAB as HAB'. pose proof HAE as HAE'.
    assert (LBR : (0 <= lastb < 128)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    do 3 zstep.
    zstep. call memtoshadow_spec.
    1:{ exact MC. }
    1:{ unfold inmem. unfold inmem_range in IR. rewrite unsigned_lit by (split; [apply Z.land_nonneg; lia| rewrite HAB'; mlia]). rewrite HAB'. mlia. }
    1:{ exact MI. }
    do 3 zstep. call memtoshadow_spec.
    1:{ exact MC. }
    1:{ unfold inmem. unfold inmem_range in IR. rewrite unsigned_lit by (split; [apply Z.land_nonneg; lia| rewrite HAE'; mlia]). rewrite HAE'. mlia. }
    1:{ exact MI. }
    (* [comment removed for export] *)
    assert (B0 : exists b0, nth_error (zeros ng ++ [Z_to_bv 8 lastb]) 0 = Some (Z_to_bv 8 b0)
                            /\ (0 <= b0 < 128)%Z /\ (b0 = 0 \/ (ng = 0%nat /\ b0 = lastb))%Z).
    { rewrite (shadow_nth ng lastb 0) by lia. destruct ng as [|ng'].
      - exists lastb. cbn. split; [reflexivity|]. split; [lia|]. right; split; [reflexivity|lia].
      - exists 0%Z. cbn. split; [reflexivity|]. split; [lia|]. left; reflexivity. }
    destruct B0 as (b0 & Hn0 & Hb0 & Hb0').
    pose proof (u8ro_read rsegs m0 (A / 8 + shadow_off) _ 0 _
                  (Z_to_bv 64 (2147450880 + Z.shiftr A 3)) SH Hn0 ltac:(lia)
                  ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)) as RD.
    do 4 zstep. rewrite sxb_small by lia.
    zstep. if_cases K1; zify_cond K1. { apply rip_last. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. destruct Hb0' as [Hz | [Hng Hl]]; [lia|]. subst b0.
      revert K2. zb_masks. intros K2. rewrite !signed_small in K2 by mlia.
      destruct LB as [LB0|LB1]; [lia|]. rewrite Hng in NG. cbn [Z.of_nat] in NG. mlia. }
    apply rip_last.
  Qed.
End Proofs.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma region_is_poisoned_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  map_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (1 <= bv_unsigned a1 <= 2^32)%Z ->
  inmem_range (bv_unsigned a0) (bv_unsigned a1) ->
  shadow_ok m (bv_unsigned a0) (bv_unsigned a1) ->
  mem_inv rsegs m ->
  evt rsegs (region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a71c) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MC ST LOLE CEIL N1 IR SOK MI.
  destruct SOK as (ng & lastb & NG & SH & LB). open_map_cells MC.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a1 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite app_length, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 9 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879%Z
    by (vm_compute; reflexivity).
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. unfold inmem_range in IR. lia. }
    replace (bv_unsigned a1 + bv_unsigned a0)%Z with (bv_unsigned a0 + bv_unsigned a1)%Z by lia.
    subst sbs. eapply rip_core; eassumption.
  - (* [comment removed for export] *)
    do 7 zstep.
    replace ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z by (vm_compute; reflexivity).
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
    do 6 zstep. if_cases K3; zify_cond K3. { exfalso. unfold inmem_range in IR. lia. }
    zstep. if_cases K4; zify_cond K4.
    { exfalso. unfold inmem_range in IR. rewrite ?Z.shiftr_div_pow2 in K4 by lia. change (2^3)%Z with 8%Z in K4. lia. }
    zstep. zstep. if_cases K5; zify_cond K5. { exfalso. unfold inmem_range in IR. lia. }
    do 7 zstep.
    replace ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z by (vm_compute; reflexivity).
    zstep. if_cases K6; zify_cond K6. 2:{ exfalso. lia. }
    do 6 zstep. if_cases K7; zify_cond K7. { exfalso. unfold inmem_range in IR. lia. }
    zstep. if_cases K8; zify_cond K8.
    { exfalso. unfold inmem_range in IR. rewrite ?Z.shiftr_div_pow2 in K8 by lia. change (2^3)%Z with 8%Z in K8. lia. }
    replace (bv_unsigned a1 + bv_unsigned a0)%Z with (bv_unsigned a0 + bv_unsigned a1)%Z by lia.
    subst sbs. eapply rip_core; eassumption.
Qed.

End CEIL.
End AIcp6d9.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.

Module AIcpdmn.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcpm9j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Ltac icpt_unfold_segs :=
  unfold rsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments;
  cbn [find_segment];
  replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x25000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x35000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xa8000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xaa000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x560000%Z by (vm_compute; reflexivity).

Lemma icpt_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x60a000 <= z) ->
  find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. icpt_unfold_segs.
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x25000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x35000 z); destruct (Z.leb_spec0 (z + n) (0x35000 + 0x73000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa8000 z); destruct (Z.leb_spec0 (z + n) (0xa8000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + n) (0xaa000 + 0x560000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma icpt_seg_rom_none : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> seg_rom rsegs x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite icpt_find_segment_none by (cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_mapped8 : forall (m : word -> option byte) a (w : word),
  bytes_at rsegs m a (le8 w) -> 0x60a000 <= a -> mapped8 m a.
Proof.
  intros m a w HB Ha i Hi. pose proof (bytes_at_bound _ _ _ _ HB) as B. rewrite length_le8 in B.
  destruct HB as (_ & _ & RD). specialize (RD (Z.to_nat i) ltac:(rewrite length_le8; lia)).
  rewrite Z2Nat.id in RD by lia. unfold mrd, wa in RD.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [congruence|].
  rewrite icpt_seg_rom_none in RD.
  - destruct (nth_error (le8 w) (Z.to_nat i)) eqn:E2; [discriminate|].
    apply nth_error_None in E2. rewrite length_le8 in E2. lia.
  - rewrite unsigned_lit by lia. lia.
Qed.
End AIcpdmn.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition range_ok (m : word -> option byte) (a n : Z) : Prop :=
  inmem_range a n /\ shadow_ok m a n /\
  mapped8 m (sha a - sha a mod 8) /\ mapped8 m (sha (a + n - 1) - sha (a + n - 1) mod 8).

(* [comment removed for export] *)
Lemma qc_word_addr : forall x, (0 <= x < 2^47)%Z ->
  Z.land (2147450880 + Z.shiftr x 3) 18446744073709551608 = (sha x - sha x mod 8)%Z.
Proof.
  intros x Hx. unfold sha, shadow_off. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
  rewrite land_m8 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Lemma mapped_bytes_at : forall (m : word -> option byte) a n,
  (forall i, (0 <= i < Z.of_nat n)%Z -> m (Z_to_bv 64 (a + i)) <> None) -> (0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n HM Ha Hn. revert a Ha Hn HM. induction n as [|n IH]; intros a Ha Hn HM.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (m (Z_to_bv 64 (a + 0))) as [b|] eqn:E.
    2:{ exfalso. apply (HM 0%Z); [lia| exact E]. }
    destruct (IH (a + 1)%Z) as (bs & Hl & Hb); [lia|lia| |].
    { intros i Hi. replace (a + 1 + i)%Z with (a + (1 + i))%Z by lia. apply HM. lia. }
    exists (b :: bs). split; [cbn; lia|].
    destruct Hb as (Hb0 & Hb1 & Hb2).
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. unfold mrd, wa. replace (a + Z.of_nat 0)%Z with (a + 0)%Z by lia. rewrite E. reflexivity.
    + cbn [nth_error]. rewrite <- (Hb2 i) by (cbn [length] in Hi; lia). f_equal. unfold wa. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma mapped8_le8 : forall (m : word -> option byte) a,
  mapped8 m a -> (0 <= a)%Z -> (a + 8 <= 2^64)%Z -> exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a HM Ha Hn. destruct (mapped_bytes_at m a 8 HM Ha Hn) as (bs & HL & HB).
  destruct (bytes8_word bs HL) as [w ->]. exists w. exact HB.
Qed.

Lemma qc_read : forall (m : word -> option byte) x w,
  bytes_at rsegs m (sha x - sha x mod 8) (le8 w) -> (0 <= x < 2^47)%Z ->
  ov_read_bytes rsegs m (Z_to_bv 64 (Z.land (2147450880 + Z.shiftr x 3) 18446744073709551608)) 8 = Some (le8 w).
Proof.
  intros m x w HB HX. pose proof (length_le8 w) as HL. set (bs := le8 w) in *. rewrite qc_word_addr by lia.
  replace (Z_to_bv 64 (sha x - sha x mod 8)) with (wa (sha x - sha x mod 8 + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m _ bs 0 8 HB) by (rewrite ?HL; cbn; lia).
  rewrite <- HL. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma poisoned_last_zero : forall x lastb, (0 <= x)%Z -> (lastb = 0 \/ (x mod 8 < lastb <= 7))%Z ->
  Z.land (Z.b2z (0 <? lastb))
         (Z.lxor (Z.b2z (Z.lxor (Z.land x 7) 9223372036854775808 <? Z.lxor lastb 9223372036854775808)) 1) = 0%Z.
Proof.
  intros x lastb Hx [HL|HL].
  - subst lastb. reflexivity.
  - change 7%Z with (2^3 - 1)%Z. rewrite zb_land_mask by lia. change (2^3)%Z with 8%Z.
    change 9223372036854775808%Z with (2^63)%Z. rewrite !zb_lxor_pow2_small by mlia.
    replace (0 <? lastb) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (x mod 8 + 2^63 <? lastb + 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

