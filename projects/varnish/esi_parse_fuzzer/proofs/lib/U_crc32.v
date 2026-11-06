(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU V_CrcLib.

Module U_cromo.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU V_CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition CRC_FRAME_U := 112%Z.
Definition CRC_TABS : Z := 0x12998.
Definition CRC_TABS_LEN : Z := 5120.

Definition crc32_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - CRC_FRAME_U, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma crc_tabs_at : forall m, mem_inv rsegs m ->
  exists tabs, Z.of_nat (length tabs) = CRC_TABS_LEN /\ bytes_at rsegs m CRC_TABS tabs.
Proof.
  intros m MI.
  set (bs := match image_bytes rsegs CRC_TABS (Z.to_nat CRC_TABS_LEN) with Some bs => bs | None => [] end).
  assert (HL : Z.of_nat (length bs) = CRC_TABS_LEN) by (vm_compute; reflexivity).
  exists bs. split; [exact HL|].
  apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | unfold CRC_TABS; lia | rewrite HL; unfold CRC_TABS, CRC_TABS_LEN; lia].
Qed.

Section Tail.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (lo : Z) (junk : list byte).
  Variables (a1 : word) (inp tabs : list byte).
  (* [comment removed for export] *)
  Variables (g1 g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g29 g30 g31 : word).
  Hypothesis MU1 : munch [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -112).
  Hypothesis LO : (lo + 112 <= bv_unsigned sp)%Z.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -112)
    [CB 8 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INP1 : bytes_at rsegs m1 (bv_unsigned a1) inp.
  Hypothesis TABS1 : bytes_at rsegs m1 0x12998 tabs.   (* [comment removed for export] *)
  Hypothesis TL : Z.of_nat (length tabs) = CRC_TABS_LEN.
  Hypothesis LL : (bv_unsigned a1 + Z.of_nat (length inp) < 2^64)%Z.   (* [comment removed for export] *)

  Notation B := (bv_unsigned a1).
  Notation L := (Z.of_nat (length inp)).
  Notation POST := (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Notation AT pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 g8 g9 x10 x11 x12 x13 x14 x15 x16 x17
            g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 g29 g30 g31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  #[using="INP1 m1"] Lemma B_bound : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INP1). Qed.

  (* [comment removed for export] *)
  #[using="FR1 LO ST1 MI1 WM1 MU1 tabs inp junk"] Lemma epi_loads : forall x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28,
    evt rsegs POST (AT 0x1ca14 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28).
  Proof.
    intros. unfold crc32_post, CRC_FRAME_U.
    pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. pose proof MI1 as MI.
    pose proof (bv_unsigned_in_range _ sp) as Rsp.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    do 14 zstep.
    release_frame FR STK (bv_unsigned sp).
    zstep. finish.
  Qed.

  (* [comment removed for export] *)
  #[using="FR1 LO ST1 MI1 WM1 MU1 tabs inp junk"] Lemma epilogue : forall x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28,
    evt rsegs POST (AT 0x1ca08 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28).
  Proof. intros. pose proof MI1 as MI. do 3 zstep. apply epi_loads. Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma tail5 : forall (k : nat) (i : Z) x5 x6 x7 x13 x15 x16 x17 x28,
    (k = Z.to_nat (L - i))%nat -> (0 <= i < L)%Z ->
    evt rsegs POST (AT 0x1c9d8 x5 x6 x7 (Z_to_bv 64 0x12998) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (B + L)) x13 (Z_to_bv 64 (-1)) x15 x16 x17 x28).
  Proof.
    induction k as [|k IH]; intros i x5 x6 x7 x13 x15 x16 x17 x28 Hk Hi; [lia|].
    pose proof B_bound as BB. pose proof MI1 as MI. pose proof TL as TL'. unfold CRC_TABS_LEN in TL'.
    zstep. notrap.
    do 11 cstep.
    if_cases K; zify_cond K.
    - replace (B + i + 1)%Z with (B + (i + 1))%Z by lia. apply (IH (i + 1)%Z); lia.
    - apply epilogue.
  Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma tail_entry : forall (i : Z) x5 x6 x7 x13 x14 x15 x16 x17 x28,
    (0 <= i <= L)%Z ->
    evt rsegs POST (AT 0x1c9b8 x5 x6 x7 (Z_to_bv 64 0x12998) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (L - i)) x13 x14 x15 x16 x17 x28).
  Proof.
    intros i x5 x6 x7 x13 x14 x15 x16 x17 x28 Hi.
    pose proof B_bound as BB. pose proof MI1 as MI.
    zstep. if_cases K; zify_cond K.
    - apply epilogue.
    - do 3 zstep. if_cases K2; zify_cond K2.
      { exfalso. rewrite zb_lxor_ones in K2 by lia. lia. }
      do 4 zstep.
      replace (L - i + -1 + (B + i) + 1)%Z with (B + L)%Z by lia.
      apply (tail5 (Z.to_nat (L - i)) i); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma loop8 : forall (k : nat) (i : Z) x5 x6 x7 x13 x17 x28,
    (k = Z.to_nat (L - i))%nat -> (0 <= i)%Z -> (i + 8 <= L)%Z ->
    evt rsegs POST (AT 0x1c86c x5 x6 x7 (Z_to_bv 64 0x12998) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (L - i)) x13
                       (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)) (Z_to_bv 64 7) x17 x28).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x6 x7 x13 x17 x28 Hk Hi HiL.
    pose proof B_bound as BB. pose proof MI1 as MI. pose proof TL as TL'. unfold CRC_TABS_LEN in TL'.
    zstep. notrap. zstep.
    do 5 (zstep; zstep; notrap).
    zstep. notrap. zstep. zstep. notrap.
    do 67 cstep.
    if_cases K; zify_cond K.
    - replace (B + i + 8)%Z with (B + (i + 8))%Z by lia.
      replace (L - i + -8)%Z with (L - (i + 8))%Z by lia.
      apply (IH (Z.to_nat (L - (i + 8)))); lia.
    - zstep.
      replace (B + i + 8)%Z with (B + (i + 8))%Z by lia. replace (L - i + -8)%Z with (L - (i + 8))%Z by lia.
      apply tail_entry. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma sec_tail : forall (i : Z) x5 x6 x7 x13 x14 x15 x16 x17 x28,
    (0 <= i <= L)%Z ->
    evt rsegs POST (AT 0x1c858 x5 x6 x7 (Z_to_bv 64 0x12998) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (L - i)) x13 x14 x15 x16 x17 x28).
  Proof.
    intros i x5 x6 x7 x13 x14 x15 x16 x17 x28 Hi.
    pose proof B_bound as BB. pose proof MI1 as MI.
    do 2 zstep. if_cases K; zify_cond K.
    - apply tail_entry. lia.
    - do 3 zstep. apply (loop8 (Z.to_nat (L - i)) i); lia.
  Qed.
End Tail.
End U_cromo.


Module U_cr51t.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ImgU V_CrcLib.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)

Lemma land3_mod : forall x, Z.land x 3 = (x mod 4)%Z.
Proof. intros x. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Section Braid.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (lo : Z) (bw : word).
  Variables (a1 : word) (inp tabs : list byte).
  Hypothesis MU1 : munch [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -112).
  Hypothesis LO : (lo + 112 <= bv_unsigned sp)%Z.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -112)
    [C8 bw; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INP1 : bytes_at rsegs m1 (bv_unsigned a1) inp.
  Hypothesis TABS1 : bytes_at rsegs m1 0x12998 tabs.
  Hypothesis TL : Z.of_nat (length tabs) = CRC_TABS_LEN.
  Hypothesis LL : (bv_unsigned a1 + Z.of_nat (length inp) < 2^64)%Z.

  Notation B := (bv_unsigned a1).
  Notation L := (Z.of_nat (length inp)).
  Notation POST := (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Notation ATB pc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0x12998) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  #[using="INP1 m1"] Lemma B_bound' : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INP1). Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs"] Lemma last_block : forall (q : Z) x1 x5 x6 x7 x8 x9 (x12 : word) x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (0 <= q)%Z -> (q + 20 <= L)%Z -> ((B + q) mod 4 = 0)%Z ->
    ((bv_unsigned bw * 18446744073709551596 + bv_unsigned x12) mod 2^64 = L - (q + 20))%Z ->
    evt rsegs POST (ATB 0x1c720 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (B + q)) x12 x13 x14 x15 (Z_to_bv 64 (B + q)) x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hq HqL Hal H72.
    pose proof B_bound' as BB. pose proof MI1 as MI. pose proof TL as TL'. unfold CRC_TABS_LEN in TL'.
    pose proof (bv_unsigned_in_range _ bw) as Rbw. pose proof (bv_unsigned_in_range _ x12) as R12.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KA; zify_cond KA. { exfalso. rewrite land3_mod in KA. lia. }
    do 5 cstep.
    replace (Z_to_bv 64 (bv_unsigned bw * 18446744073709551596 + bv_unsigned x12)) with (Z_to_bv 64 (L - (q + 20)))
      by (apply Z_to_bv_eqm; rewrite H72; rewrite Z.mod_small; lia).
    do 2 cstep.
    do 4 (do 8 cstep; lit_branch). gen_lxor.
    zstep. zstep. notrap. do 4 cstep. do 4 (do 8 cstep; lit_branch). gen_lxor.
    zstep. zstep. notrap. do 4 cstep. do 4 (do 8 cstep; lit_branch). gen_lxor.
    zstep. zstep. notrap. do 4 cstep. do 4 (do 8 cstep; lit_branch). gen_lxor.
    zstep. zstep. notrap. do 4 cstep. do 4 (do 8 cstep; lit_branch). gen_lxor.
    zstep. zstep. notrap. do 3 cstep.
    replace (B + q + 20)%Z with (B + (q + 20))%Z by lia.
    pose proof (rw_cells_C8_CB rsegs m1 _ bw _ FR1) as FRB.
    eapply sec_tail; try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs"] Lemma braid_outer : forall (n : nat) (j i0 blks : Z)
      x1 x6 x8 x9 x13 x14 x15 x17 x19 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    (1 <= n)%nat -> (0 <= j)%Z -> (j + Z.of_nat n = blks - 1)%Z -> (0 <= i0)%Z -> (i0 + 20 * blks <= L)%Z ->
    ((B + i0) mod 4 = 0)%Z -> bv_unsigned bw = blks ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 18446744073709473383) x6 (Z_to_bv 64 (Z.of_nat n)) x8 x9
              (Z_to_bv 64 0x12998) (Z_to_bv 64 (B + i0 + 20 * j)) (Z_to_bv 64 (L - i0)) x13 x14 x15 (Z_to_bv 64 (B + (i0 + 20 * (blks - 1)))) x17
              (Z_to_bv 64 0x12d98) x19 (Z_to_bv 64 0x13198) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 0) x29 x30 x31)
          F (Z_to_bv 64 0x1c5a8) fc None m1 (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros j i0 blks x1 x6 x8 x9 x13 x14 x15 x17 x19 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 Hn Hj Hjn Hi0 HL Hal Hbw; [lia|].
    pose proof B_bound' as BB. pose proof MI1 as MI. pose proof TL as TL'. unfold CRC_TABS_LEN in TL'.
    (* [comment removed for export] *)
    zstep. lit_branch.
    do 5 (zstep; zstep; notrap).
    (* [comment removed for export] *)
    do 35 cstep.
    (* [comment removed for export] *)
    do 3 (do 5 (do 3 cstep; zstep; notrap); do 19 cstep; zstep; lit_branch).
    gen_lxor.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    - replace (Z.of_nat (S n) + -1)%Z with (Z.of_nat n) by lia.
      replace (B + i0 + 20 * j + 20)%Z with (B + i0 + 20 * (j + 1))%Z by lia.
      apply IH; try lia; try exact Hbw.
    - (* [comment removed for export] *)
      zstep. zstep.
      apply last_block; try lia.
      (* [comment removed for export] *)
      rewrite Hbw, unsigned_lit_wrap, Zplus_mod_idemp_r.
        replace (blks * 18446744073709551596 + (L - i0))%Z with ((L - (i0 + 20 * (blks - 1) + 20)) + blks * 2^64)%Z by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
End Braid.
End U_cr51t.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cr51t.

Module U_cr6ux.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU V_CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition x2nmodp_entry := 0x1cae4%Z.
Definition crc32_combine64_entry := 0x1ca60%Z.
Definition crc32_combine_entry := 0x1cb84%Z.

(* [comment removed for export] *)
Lemma x2n_tab_at : forall m, mem_inv rsegs m -> bytes_at rsegs m X2N_TAB x2n_bytes.
Proof. intros m MI. apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | unfold X2N_TAB; lia | rewrite x2n_bytes_length; unfold X2N_TAB; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition x2nmodp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (p : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SX p)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m
    /\ (0 < p < 2^32)%Z.

Section X2N.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv rsegs m.

  (* [comment removed for export] *)
  Notation AT pc x5 x6 x10 x11 x12 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 0x13d98) (Z_to_bv 64 18446744073709470311) (Z_to_bv 64 18446744073402876704) x16 x17
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Section AnyPost.
  Variable Q : machine_state -> Prop.

  (* [comment removed for export] *)
  Lemma x2n_shift : forall (k : nat) (a b p : Z) x6 x10 x12,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (1 <= k <= 31)%nat ->
    (forall x6', evt rsegs Q (AT 0x1cb40 (Z_to_bv 64 (SX (2 ^ Z.of_nat (k - 1)))) x6' x10 (Z_to_bv 64 (SX p)) x12 (Z_to_bv 64 (SX (cstep b))) (Z_to_bv 64 (SX a)))) ->
    evt rsegs Q (AT 0x1cb58 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) x12 (Z_to_bv 64 (SX b)) (Z_to_bv 64 (SX a))).
  Proof.
    intros k a b p x6 x10 x12 Ha Hb Hp Hk H.
    pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
    assert (Hm : (0 < 2 ^ Z.of_nat k <= 2^31)%Z). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. }
    pose proof (SX_range (2 ^ Z.of_nat k) ltac:(lia)) as Rm.
    pose proof (cstep_range b Hb) as Rc. pose proof (SX_range _ Rc) as Rc'.
    do 7 zstep.
    rewrite (srliw1_SX b Hb). rewrite (srliw1_SX (2 ^ Z.of_nat k)) by lia.
    rewrite (signmask_SX b Hb). rewrite (shr1_mod64 b Hb). rewrite (bstep_SX b Hb).
    rewrite (pow2k_half k) by lia.
    rewrite <- (SX_small (2 ^ Z.of_nat (k - 1))) by (pose proof (pow2k_range (k-1)%nat ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
    apply H.
  Qed.

  Lemma x2n_inner : forall (k : nat) (a b p : Z) x6 x10 x12,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (k <= 31)%nat ->
    lowbits_nz a (Z.of_nat k) ->
    (forall x5' x6' x16',
       evt rsegs Q (AT 0x1cb10 x5' x6' x10 (Z_to_bv 64 (SX (mm_loop (S k) (2 ^ Z.of_nat k) a b p))) x12 x16' (Z_to_bv 64 (SX a)))) ->
    evt rsegs Q (AT 0x1cb40 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x6 x10 (Z_to_bv 64 (SX p)) x12 (Z_to_bv 64 (SX b)) (Z_to_bv 64 (SX a))).
  Proof.
    induction k as [|k IH]; intros a b p x6 x10 x12 Ha Hb Hp Hk LB CONT.
    - (* [comment removed for export] *)
      destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
      pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite land_small_SX in K by lia. change 1%Z with (2^0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
      do 4 zstep.
      change (bv_swrap 32 (1 + -1)) with 0%Z. rewrite Z.land_0_l.
      if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
      rewrite (lxor_SX p b) by lia.
      rewrite land_small_SX in K by lia.
      rewrite mm_loop_exit in CONT by (first [exact K | exact L0]).
      apply CONT.
    - pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      pose proof (pow2k_range (S k) Hk) as Hm. pose proof (SX_range (2 ^ Z.of_nat (S k)) ltac:(lia)) as Rm.
      pose proof (lxor_bound 32 p b ltac:(lia) Hp Hb) as Rx. pose proof (SX_range _ Rx) as Rx'.
      zstep. zstep. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        rewrite land_SX in K by lia. apply (proj1 (SX_nz _ (land_bound_l 32 (2 ^ Z.of_nat (S k)) a ltac:(lia) ltac:(lia)))) in K.
        pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
        apply x2n_shift; try lia. intros x6'.
        rewrite mm_loop_skip in CONT by exact K. rewrite pow2k_half in CONT by lia.
        replace (S k - 1)%nat with k in * by lia.
        apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
        replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (left; exact Tk).
      + (* [comment removed for export] *)
        do 4 zstep.
        rewrite (addiw_m1_SX (2 ^ Z.of_nat (S k))) by lia.
        rewrite (Z.mod_small (2 ^ Z.of_nat (S k) - 1) 18446744073709551616) by lia.
        rewrite (land_small_SX (2 ^ Z.of_nat (S k) - 1) a) by lia.
        rewrite (lxor_SX p b) by lia.
        rewrite land_SX in K by lia.
        assert (K' : Z.land (2 ^ Z.of_nat (S k)) a <> 0%Z). { intros E. apply K. rewrite E. reflexivity. }
        if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          rewrite mm_loop_exit in CONT by (first [exact K' | exact K2]). apply CONT.
        * apply x2n_shift; try lia. intros x6'.
          rewrite mm_loop_cont in CONT by (first [exact K' | exact K2]). rewrite pow2k_half in CONT by lia.
          replace (S k - 1)%nat with k in * by lia.
          apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
          replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (right; exact K2).
  Qed.

  End AnyPost.

  Notation POST := (x2nmodp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono rsegs m m := wmono_refl rsegs m.

  (* [comment removed for export] *)
  #[using="WM MU MI"] Lemma x2n_outer : forall (N : nat) (n k p : Z) x5 x6 x11 x17,
    (Z.to_nat n < N)%nat -> (0 < n < 2^63)%Z -> (0 <= k)%Z -> (k + Z.of_nat N <= 2^63 + 8)%Z -> (0 < p < 2^32)%Z ->
    evt rsegs POST (AT 0x1cb04 x5 x6 (Z_to_bv 64 n) x11 (Z_to_bv 64 k) (Z_to_bv 64 (SX p)) x17).
  Proof.
    induction N as [N IH] using lt_wf_ind; intros n k p x5 x6 x11 x17 HN Hn Hk HkN Hp.
    pose proof (SX_range p ltac:(lia)) as Rp.
    (* [comment removed for export] *)
    assert (CONT : forall (p' : Z) x5' x6' x16' x17', (0 < p' < 2^32)%Z ->
      evt rsegs POST (AT 0x1cb10 x5' x6' (Z_to_bv 64 n) (Z_to_bv 64 (SX p')) (Z_to_bv 64 k) x16' x17')).
    { intros p' x5' x6' x16' x17' Hp'. pose proof (SX_range p' ltac:(lia)) as Rp'.
      zstep. rewrite (signed_small n) by lia.
      assert (Hs : (0 <= Z.shiftr n 1 < n)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1)%Z with 2%Z; Z.div_mod_to_equations; lia).
      try rewrite (Z.mod_small (Z.shiftr n 1) 18446744073709551616) by lia.
      do 3 zstep.
      if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply (IH (S (Z.to_nat (Z.shiftr n 1)))); lia.
      - do 3 zstep. finish; lia. }
    zstep. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      pose proof (rd_x2n rsegs m k _ (x2n_tab_at m MI) eq_refl) as RD. cbv delta [X2N_TAB] in RD.
      pose proof (land31_range k) as Hi.
      set (i := Z.to_nat (Z.land k 31)) in RD.
      assert (Hi32 : (i < 32)%nat) by lia.
      pose proof (tabz_range i Hi32) as Ht.
      zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. crc_arith_prep. lia. }
      do 3 zstep.
      rewrite (sx32_SX (Z_to_bv 64 (tabz i)) (tabz i) (tabz_word i Hi32) ltac:(lia)).
      zstep.
      replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2 ^ Z.of_nat 31))) by (apply bv_eq; reflexivity).
      change (Z_to_bv 64 0) with (Z_to_bv 64 (SX 0)).
      (* [comment removed for export] *)
      apply (x2n_inner _ 31 (tabz i) p 0); [lia|lia|lia|lia| apply lowbits_nz_init; lia |].
      intros x5' x6' x16'. apply CONT.
      exact (mm_tab_pos i p Hi32 ltac:(lia)).
    - (* [comment removed for export] *)
      zstep. apply CONT. lia.
  Qed.
End X2N.

Lemma x2nmodp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  (bv_unsigned a0 < 2^63)%Z ->
  evt rsegs (x2nmodp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cae4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI Hn.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ a0) as Ra0.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep. replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity). finish; lia.
  - do 7 zstep.
    rewrite <- (Z_to_bv_bv_unsigned a0).
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
    apply (x2n_outer ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI
             (S (Z.to_nat (bv_unsigned a0))) (bv_unsigned a0) 3 (2^31)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition C64_FRAME := 32%Z.

Definition crc32_combine64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - C64_FRAME, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Section C64Loop.
  Variables (sp gp tp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (a : Z).
  Variable Q : machine_state -> Prop.
  Hypothesis Ha : (0 < a < 2^32)%Z.

  Notation AT2 pc x9 x11 x12 x14 x15 :=
    (MS (mkR (Z_to_bv 64 0x1ca80) sp gp tp t0 t1 t2 s0 x9 (Z_to_bv 64 (SX a)) x11 x12 (Z_to_bv 64 (-306674912)) x14 x15 a6 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  #[using="Ha"] Lemma c64_loop : forall (k : nat) (x9 x11 x14 x15 : word),
    (k <= 31)%nat -> lowbits_nz a (Z.of_nat k) ->
    (forall x9' x11' x12' x14' x15', evt rsegs Q (AT2 0x1cac4 x9' x11' x12' x14' x15')) ->
    evt rsegs Q (AT2 0x1ca90 x9 x11 (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x14 x15).
  Proof.
    induction k as [|k IH]; intros x9 x11 x14 x15 Hk LB CONT.
    - destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
      pose proof (SX_range a ltac:(lia)) as Ra.
      change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite land_small_SX in K by lia. change 1%Z with (2^0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
      do 4 zstep.
      change (bv_swrap 32 (1 + -1)) with 0%Z. rewrite Z.land_0_l.
      if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
      apply CONT.
    - pose proof (SX_range a ltac:(lia)) as Ra.
      pose proof (pow2k_range (S k) Hk) as Hm. pose proof (SX_range (2 ^ Z.of_nat (S k)) ltac:(lia)) as Rm.
      assert (SHIFT : forall x9' x11' x14' x15',
        lowbits_nz a (Z.of_nat k) ->
        evt rsegs Q (AT2 0x1caa8 x9' x11' (Z_to_bv 64 (SX (2 ^ Z.of_nat (S k)))) x14' x15')).
      { intros x9' x11' x14' x15' LB'. do 7 zstep.
        rewrite (srliw1_SX (2 ^ Z.of_nat (S k))) by lia. rewrite pow2k_half by lia.
        replace (S k - 1)%nat with k by lia.
        rewrite <- (SX_small (2 ^ Z.of_nat k)) by (pose proof (pow2k_range k ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
        apply IH; [lia | exact LB' | exact CONT]. }
      zstep. zstep. if_cases K; zify_cond K.
      + rewrite land_SX in K by lia. apply (proj1 (SX_nz _ (land_bound_l 32 (2 ^ Z.of_nat (S k)) a ltac:(lia) ltac:(lia)))) in K.
        pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
        apply SHIFT. replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (left; exact Tk).
      + do 4 zstep.
        rewrite (addiw_m1_SX (2 ^ Z.of_nat (S k))) by lia.
        rewrite (Z.mod_small (2 ^ Z.of_nat (S k) - 1) 18446744073709551616) by lia.
        rewrite (land_small_SX (2 ^ Z.of_nat (S k) - 1) a) by lia.
        if_cases K2; zify_cond K2.
        * apply CONT.
        * apply SHIFT. replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (right; exact K2).
  Qed.
End C64Loop.

Section C64.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo + 32 <= bv_unsigned sp)%Z.
  Hypothesis LEN : (bv_unsigned a2 < 2^63)%Z.

  #[using="LEN LO ST MI"] Lemma crc32_combine64_body :
    evt rsegs (crc32_combine64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ca60) fc None m (seg_rom rsegs)).
  Proof.
    unfold crc32_combine64_post, C64_FRAME.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ sp) as Rsp.
    carve_frame 32%nat ST.
    do 8 zstep.
    call x2nmodp_spec. all: try assumption.
    lazymatch goal with PC : (0 < ?p)%Z |- _ => rename p into pa end.
    pose proof (SX_range pa ltac:(lia)) as Rpa.
    do 4 zstep.
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2 ^ Z.of_nat 31))) by (apply bv_eq; reflexivity).
    eapply c64_loop; [lia | lia | apply lowbits_nz_init; lia |].
    intros x9' x11' x12' x14' x15'.
    do 7 zstep.
    lazymatch goal with FR : rw_cells _ _ _ _, STK : stk _ _ _ _ |- _ =>
      release_frame FR STK (bv_unsigned sp) end.
    zstep. finish.
  Qed.
End C64.

Lemma crc32_combine64_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  (bv_unsigned a2 < 2^63)%Z ->
  evt rsegs (crc32_combine64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ca60) fc None m (seg_rom rsegs)).
Proof. intros. eapply crc32_combine64_body; eassumption. Qed.

(* [comment removed for export] *)
Lemma crc32_combine_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  (bv_unsigned a2 < 2^63)%Z ->
  evt rsegs (crc32_combine64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cb84) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MI ST LO LEN.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. apply crc32_combine64_spec; assumption.
Qed.
End U_cr6ux.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition crc32_z_entry := 0x1c48c%Z.
Definition crc32_entry := 0x1ca54%Z.

Section Entry.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (lo : Z) (junk : list byte).
  Variables (a1 : word) (inp tabs : list byte).
  Hypothesis MU1 : munch [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -112).
  Hypothesis LO : (lo + 112 <= bv_unsigned sp)%Z.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -112)
    [CB 8 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INP1 : bytes_at rsegs m1 (bv_unsigned a1) inp.
  Hypothesis TABS1 : bytes_at rsegs m1 0x12998 tabs.
  Hypothesis TL : Z.of_nat (length tabs) = CRC_TABS_LEN.
  Hypothesis LL : (bv_unsigned a1 + Z.of_nat (length inp) < 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis SEP : (bv_unsigned a1 + Z.of_nat (length inp) <= bv_unsigned sp + -112 \/ bv_unsigned sp <= bv_unsigned a1)%Z.

  Notation B := (bv_unsigned a1).
  Notation L := (Z.of_nat (length inp)).
  Notation POST := (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Notation ATE pc x5 x6 x11 x12 x13 x14 x15 x16 x17 x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0x12998) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  #[using="INP1 m1"] Lemma B_bound'' : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INP1). Qed.

  (* [comment removed for export] *)
  #[using="SEP LL INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma setup : forall (i0 : Z) x5 x6 x13 x14 x15 x17 x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (0 <= i0 <= 3)%Z -> (23 <= L)%Z -> ((B + i0) mod 4 = 0)%Z ->
    evt rsegs POST (ATE 0x1c554 x5 x6 (Z_to_bv 64 (B + i0)) (Z_to_bv 64 (L - i0)) x13 x14 x15 (Z_to_bv 64 (B + i0)) x17
                        x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hi0 HL Hal.
    pose proof B_bound'' as BB. pose proof MI1 as MI. pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK.
    pose proof (bv_unsigned_in_range _ sp) as Rsp.
    do 4 zstep.
    rewrite (div20_form (L - i0)) by lia.
    set (blks := ((L - i0) / 20)%Z).
    assert (Hb : (1 <= blks /\ 20 * blks <= L - i0)%Z) by (subst blks; Z.div_mod_to_equations; lia).
    clearbody blks.
    zstep.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (crc_tabs_at mx ltac:(assumption)) as (tabs2 & TL2 & TABS2); cbv delta [CRC_TABS] in TABS2 end.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 4 zstep.
      eapply last_block; try eassumption; try lia.
      rewrite !unsigned_lit by lia.
      replace (blks * 18446744073709551596 + (L - i0))%Z with ((L - (i0 + 20)) + blks * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - do 14 zstep.
      replace (Z.land (B + i0) 3) with 0%Z by (rewrite land3_mod; symmetry; exact Hal).
      replace (B + i0 + blks * 20 + -20)%Z with (B + (i0 + 20 * (blks - 1)))%Z by lia.
      replace (Z_to_bv 64 (blks + -1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (blks - 1)))) by (f_equal; lia).
      replace (Z_to_bv 64 (B + i0)) with (Z_to_bv 64 (B + i0 + 20 * 0)) by (f_equal; lia).
      eapply braid_outer; try eassumption; try lia.
      rewrite unsigned_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SEP LL TL TABS1 INP1 FR1 LO ST1 MI1 WM1 MU1 tabs junk"] Lemma align_loop : forall (k : nat) (i : Z) x6 x11 x12 x13 x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (4 - (B + i) mod 4 <= Z.of_nat k)%Z -> ((B + i) mod 4 <> 0)%Z -> (0 <= i)%Z -> (i + (4 - (B + i) mod 4) <= 3)%Z -> (23 <= L)%Z ->
    evt rsegs POST (ATE 0x1c500 (Z_to_bv 64 (B + i)) x6 x11 x12 x13 (Z_to_bv 64 (-1)) (Z_to_bv 64 1) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (L - i))
                        x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros Hk Hal Hi Hi3 HL.
    { exfalso. pose proof (Z.mod_pos_bound (B + i) 4 ltac:(lia)). lia. }
    pose proof B_bound'' as BB. pose proof MI1 as MI. pose proof TL as TL'. unfold CRC_TABS_LEN in TL'.
    pose proof (Z.mod_pos_bound (B + i) 4 ltac:(lia)) as Hm4.
    zstep. notrap.
    do 11 cstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    do 4 zstep. if_cases K2; zify_cond K2.
    - rewrite land3_mod in K2.
      replace (B + i + 1)%Z with (B + (i + 1))%Z in * by lia.
      replace (L - i + -1)%Z with (L - (i + 1))%Z by lia.
      apply IH; try lia; revert K2 Hk Hal Hi3; Z.div_mod_to_equations; intros; lia.
    - zstep. rewrite land3_mod in K2.
      replace (B + i + 1)%Z with (B + (i + 1))%Z in * by lia.
      replace (L - i + -1)%Z with (L - (i + 1))%Z by lia.
      apply setup; try lia; revert K2 Hal Hi3; Z.div_mod_to_equations; intros; lia.
  Qed.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (inp : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo + 112 <= bv_unsigned sp)%Z.
  Hypothesis INP : bytes_at rsegs m (bv_unsigned a1) inp.
  Hypothesis SEP : (bv_unsigned a1 + Z.of_nat (length inp) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis LL : (bv_unsigned a1 + Z.of_nat (length inp) < 2^64)%Z.

  #[using="LL SEP INP LO ST MI"] Lemma crc32_z_body_gen : forall a2 : word,
    bv_unsigned a2 = Z.of_nat (length inp) ->
    evt rsegs (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c48c) fc None m (seg_rom rsegs)).
  Proof.
    intros a2 LEN. unfold crc32_post, CRC_FRAME_U.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ sp) as Rsp. pose proof (bv_unsigned_in_range _ a1) as Ra1. pose proof (bv_unsigned_in_range _ a2) as Ra2.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z in SEP by lia.
    carve_frame 112%nat ST.
    do 14 zstep.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. eapply epi_loads; try eassumption; lia.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (crc_tabs_at mx ltac:(assumption)) as (tabs & TL & TABS); cbv delta [CRC_TABS] in TABS end.
      do 7 zstep.
      if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        replace a1 with (Z_to_bv 64 (bv_unsigned a1 + 0)) by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
        replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
        eapply sec_tail; try eassumption; lia.
      + zstep. zstep. if_cases K2; zify_cond K2.
        * zstep.
          replace a1 with (Z_to_bv 64 (bv_unsigned a1 + 0)) by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
          replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
          rewrite land3_mod in K2.
          eapply setup; try eassumption; try lia; rewrite ?Z.add_0_r; exact K2.
        * do 5 zstep.
          replace a1 with (Z_to_bv 64 (bv_unsigned a1 + 0)) by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
          replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
          rewrite land3_mod in K2.
          eapply align_loop with (k := 4%nat).
          all: try eassumption.
          all: rewrite ?Z.add_0_r, ?Z.add_0_l; pose proof (Z.mod_pos_bound (bv_unsigned a1) 4 ltac:(lia)); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LL SEP INP LO ST MI"] Lemma crc32_body_gen : forall a2 : word,
    (bv_unsigned a2 mod 2^32 = Z.of_nat (length inp))%Z ->
    evt rsegs (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ca54) fc None m (seg_rom rsegs)).
  Proof.
    intros a2 LEN.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ a2) as Ra2.
    do 3 zstep.
    pose proof (crc32_z_body_gen (Z_to_bv 64 (bv_unsigned a2 mod 4294967296))) as H.
    apply H. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). exact LEN.
  Qed.
End Spec.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem crc32_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (inp : list byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 112 <= bv_unsigned sp)%Z ->
  bytes_at rsegs m (bv_unsigned a1) inp ->
  (bv_unsigned a1 + Z.of_nat (length inp) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + Z.of_nat (length inp) < 2^64)%Z ->
  (bv_unsigned a2 mod 2^32 = Z.of_nat (length inp))%Z ->
  evt rsegs (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ca54) fc None m (seg_rom rsegs)).
Proof. intros. eapply crc32_body_gen; eassumption. Qed.

(* [comment removed for export] *)
Theorem crc32_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 112 <= bv_unsigned sp)%Z ->
  bv_unsigned a1 = 0%Z ->
  evt rsegs (crc32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ca54) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MI ST LO A1. unfold crc32_post, CRC_FRAME_U.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as Rsp. pose proof (bv_unsigned_in_range _ a2) as Ra2.
  do 3 zstep.
  carve_frame 112%nat ST.
  do 14 zstep.
  zstep. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. exact A1. }
  zstep. zstep. eapply epi_loads; try eassumption; lia.
Qed.
